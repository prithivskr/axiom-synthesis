open Printf
open Z3
open Axiomatization.Parser
open Axiomatization.Term
open Axiomatization.Verify
open Axiomatization.Verify_index
open Axiomatization.Prelude

let hlo_comparator_text =
  {|
  %region_0.2 (Arg_0.3: f32[], Arg_1.4: s32[], Arg_2.5: f32[], Arg_3.6: s32[]) -> (f32[], s32[]) {
    %Arg_0.3 = f32[] parameter(0)
    %Arg_2.5 = f32[] parameter(2)

    %Arg_1.4 = s32[] parameter(1)
    %Arg_3.6 = s32[] parameter(3)

    %multiply.6 = f32[] multiply(%Arg_0.3, %Arg_2.5)
    ROOT %tuple.16 = (f32[], s32[]) tuple(%multiply.6, %Arg_3.6)
  }
|}

let hlo_eval = compile_hlo hlo_comparator_text

let get_val = function
  | VInt i ->
      i
  | VBool b ->
      if b then 1 else 0
  | _ ->
      failwith "Expected int/bool in get_val"

let hlo_op a b =
  let res = hlo_eval [|VInt a; VInt 0; VInt b; VInt 1|] in
  get_val res.(0)

let hlo_z3_op ctx a b _ _ =
  let root =
    translate_comparator ctx
      [ a
      ; Arithmetic.Integer.mk_numeral_i ctx 0
      ; b
      ; Arithmetic.Integer.mk_numeral_i ctx 1 ]
      hlo_comparator_text
  in
  List.nth root 0

let () =
  Random.self_init () ;
  let n_candidates = 5 in
  let batch_size = 50 in
  let params = {var_pool= ["u"]; axes_pool= ["X"]; tensor_pool= ["A"; "B"]} in
  let op = hlo_op in
  let z3_op = hlo_z3_op in
  let found_tbl : (string, int term * int term * string) Hashtbl.t =
    Hashtbl.create (n_candidates * 2)
  in
  let trivial_tbl : (string, string * string) Hashtbl.t =
    Hashtbl.create (n_candidates * 2)
  in
  let iteration = ref 0 in
  while Hashtbl.length found_tbl < n_candidates do
    incr iteration ;
    let terms = generate_terms op params 3 batch_size in
    let candidates =
      find_empirical_equal_pairs ~terms ~params ~tests:10 ~max_tries_per_test:20
    in
    List.iter
      (fun (a, b) ->
        let a_c, b_c = strip_common_structure (a, b) in
        let a_prime, b_prime = generalize_relation params a_c b_c in
        let key = pair_key a_prime b_prime in
        if
          (not (Hashtbl.mem found_tbl key)) && not (Hashtbl.mem trivial_tbl key)
        then (
          printf "Candidate: %s == %s\n" (term_to_s a) (term_to_s b) ;
          printf "Stripped: %s == %s\n" (term_to_s a_prime) (term_to_s b_prime) ;
          let reduction_to_tensor_map = Hashtbl.create 10 in
          let no_reduce_a =
            transform_to_no_reductions reduction_to_tensor_map a_prime
          in
          let no_reduce_b =
            transform_to_no_reductions reduction_to_tensor_map b_prime
          in
          let new_tensor_names =
            Hashtbl.fold (fun _ v acc -> v :: acc) reduction_to_tensor_map []
          in
          let trivial_params =
            {params with tensor_pool= params.tensor_pool @ new_tensor_names}
          in
          printf "  Checking triviality...\n" ;
          printf "    A' = %s\n" (term_to_s no_reduce_a) ;
          printf "    B' = %s\n" (term_to_s no_reduce_b) ;
          let is_trivial =
            check_equality no_reduce_a no_reduce_b trivial_params ~tests:10
              ~max_tries_per_test:20
          in
          if is_trivial then (
            printf "  -> REJECTED (Trivial)\n\n%!" ;
            Hashtbl.add trivial_tbl key (term_to_s a_prime, term_to_s b_prime) )
          else (
            printf "  -> ACCEPTED (Non-Trivial)\n\n%!" ;
            let latex_rep =
              eq_to_latex_math ~reduction_symbol:"\\operatorname{Red}^+" a_prime
                b_prime
            in
            let lhs, rhs =
              match a_prime with
              | Reduction (_, _, _) ->
                  (a_prime, b_prime)
              | _ ->
                  (b_prime, a_prime)
            in
            Hashtbl.add found_tbl key (lhs, rhs, latex_rep) ) ) )
      candidates
  done ;
  printf "Finished: found %d unique candidate equalities (target was %d).\n"
    (Hashtbl.length found_tbl) n_candidates ;
  let candidates_sorted =
    Hashtbl.fold (fun _ (a, b, _) acc -> (a, b) :: acc) found_tbl []
    |> List.sort (fun (a0, b0) (a1, b1) ->
        compare
          (min (term_depth a0) (term_depth b0))
          (min (term_depth a1) (term_depth b1)) )
  in
  let proven_axioms = ref [] in
  let deferred_nested = ref [] in
  List.iter
    (fun (a, b) ->
      try
        begin
          print_endline "\n========================================" ;
          print_endline (term_to_s a) ;
          print_endline (term_to_s b) ;
          print_endline "========================================" ;
          let check_index bounds =
            verify_index_step bounds a b (fun ctx v0 i0 v1 i1 ->
                List.nth
                  (translate_comparator ctx [v0; i0; v1; i1] hlo_comparator_text)
                  1 )
          in
          let is_purely_entailed =
            !proven_axioms <> []
            && fst
                 (verify ~use_inductive_hypothesis:false a b z3_op ~check_index
                    !proven_axioms )
          in
          if is_purely_entailed then
            print_endline
              "\n\
               ⊂ REDUNDANT: pure consequence of existing axioms (no own IH \
               needed)"
          else begin
            let proven_directly =
              fst
                (verify ~use_inductive_hypothesis:true a b z3_op ~check_index [])
            in
            if proven_directly then begin
              print_endline
                "\n✓ PROVEN DIRECTLY (independent) — Adding to axiom set" ;
              proven_axioms := (a, b) :: !proven_axioms
            end
            else begin
              let proven_combined =
                fst
                  (verify ~use_inductive_hypothesis:true a b z3_op ~check_index
                     !proven_axioms )
              in
              if proven_combined then begin
                print_endline
                  "\n\
                   ✓ PROVEN (requires own IH + existing axioms) — Adding to \
                   axiom set" ;
                proven_axioms := (a, b) :: !proven_axioms
              end
              else printf "\n✗ NOT PROVEN\n"
            end
          end
        end
      with _ ->
        print_endline "\n! verify errored; deferring nested proof to final pass" ;
        deferred_nested := (a, b) :: !deferred_nested )
    candidates_sorted ;
  if !deferred_nested <> [] then begin
    print_endline
      "\n\
       ========================================\n\
       Deferred nested proof pass\n\
       ========================================" ;
    List.iter
      (fun (a, b) ->
        print_endline "\n----------------------------------------" ;
        print_endline (term_to_s a) ;
        print_endline (term_to_s b) ;
        print_endline "----------------------------------------" ;
        try
          let proven_nested = verify_nested a b z3_op !proven_axioms in
          if proven_nested then begin
            print_endline "\n⊂ REDUNDANT: pure consequence of existing axioms" ;
            proven_axioms := (a, b) :: !proven_axioms
          end
          else print_endline "\n✗ NOT PROVEN"
        with _ -> print_endline "\n✗ NOT PROVEN (nested verifier errored)" )
      (List.rev !deferred_nested)
  end
