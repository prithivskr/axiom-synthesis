open Printf
open Z3
open Axiomatization.Prelude

(* Main *)

type config_t =
  { n_candidates: int
  ; op: int -> int -> int
  ; z3_op:
         context
      -> Expr.expr
      -> Expr.expr
      -> FuncDecl.func_decl
      -> FuncDecl.func_decl
      -> Expr.expr }

let conf =
  { n_candidates= 5
  ; op= (fun a b -> max a b)
  ; z3_op=
      (fun ctx a b mul_scalar_scalar add_scalar_scalar ->
        Boolean.mk_ite ctx (Arithmetic.mk_ge ctx a b) a b ) }

(*
Boolean.mk_ite ctx (Arithmetic.mk_ge ctx x y) x y
 *)

let () =
  Random.self_init () ;
  let n_candidates = conf.n_candidates in
  let batch_size = 50 in
  let params = {var_pool= ["u"]; axes_pool= ["X"]; tensor_pool= ["A"; "B"]} in
  let op = conf.op in
  let z3_op = conf.z3_op in
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
          let is_purely_entailed =
            !proven_axioms <> []
            && fst (verify ~use_inductive_hypothesis:false a b z3_op !proven_axioms)
          in
          if is_purely_entailed then
            print_endline
              "\n\
               ⊂ REDUNDANT: pure consequence of existing axioms (no own IH \
               needed)"
          else begin
            let proven_directly =
              fst (verify ~use_inductive_hypothesis:true a b z3_op [])
            in
            if proven_directly then begin
              print_endline
                "\n✓ PROVEN DIRECTLY (independent) — Adding to axiom set" ;
              proven_axioms := (a, b) :: !proven_axioms
            end
            else begin
              let proven_combined =
                fst (verify ~use_inductive_hypothesis:true a b z3_op !proven_axioms)
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
