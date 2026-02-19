open Axiomatization.Prelude
open Z3

let params = {var_pool= ["u"; "v"]; axes_pool= ["X"]; tensor_pool= ["A"; "B"]}

let op = fun a b -> a + b

let z3_op_add =
 fun ctx a b mul_scalar_scalar add_scalar_scalar ->
  Z3.Expr.mk_app ctx add_scalar_scalar [a; b]

let z3_op_mult =
 fun ctx a b mul_scalar_scalar add_scalar_scalar ->
  Z3.Expr.mk_app ctx mul_scalar_scalar [a; b]

let is_empirically_equal t1 t2 ~tests ~max_tries =
  check_equality t1 t2 params ~tests ~max_tries_per_test:max_tries

let is_formally_provable t1 t2 z3_op =
  try verify ~use_inductive_hypothesis:true ~verbose:true t1 t2 z3_op []
  with _ -> false

let find_mismatch () =
  Random.self_init () ;
  Printf.printf
    "Searching for mismatches between empirical and formal verifiers...\n%!" ;
  let rec loop count =
    (* Progress indicator *)
    if count mod 100 = 0 then Printf.printf "\rChecked %d pairs..." count ;
    flush stdout ;
    (* Generate two random terms *)
    let t1 = generate_terms op params 2 1 |> List.hd in
    let t2 = generate_terms op params 2 1 |> List.hd in
    (* Check empirical equality *)
    let empirical =
      try is_empirically_equal t1 t2 ~tests:10 ~max_tries:5
      with e ->
        Printf.printf "\nEmpirical checker crashed: %s\n%!"
          (Printexc.to_string e) ;
        false
    in
    (* Check formal provability *)
    let formal =
      try is_formally_provable t1 t2 z3_op_add
      with e ->
        Printf.printf "\nFormal checker crashed: %s\n%!" (Printexc.to_string e) ;
        false
    in
    (* Check for mismatch *)
    if empirical <> formal then begin
      Printf.printf "\n\n╔═══════════════════════════════════════╗\n" ;
      Printf.printf "║  MISMATCH FOUND (pair #%d)%*s║\n" count
        (14 - String.length (string_of_int count))
        "" ;
      Printf.printf "╚═══════════════════════════════════════╝\n\n" ;
      Printf.printf "Term 1:\n  %s\n\n" (term_to_s t1) ;
      Printf.printf "Term 2:\n  %s\n\n" (term_to_s t2) ;
      Printf.printf "Empirical verdict: %s\n"
        (if empirical then "EQUAL" else "NOT EQUAL") ;
      Printf.printf "Formal verdict:    %s\n"
        (if formal then "PROVABLE" else "NOT PROVABLE") ;
      Printf.printf "\nVariables in t1: %s\n"
        ( extract_vars t1 |> List.map fst |> List.sort_uniq compare
        |> String.concat ", " ) ;
      Printf.printf "Variables in t2: %s\n"
        ( extract_vars t2 |> List.map fst |> List.sort_uniq compare
        |> String.concat ", " ) ;
      Printf.printf "\n"
    end
    else loop (count + 1)
  in
  loop 1

let () = find_mismatch ()
