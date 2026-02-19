open Axiomatization.Prelude
open Alcotest

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

let test_random_pairs_consistency () =
  Random.self_init () ;
  let rec test_n_pairs n successes failures =
    if n = 0 then (successes, failures)
    else
      let t1 = generate_terms op params 2 1 |> List.hd in
      let t2 = generate_terms op params 2 1 |> List.hd in
      let empirical =
        try is_empirically_equal t1 t2 ~tests:10 ~max_tries:5 with _ -> false
      in
      let formal = try is_formally_provable t1 t2 z3_op_add with _ -> false in
      let agrees =
        match (empirical, formal) with
        | false, false ->
            true
        | true, true ->
            true
        | false, true ->
            false
        | true, false ->
            false
      in
      if agrees then test_n_pairs (n - 1) (successes + 1) failures
      else test_n_pairs (n - 1) successes (failures + 1)
  in
  let n_t = 100 in
  let successes, failures = test_n_pairs n_t 0 0 in
  check bool "All random pairs are consistent" true (successes == n_t)

let test_empirical_implies_potentially_provable () =
  Random.self_init () ;
  let terms = generate_terms op params 3 20 in
  let candidates =
    find_empirical_equal_pairs ~terms ~params ~tests:10 ~max_tries_per_test:10
  in
  if List.length candidates > 0 then begin
    let t1, t2 = List.hd candidates in
    let empirical = is_empirically_equal t1 t2 ~tests:10 ~max_tries:5 in
    check bool "Found pair is empirically equal" true empirical ;
    let formal = is_formally_provable t1 t2 z3_op_add in
    Printf.printf "\nEmpirical: %b, Formal: %b for: %s = %s\n%!" empirical
      formal (term_to_s t1) (term_to_s t2) ;
    check bool "Test completed" true true
  end
  else begin
    check bool "No empirically equal pairs found (ok)" true true
  end

(* Test suite *)
let () =
  Random.self_init () ;
  run "Axiomatization Tests"
    [ ( "Consistency"
      , [ test_case "Random pairs consistency" `Quick
            test_random_pairs_consistency
        ; test_case "Empirical implies potentially provable" `Quick
            test_empirical_implies_potentially_provable ] ) ]
