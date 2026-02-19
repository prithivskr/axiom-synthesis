open Term
open Equality

let generalize_relation params t1 t2 =
  let candidates =
    collect_simplify_candidates (canonicalize t1)
    @ collect_simplify_candidates (canonicalize t2)
  in
  let unique_candidates =
    List.sort_uniq
      (fun x y -> String.compare (term_to_s x) (term_to_s y))
      candidates
  in
  let sorted_candidates =
    List.sort
      (fun x y -> compare (count_nodes y) (count_nodes x))
      unique_candidates
  in
  let rec try_simplify current_t1 current_t2 idx = function
    | [] ->
        (current_t1, current_t2)
    | candidate :: rest ->
        let gen_name = "G_" ^ string_of_int idx in
        let gen_term = Tensor gen_name in
        let next_t1 = replace_subterm candidate gen_term current_t1 in
        let next_t2 = replace_subterm candidate gen_term current_t2 in
        let temp_params =
          {params with tensor_pool= gen_name :: params.tensor_pool}
        in
        if
          check_equality next_t1 next_t2 temp_params ~tests:5
            ~max_tries_per_test:10
        then try_simplify next_t1 next_t2 (idx + 1) rest
        else try_simplify current_t1 current_t2 idx rest
  in
  try_simplify t1 t2 1 sorted_candidates
