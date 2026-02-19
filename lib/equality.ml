open Printf
open Evaluator
open Environment
open Term

let print_candidate a b =
  printf "Candidate equality:\n  %s\n  ==\n  %s\n\n" (term_to_s a) (term_to_s b)

let find_empirical_equal_pairs ~terms ~params ~tests ~max_tries_per_test =
  let n = List.length terms in
  let results = ref [] in
  for i = 0 to n - 1 do
    for j = i + 1 to n - 1 do
      let a = List.nth terms i in
      let b = List.nth terms j in
      let rec run_k k =
        if k >= tests then (
          results := (a, b) :: !results ;
          true )
        else
          let rec try_env attempt =
            if attempt > max_tries_per_test then false
            else
              let env =
                randomize_env_unified_shapes ~max_rank:4 ~max_dim:10 params
              in
              match (try_evaluate_term env a, try_evaluate_term env b) with
              | Some va, Some vb ->
                  if equal_value va vb then run_k (k + 1) else false
              | _, _ ->
                  try_env (attempt + 1)
          in
          try_env 0
      in
      ignore (run_k 0)
    done
  done ;
  !results

let check_equality t1 t2 params ~tests ~max_tries_per_test =
  let rec run_k k =
    if k >= tests then true
    else
      let rec try_env attempt =
        if attempt > max_tries_per_test then false
        else
          let env =
            randomize_env_unified_shapes ~max_rank:4 ~max_dim:10 params
          in
          match (try_evaluate_term env t1, try_evaluate_term env t2) with
          | Some va, Some vb ->
              if equal_value va vb then run_k (k + 1) else false
          | _, _ ->
              try_env (attempt + 1)
      in
      try_env 0
  in
  run_k 0
