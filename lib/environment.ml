open Tensor
open Term

type env =
  { vars: (string, int) Hashtbl.t
  ; axes: (string, int list) Hashtbl.t
  ; tensors: (string, int tensor) Hashtbl.t }

let random_shape ~max_rank ~max_dim =
  let rank = 1 + Random.int max_rank in
  Array.init rank (fun _ -> 1 + Random.int max_dim)

let randomize_env ?(max_rank = 4) ?(max_dim = 4) params =
  let vars_tbl = Hashtbl.create (List.length params.var_pool) in
  let axes_tbl = Hashtbl.create (List.length params.axes_pool) in
  let tensors_tbl = Hashtbl.create (List.length params.tensor_pool) in
  let ranks = ref [] in
  List.iter
    (fun t ->
      let shape = random_shape ~max_rank ~max_dim in
      Hashtbl.add tensors_tbl t (random_int_tensor shape) ;
      ranks := Array.length shape :: !ranks )
    params.tensor_pool ;
  List.iter
    (fun v ->
      Hashtbl.add vars_tbl v (Random.int_in_range ~min:(-10000) ~max:10000) )
    params.var_pool ;
  let global_max_rank =
    match !ranks with [] -> 1 | l -> List.fold_left max 0 l
  in
  let global_max_rank = max 1 global_max_rank in
  List.iter
    (fun a ->
      let k = 1 + Random.int global_max_rank in
      let rec gen_unique acc n =
        if n = 0 then acc
        else
          let x = Random.int global_max_rank in
          if List.mem x acc then gen_unique acc n
          else gen_unique (x :: acc) (n - 1)
      in
      let idxs = gen_unique [] k in
      Hashtbl.add axes_tbl a idxs )
    params.axes_pool ;
  {vars= vars_tbl; axes= axes_tbl; tensors= tensors_tbl}

let randomize_env_unified_shapes ?(max_rank = 4) ?(max_dim = 4) params =
  let vars_tbl = Hashtbl.create (List.length params.var_pool) in
  let axes_tbl = Hashtbl.create (List.length params.axes_pool) in
  let tensors_tbl = Hashtbl.create (List.length params.tensor_pool) in
  let rank = 1 + Random.int max_rank in
  let shape = Array.init rank (fun _ -> 1 + Random.int max_dim) in
  List.iter
    (fun t -> Hashtbl.add tensors_tbl t (random_int_tensor shape))
    params.tensor_pool ;
  List.iter
    (fun v -> Hashtbl.add vars_tbl v (Random.int_in_range ~min:(-10) ~max:11))
    params.var_pool ;
  List.iter
    (fun a ->
      let k = 1 + Random.int rank in
      let rec gen_unique acc n =
        if n = 0 then acc
        else
          let x = Random.int rank in
          if List.mem x acc then gen_unique acc n
          else gen_unique (x :: acc) (n - 1)
      in
      let idxs = gen_unique [] k in
      Hashtbl.add axes_tbl a idxs )
    params.axes_pool ;
  {vars= vars_tbl; axes= axes_tbl; tensors= tensors_tbl}
