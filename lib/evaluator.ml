open Printf
open Tensor
open Term
open Environment

type value = VScalar of int | VTensor of int tensor

let map_tensor t f =
  let new_data = Array.map f t.data in
  {t with data= new_data}

let elementwise_binary t1 t2 f =
  if Array.length t1.shape <> Array.length t2.shape then
    failwith "elementwise: rank mismatch" ;
  for i = 0 to Array.length t1.shape - 1 do
    if t1.shape.(i) <> t2.shape.(i) then failwith "elementwise: shape mismatch"
  done ;
  let total = Array.length t1.data in
  let data = Array.init total (fun i -> f t1.data.(i) t2.data.(i)) in
  {shape= Array.copy t1.shape; data}

let scalar_left_multiplication s t f = map_tensor t (fun x -> f s x)

let scalar_right_multiplication t s f = map_tensor t (fun x -> f x s)

let reduction t op d =
  let old_shape = t.shape in
  let rank = Array.length old_shape in
  if d < 0 || d >= rank then failwith "rank error" ;
  let new_shape =
    Array.init (rank - 1) (fun i ->
        if i < d then old_shape.(i) else old_shape.(i + 1) )
  in
  let new_total = Array.fold_left ( * ) 1 new_shape in
  let new_data = Array.make new_total 0 in
  let new_t = {shape= new_shape; data= new_data} in
  let out_idx = Array.make (rank - 1) 0 in
  let in_idx = Array.make rank 0 in
  let rec fill dim =
    if dim = rank - 1 then (
      let oi = ref 0 in
      for i = 0 to rank - 1 do
        if i = d then ()
        else (
          in_idx.(i) <- out_idx.(!oi) ;
          incr oi )
      done ;
      let acc =
        ref (get t (Array.init rank (fun i -> if i = d then 0 else in_idx.(i))))
      in
      for k = 1 to old_shape.(d) - 1 do
        in_idx.(d) <- k ;
        acc := op !acc (get t in_idx)
      done ;
      set new_t out_idx !acc )
    else
      for i = 0 to new_shape.(dim) - 1 do
        out_idx.(dim) <- i ;
        fill (dim + 1)
      done
  in
  fill 0 ; new_t

let evaluate_addition va vb =
  match (va, vb) with
  | VScalar x, VScalar y ->
      VScalar (x + y)
  | VScalar s, VTensor t ->
      VTensor (map_tensor t (fun x -> s + x))
  | VTensor t, VScalar s ->
      VTensor (map_tensor t (fun x -> x + s))
  | VTensor t1, VTensor t2 ->
      VTensor (elementwise_binary t1 t2 (fun x y -> x + y))

let evaluate_multiplication va vb =
  match (va, vb) with
  | VScalar x, VScalar y ->
      VScalar (x * y)
  | VScalar s, VTensor t ->
      VTensor (map_tensor t (fun x -> s * x))
  | VTensor t, VScalar s ->
      VTensor (map_tensor t (fun x -> x * s))
  | VTensor t1, VTensor t2 ->
      VTensor (elementwise_binary t1 t2 (fun x y -> x * y))

let rec evaluate_term env t =
  match t with
  | Var x -> (
    try VScalar (Hashtbl.find env.vars x)
    with Not_found -> failwith ("Unbound var: " ^ x) )
  | Tensor x -> (
    try VTensor (Hashtbl.find env.tensors x)
    with Not_found -> failwith ("Unknown tensor: " ^ x) )
  | Add (a, b) ->
      let va = evaluate_term env a in
      let vb = evaluate_term env b in
      evaluate_addition va vb
  | Mult (a, b) ->
      let va = evaluate_term env a in
      let vb = evaluate_term env b in
      evaluate_multiplication va vb
  | Reduction (axis_name, op, inner) -> (
      let v = evaluate_term env inner in
      match v with
      | VScalar _ ->
          failwith "Reduction applied to scalar"
      | VTensor tval ->
          let axis_idxs =
            try Hashtbl.find env.axes axis_name
            with Not_found -> failwith ("Unknown axis: " ^ axis_name)
          in
          let idxs_sorted = List.sort (fun a b -> compare b a) axis_idxs in
          let result_tensor =
            List.fold_left (fun acc d -> reduction acc op d) tval idxs_sorted
          in
          VTensor result_tensor )

let print_value = function
  | VScalar x ->
      printf "Scalar: %d\n" x
  | VTensor t ->
      print_tensor t

let try_evaluate_term env term =
  try Some (evaluate_term env term) with Failure _ -> None

let equal_value va vb =
  match (va, vb) with
  | VScalar x, VScalar y ->
      x = y
  | VScalar _, VTensor _ ->
      false
  | VTensor _, VScalar _ ->
      false
  | VTensor t1, VTensor t2 ->
      if Array.length t1.shape <> Array.length t2.shape then false
      else
        let rec shapes_equal i =
          if i = Array.length t1.shape then true
          else if t1.shape.(i) <> t2.shape.(i) then false
          else shapes_equal (i + 1)
        in
        if not (shapes_equal 0) then false
        else
          let n = Array.length t1.data in
          let rec loop i =
            if i = n then true
            else if t1.data.(i) <> t2.data.(i) then false
            else loop (i + 1)
          in
          loop 0
