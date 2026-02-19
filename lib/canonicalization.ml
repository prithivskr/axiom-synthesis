open Term

let sort_terms l = List.sort (fun x y -> compare (term_to_s x) (term_to_s y)) l

let rebuild_op terms op_ctor identity_term =
  match terms with
  | [] ->
      identity_term
  | [t] ->
      t
  | h :: t ->
      List.fold_left op_ctor h t

let find_common_terms terms1 terms2 =
  let l1 = sort_terms terms1 in
  let l2 = sort_terms terms2 in
  let rec loop acc_common acc_rem1 acc_rem2 l1 l2 =
    match (l1, l2) with
    | [], _ | _, [] ->
        ( List.rev acc_common
        , List.rev_append acc_rem1 l1
        , List.rev_append acc_rem2 l2 )
    | h1 :: t1, h2 :: t2 ->
        let s1 = term_to_s h1 in
        let s2 = term_to_s h2 in
        let cmp = compare s1 s2 in
        if cmp = 0 then loop (h1 :: acc_common) acc_rem1 acc_rem2 t1 t2
        else if cmp < 0 then loop acc_common (h1 :: acc_rem1) acc_rem2 t1 l2
        else (* cmp > 0 *)
          loop acc_common acc_rem1 (h2 :: acc_rem2) l1 t2
  in
  loop [] [] [] l1 l2

let rec strip_common_structure (t1, t2) =
  let t1_canon = canonicalize t1 in
  let t2_canon = canonicalize t2 in
  let stripped =
    match (t1_canon, t2_canon) with
    | Reduction (axis1, _, inner1), Reduction (axis2, _, inner2) ->
        if axis1 = axis2 then (inner1, inner2) else (t1_canon, t2_canon)
    | Add _, _ | _, Add _ ->
        let terms1 = flatten_add t1_canon in
        let terms2 = flatten_add t2_canon in
        let common, remaining1, remaining2 = find_common_terms terms1 terms2 in
        if common = [] then (t1_canon, t2_canon)
        else
          ( rebuild_op remaining1 (fun a b -> Add (a, b)) (Tensor "ID_ADD")
          , rebuild_op remaining2 (fun a b -> Add (a, b)) (Tensor "ID_ADD") )
    | Mult _, _ | _, Mult _ ->
        let terms1 = flatten_mult t1_canon in
        let terms2 = flatten_mult t2_canon in
        let common, remaining1, remaining2 = find_common_terms terms1 terms2 in
        if common = [] then (t1_canon, t2_canon)
        else
          ( rebuild_op remaining1 (fun a b -> Mult (a, b)) (Tensor "ID_MULT")
          , rebuild_op remaining2 (fun a b -> Mult (a, b)) (Tensor "ID_MULT") )
    | _, _ ->
        (t1_canon, t2_canon)
  in
  if
    term_to_s t1_canon <> term_to_s (fst stripped)
    || term_to_s t2_canon <> term_to_s (snd stripped)
  then strip_common_structure stripped
  else stripped

let rec transform_no_reduce_helper memo term =
  match term with
  | Var x ->
      Var x
  | Tensor x ->
      Tensor x
  | Add (a, b) ->
      Add (transform_no_reduce_helper memo a, transform_no_reduce_helper memo b)
  | Mult (a, b) ->
      Mult (transform_no_reduce_helper memo a, transform_no_reduce_helper memo b)
  | Reduction (_, _, inner) -> (
      let inner_key = term_to_s (canonicalize inner) in
      try
        let new_tensor_name = Hashtbl.find memo inner_key in
        Tensor new_tensor_name
      with Not_found ->
        let new_id = Hashtbl.length memo in
        let new_tensor_name = "T_reduce_" ^ string_of_int new_id in
        Hashtbl.add memo inner_key new_tensor_name ;
        Tensor new_tensor_name )

let transform_to_no_reductions memo term = transform_no_reduce_helper memo term
