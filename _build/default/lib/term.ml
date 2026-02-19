type 'a term =
  | Var of string
  | Mult of 'a term * 'a term
  | Add of 'a term * 'a term
  | Tensor of string
  | Reduction of string * ('a -> 'a -> 'a) * 'a term

type term_params =
  {var_pool: string list; axes_pool: string list; tensor_pool: string list}

let rec term_to_s = function
  | Var x ->
      x
  | Mult (a, b) ->
      "(" ^ term_to_s a ^ " * " ^ term_to_s b ^ ")"
  | Add (a, b) ->
      "(" ^ term_to_s a ^ " + " ^ term_to_s b ^ ")"
  | Tensor x ->
      x
  | Reduction (x, _, t) ->
      "reduce(" ^ term_to_s t ^ ", " ^ x ^ ")"

let choose l = List.nth l (Random.int (List.length l))

let rec flatten_add = function
  | Add (a, b) ->
      flatten_add a @ flatten_add b
  | t ->
      [t]

let rec flatten_mult = function
  | Mult (a, b) ->
      flatten_mult a @ flatten_mult b
  | t ->
      [t]

let rec canonicalize term =
  let norm = canonicalize in
  match term with
  | Add (a, b) ->
      let terms = List.map norm (flatten_add (Add (a, b))) in
      let sorted =
        List.sort (fun x y -> compare (term_to_s x) (term_to_s y)) terms
      in
      List.fold_left
        (fun acc t ->
          match acc with None -> Some t | Some acc_t -> Some (Add (acc_t, t)) )
        None sorted
      |> Option.get
  | Mult (a, b) ->
      let terms = List.map norm (flatten_mult (Mult (a, b))) in
      let sorted =
        List.sort (fun x y -> compare (term_to_s x) (term_to_s y)) terms
      in
      List.fold_left
        (fun acc t ->
          match acc with None -> Some t | Some acc_t -> Some (Mult (acc_t, t)) )
        None sorted
      |> Option.get
  | Reduction (axis, op, inner) ->
      Reduction (axis, op, norm inner)
  | Var _ | Tensor _ ->
      term

let rec has_reduction = function
  | Reduction _ ->
      true
  | Add (a, b) | Mult (a, b) ->
      has_reduction a || has_reduction b
  | Var _ | Tensor _ ->
      false

let rec collect_vars = function
  | Var _ ->
      []
  | Tensor x ->
      [x]
  | Add (a, b) | Mult (a, b) ->
      collect_vars a @ collect_vars b
  | Reduction (_, _, t) ->
      collect_vars t

let has_exactly_two_vars t =
  let vars = collect_vars t in
  let unique = List.sort_uniq String.compare vars in
  List.length unique = 2

let rec count_nodes = function
  | Var _ | Tensor _ ->
      1
  | Reduction (_, _, t) ->
      1 + count_nodes t
  | Add (a, b) | Mult (a, b) ->
      1 + count_nodes a + count_nodes b

let rec replace_subterm target replacement t =
  if term_to_s t = term_to_s target then replacement
  else
    match t with
    | Add (a, b) ->
        Add
          ( replace_subterm target replacement a
          , replace_subterm target replacement b )
    | Mult (a, b) ->
        Mult
          ( replace_subterm target replacement a
          , replace_subterm target replacement b )
    | Reduction (ax, op, inner) ->
        Reduction (ax, op, replace_subterm target replacement inner)
    | _ ->
        t

let collect_simplify_candidates term =
  let rec traverse t acc =
    if has_reduction t then
      match t with
      | Reduction (_, _, inner) ->
          traverse inner acc
      | Add (a, b) | Mult (a, b) ->
          traverse b (traverse a acc)
      | _ ->
          acc
    else match t with Add _ | Mult _ -> t :: acc | _ -> acc
  in
  let candidates = traverse term [] in
  List.sort_uniq
    (fun x y -> String.compare (term_to_s x) (term_to_s y))
    candidates

let rec term_depth = function
  | Var _ ->
      1
  | Mult (a, b) ->
      1 + max (term_depth a) (term_depth b)
  | Add (a, b) ->
      1 + max (term_depth a) (term_depth b)
  | Tensor _ ->
      1
  | Reduction (_, _, t) ->
      1 + term_depth t

let rec extract_vars = function
  | Var v ->
      [(v, 0)]
  | Mult (a, b) ->
      extract_vars a @ extract_vars b
  | Add (a, b) ->
      extract_vars a @ extract_vars b
  | Tensor v ->
      [(v, 1)]
  | Reduction (_, _, a) ->
      extract_vars a

let rec hash_term = function
  | Var x ->
      Hashtbl.hash ("V", x)
  | Tensor x ->
      Hashtbl.hash ("T", x)
  | Add (a, b) ->
      Hashtbl.hash ("A", hash_term a, hash_term b)
  | Mult (a, b) ->
      Hashtbl.hash ("M", hash_term a, hash_term b)
  | Reduction (ax, op, t) ->
      Hashtbl.hash ("R", ax, op, hash_term t)
