open Term

let rec gen_term op params depth =
  if depth = 0 || Random.float 1.0 < 0.3 then
    match Random.int 2 with
    | 0 ->
        Var (choose params.var_pool)
    | _ ->
        Tensor (choose params.tensor_pool)
  else
    match Random.int 3 with
    | 0 ->
        Add (gen_term op params (depth - 1), gen_term op params (depth - 1))
    | 1 ->
        Mult (gen_term op params (depth - 1), gen_term op params (depth - 1))
    | _ ->
        Reduction (choose params.axes_pool, op, gen_term op params (depth - 1))

let generate_terms op params depth count =
  let seen = Hashtbl.create (count * 2) in
  let results = ref [] in
  let attempts = ref 0 in
  let max_attempts = count * 50 in
  while List.length !results < count && !attempts < max_attempts do
    incr attempts ;
    let t = gen_term op params depth in
    if has_reduction t then begin
      let t = canonicalize t in
      if not (Hashtbl.mem seen t) then begin
        Hashtbl.add seen t () ;
        results := t :: !results
      end
    end
  done ;
  !results
