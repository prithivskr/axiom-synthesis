open Z3
open Term
open Verify

let rec find_reduction = function
  | Reduction (_, _, inner) ->
      Some inner
  | Add (a, b) | Mult (a, b) -> (
    match find_reduction a with
    | Some inner ->
        Some inner
    | None ->
        find_reduction b )
  | _ ->
      None

let rec inner_term_to_z3 ctx vars tensor_val term =
  match term with
  | Var x ->
      Hashtbl.find vars x
  | Tensor _ ->
      tensor_val
  | Add (a, b) ->
      let a_z3 = inner_term_to_z3 ctx vars tensor_val a in
      let b_z3 = inner_term_to_z3 ctx vars tensor_val b in
      Arithmetic.mk_add ctx [a_z3; b_z3]
  | Mult (a, b) ->
      let a_z3 = inner_term_to_z3 ctx vars tensor_val a in
      let b_z3 = inner_term_to_z3 ctx vars tensor_val b in
      Arithmetic.mk_mul ctx [a_z3; b_z3]
  | Reduction _ ->
      failwith "Nested reductions in index verification not yet supported"

let verify_index_step bounds lhs rhs z3_reduce_index =
  (* We no longer print anything here so we are silent in the loop, or maybe print a small debug line if we want? Let's stay silent. *)
  let cfg = [("model", "true")] in
  let ctx = mk_context cfg in
  let solver = Solver.mk_solver ctx None in
  let int_sort = Arithmetic.Integer.mk_sort ctx in
  let v0 = Expr.mk_const_s ctx "v0" int_sort in
  let i0 = Expr.mk_const_s ctx "i0" int_sort in
  let v1 = Expr.mk_const_s ctx "v1" int_sort in
  let i1 = Expr.mk_const_s ctx "i1" int_sort in
  let vars = Hashtbl.create 10 in
  let rec collect_v = function
    | Var x ->
        if not (Hashtbl.mem vars x) then
          Hashtbl.add vars x (Expr.mk_const_s ctx x int_sort)
    | Add (a, b) | Mult (a, b) ->
        collect_v a ; collect_v b
    | Reduction (_, _, inner) ->
        collect_v inner
    | Tensor _ ->
        ()
  in
  collect_v lhs ;
  collect_v rhs ;
  let inner_lhs =
    match find_reduction lhs with
    | Some t ->
        t
    | None ->
        failwith "No reduction found in LHS"
  in
  let inner_rhs =
    match find_reduction rhs with
    | Some t ->
        t
    | None ->
        failwith "No reduction found in RHS"
  in
  let v0_lhs = inner_term_to_z3 ctx vars v0 inner_lhs in
  let v1_lhs = inner_term_to_z3 ctx vars v1 inner_lhs in
  let v0_rhs = inner_term_to_z3 ctx vars v0 inner_rhs in
  let v1_rhs = inner_term_to_z3 ctx vars v1 inner_rhs in
  let lhs_idx = z3_reduce_index ctx v0_lhs i0 v1_lhs i1 in
  let rhs_idx = z3_reduce_index ctx v0_rhs i0 v1_rhs i1 in
  let eq = Boolean.mk_eq ctx lhs_idx rhs_idx in
  let not_eq = Boolean.mk_not ctx eq in
  Solver.add solver [not_eq] ;
  let scalar_vars = Hashtbl.fold (fun k v acc ->
    if Sort.equal (Expr.get_sort v) int_sort then (k, v) :: acc else acc
  ) vars [] in
  List.iter (fun (name, b) ->
     let expr_opt = List.assoc_opt name scalar_vars in
     match expr_opt with
     | Some expr ->
         (match b.lower with
          | Some l -> 
              let num = Expr.mk_numeral_int ctx l (Arithmetic.Real.mk_sort ctx) in
              if b.lower_strict then
                Solver.add solver [Arithmetic.mk_gt ctx expr num]
              else
                Solver.add solver [Arithmetic.mk_ge ctx expr num]
          | None -> ());
         (match b.upper with
          | Some u -> 
              let num = Expr.mk_numeral_int ctx u (Arithmetic.Real.mk_sort ctx) in
              if b.upper_strict then
                Solver.add solver [Arithmetic.mk_lt ctx expr num]
              else
                Solver.add solver [Arithmetic.mk_le ctx expr num]
          | None -> ())
     | None -> ()
  ) bounds;

  match Solver.check solver [] with
  | Solver.UNSATISFIABLE -> Proven
  | Solver.SATISFIABLE ->
      let model = Option.get (Solver.get_model solver) in
      let env = List.filter_map (fun (name, expr) ->
         match Model.eval model expr true with
         | Some v_expr ->
             let s = Expr.to_string v_expr in
             let s_clean = 
               if String.length s > 0 && s.[0] = '(' then
                 let inner = String.sub s 1 (String.length s - 2) in
                 match String.split_on_char ' ' inner with
                 | ["-"; n] -> "-" ^ n
                 | _ -> inner
               else s
             in
             (try Some (name, int_of_string s_clean) with _ -> None)
         | None -> None
      ) scalar_vars in
      Counterexample env
  | Solver.UNKNOWN -> Unknown
