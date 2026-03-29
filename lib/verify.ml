open Term
open Z3

type bound =
  {lower: int option; lower_strict: bool; upper: int option; upper_strict: bool}

type verify_result = Proven | Counterexample of (string * int) list | Unknown

let print_bounds bs =
  let s =
    List.map
      (fun (name, b) ->
        let l_str =
          match b.lower with Some l -> string_of_int l | None -> "-inf"
        in
        let u_str =
          match b.upper with Some u -> string_of_int u | None -> "inf"
        in
        let l_paren = if b.lower_strict || b.lower = None then "(" else "[" in
        let u_paren = if b.upper_strict || b.upper = None then ")" else "]" in
        Printf.sprintf "%s in %s%s, %s%s" name l_paren l_str u_str u_paren )
      bs
  in
  String.concat ", " s

let is_valid b =
  match (b.lower, b.upper) with
  | Some l, Some u ->
      let eff_l = if b.lower_strict then l + 1 else l in
      let eff_u = if b.upper_strict then u - 1 else u in
      eff_l <= eff_u && not (eff_l = 0 && eff_u = 0)
  | _ ->
      true

let declare_vars ctx int_sort tensor_sort lhs rhs =
  let vars = extract_vars lhs @ extract_vars rhs in
  let uniq = List.sort_uniq (fun (a, _) (b, _) -> compare a b) vars in
  List.fold_left
    (fun acc (name, kind) ->
      let sort =
        match kind with
        | 0 ->
            int_sort
        | 1 ->
            tensor_sort
        | _ ->
            failwith "Unknown variable kind"
      in
      let sym = Symbol.mk_string ctx name in
      let expr = Expr.mk_const ctx sym sort in
      Hashtbl.add acc name expr ; acc )
    (Hashtbl.create (List.length uniq))
    uniq

let rec term_to_z3_expr ctx vars mul_tensor_tensor mul_scalar_tensor
    mul_scalar_scalar add_tensor_tensor add_scalar_tensor add_scalar_scalar r2
    term =
  match term with
  | Var x ->
      Hashtbl.find vars x
  | Tensor x ->
      Hashtbl.find vars x
  | Add (a, b) ->
      let a_expr =
        term_to_z3_expr ctx vars mul_tensor_tensor mul_scalar_tensor
          mul_scalar_scalar add_tensor_tensor add_scalar_tensor
          add_scalar_scalar r2 a
      in
      let b_expr =
        term_to_z3_expr ctx vars mul_tensor_tensor mul_scalar_tensor
          mul_scalar_scalar add_tensor_tensor add_scalar_tensor
          add_scalar_scalar r2 b
      in
      let a_sort = Expr.get_sort a_expr in
      let b_sort = Expr.get_sort b_expr in
      let int_sort = Arithmetic.Integer.mk_sort ctx in
      let a_is_int = Sort.equal a_sort int_sort in
      let b_is_int = Sort.equal b_sort int_sort in
      if a_is_int && b_is_int then
        Expr.mk_app ctx add_scalar_scalar [a_expr; b_expr]
      else if a_is_int && not b_is_int then
        Expr.mk_app ctx add_scalar_tensor [a_expr; b_expr]
      else if (not a_is_int) && b_is_int then
        Expr.mk_app ctx add_scalar_tensor [b_expr; a_expr]
      else Expr.mk_app ctx add_tensor_tensor [a_expr; b_expr]
  | Mult (a, b) ->
      let a_expr =
        term_to_z3_expr ctx vars mul_tensor_tensor mul_scalar_tensor
          mul_scalar_scalar add_tensor_tensor add_scalar_tensor
          add_scalar_scalar r2 a
      in
      let b_expr =
        term_to_z3_expr ctx vars mul_tensor_tensor mul_scalar_tensor
          mul_scalar_scalar add_tensor_tensor add_scalar_tensor
          add_scalar_scalar r2 b
      in
      let a_sort = Expr.get_sort a_expr in
      let b_sort = Expr.get_sort b_expr in
      let int_sort = Arithmetic.Integer.mk_sort ctx in
      let a_is_int = Sort.equal a_sort int_sort in
      let b_is_int = Sort.equal b_sort int_sort in
      if a_is_int && b_is_int then
        Expr.mk_app ctx mul_scalar_scalar [a_expr; b_expr]
      else if a_is_int && not b_is_int then
        Expr.mk_app ctx mul_scalar_tensor [a_expr; b_expr]
      else if (not a_is_int) && b_is_int then
        Expr.mk_app ctx mul_scalar_tensor [b_expr; a_expr]
      else Expr.mk_app ctx mul_tensor_tensor [a_expr; b_expr]
  | Reduction (_, _, inner) ->
      let inner_expr =
        term_to_z3_expr ctx vars mul_tensor_tensor mul_scalar_tensor
          mul_scalar_scalar add_tensor_tensor add_scalar_tensor
          add_scalar_scalar r2 inner
      in
      Expr.mk_app ctx r2 [inner_expr]

let check_addition_distributes ctx operation mul_scalar_scalar add_scalar_scalar
    z3_op =
  let solver = Solver.mk_solver ctx None in
  let params = Params.mk_params ctx in
  Params.add_int params (Symbol.mk_string ctx "timeout") 2000 ;
  Solver.set_parameters solver params ;
  let int_sort = Arithmetic.Integer.mk_sort ctx in
  let a = Expr.mk_const ctx (Symbol.mk_string ctx "at") int_sort in
  let b = Expr.mk_const ctx (Symbol.mk_string ctx "bt") int_sort in
  let c = Expr.mk_const ctx (Symbol.mk_string ctx "ct") int_sort in
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx operation [a; b])
              (z3_op ctx a b mul_scalar_scalar add_scalar_scalar) )
           None [] [] None None ) ] ;
  (* Addition and multiplication definition *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx add_scalar_scalar [a; b])
              (Arithmetic.mk_add ctx [a; b]) )
           None [] [] None None ) ] ;
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_scalar_scalar [a; b])
              (Arithmetic.mk_mul ctx [a; b]) )
           None [] [] None None ) ] ;
  Solver.add solver
    [ Boolean.mk_not ctx
        (Boolean.mk_eq ctx
           (Expr.mk_app ctx operation
              [ Expr.mk_app ctx add_scalar_scalar [a; c]
              ; Expr.mk_app ctx add_scalar_scalar [b; c] ] )
           (Expr.mk_app ctx add_scalar_scalar
              [Expr.mk_app ctx operation [a; b]; c] ) ) ] ;
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE ->
      true
  | Solver.SATISFIABLE ->
      false
  | Solver.UNKNOWN ->
      false

let check_multiplication_distributes ctx operation mul_scalar_scalar
    add_scalar_scalar z3_op =
  let solver = Solver.mk_solver ctx None in
  let params = Params.mk_params ctx in
  Params.add_int params (Symbol.mk_string ctx "timeout") 2000 ;
  Solver.set_parameters solver params ;
  let int_sort = Arithmetic.Integer.mk_sort ctx in
  let a = Expr.mk_const ctx (Symbol.mk_string ctx "at") int_sort in
  let b = Expr.mk_const ctx (Symbol.mk_string ctx "bt") int_sort in
  let c = Expr.mk_const ctx (Symbol.mk_string ctx "ct") int_sort in
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx operation [a; b])
              (z3_op ctx a b mul_scalar_scalar add_scalar_scalar) )
           None [] [] None None ) ] ;
  (* Addition and multiplication definition *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx add_scalar_scalar [a; b])
              (Arithmetic.mk_add ctx [a; b]) )
           None [] [] None None ) ] ;
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_scalar_scalar [a; b])
              (Arithmetic.mk_mul ctx [a; b]) )
           None [] [] None None ) ] ;
  Solver.add solver
    [ Boolean.mk_not ctx
        (Boolean.mk_eq ctx
           (Expr.mk_app ctx operation
              [ Expr.mk_app ctx mul_scalar_scalar [a; c]
              ; Expr.mk_app ctx mul_scalar_scalar [b; c] ] )
           (Expr.mk_app ctx mul_scalar_scalar
              [Expr.mk_app ctx operation [a; b]; c] ) ) ] ;
  match Solver.check solver [] with
  | Solver.UNSATISFIABLE ->
      true
  | Solver.SATISFIABLE ->
      false
  | Solver.UNKNOWN ->
      false

let verify ?(use_inductive_hypothesis = true) ?(verbose = false)
    ?(check_index = fun _ -> Proven) lhs rhs z3_op proven_axioms =
  print_endline "Verifying..." ;
  let cfg = [("model", "true")] in
  let ctx = mk_context cfg in
  let int_sort = Arithmetic.Integer.mk_sort ctx in
  let tensor_sort = Sort.mk_uninterpreted ctx (Symbol.mk_string ctx "Tensor") in
  let mk_fun name dom rng =
    FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx name) dom rng
  in
  let mul_tensor_tensor =
    mk_fun "MulTensorTensor" [tensor_sort; tensor_sort] tensor_sort
  in
  let mul_scalar_tensor =
    mk_fun "MulScalarTensor" [int_sort; tensor_sort] tensor_sort
  in
  let mul_scalar_scalar =
    mk_fun "MulScalarScalar" [int_sort; int_sort] int_sort
  in
  let add_tensor_tensor =
    mk_fun "AddTensorTensor" [tensor_sort; tensor_sort] tensor_sort
  in
  let add_scalar_tensor =
    mk_fun "AddScalarTensor" [int_sort; tensor_sort] tensor_sort
  in
  let add_scalar_scalar =
    mk_fun "AddScalarScalar" [int_sort; int_sort] int_sort
  in
  let r1 = mk_fun "R1" [tensor_sort] int_sort in
  let r2 = mk_fun "R2" [tensor_sort] int_sort in
  let operation = mk_fun "operation" [int_sort; int_sort] int_sort in
  let add_distributes =
    check_addition_distributes ctx operation mul_scalar_scalar add_scalar_scalar
      z3_op
  in
  let mul_distributes =
    check_multiplication_distributes ctx operation mul_scalar_scalar
      add_scalar_scalar z3_op
  in
  let e_fun = mk_fun "E" [tensor_sort] int_sort in
  let solver = Solver.mk_solver ctx None in
  let params = Params.mk_params ctx in
  Params.add_int params (Symbol.mk_string ctx "timeout") 2000 ;
  Solver.set_parameters solver params ;
  let a = Expr.mk_const ctx (Symbol.mk_string ctx "a") int_sort in
  let b = Expr.mk_const ctx (Symbol.mk_string ctx "b") int_sort in
  (* MulScalarScalar a b = a * b *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_scalar_scalar [a; b])
              (Arithmetic.mk_mul ctx [a; b]) )
           None [] [] None None ) ] ;
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_scalar_scalar [a; b])
              (Expr.mk_app ctx mul_scalar_scalar [b; a]) )
           None [] [] None None ) ] ;
  (* AddScalarScalar a b = a + b *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx add_scalar_scalar [a; b])
              (Arithmetic.mk_add ctx [a; b]) )
           None [] [] None None ) ] ;
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx add_scalar_scalar [a; b])
              (Expr.mk_app ctx add_scalar_scalar [b; a]) )
           None [] [] None None ) ] ;
  (* R1 t = operation (R2 t) (E t) *)
  let t = Expr.mk_const ctx (Symbol.mk_string ctx "t") tensor_sort in
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [t]
           (Boolean.mk_eq ctx (Expr.mk_app ctx r1 [t])
              (Expr.mk_app ctx operation
                 [Expr.mk_app ctx r2 [t]; Expr.mk_app ctx e_fun [t]] ) )
           None [] [] None None ) ] ;
  (* Inductive hypothesis *)
  let exp_vars = declare_vars ctx int_sort tensor_sort lhs rhs in
  let f = Expr.mk_const ctx (Symbol.mk_string ctx "f") tensor_sort in
  let v = Expr.mk_const ctx (Symbol.mk_string ctx "v") int_sort in
  let hyp_lhs =
    term_to_z3_expr ctx exp_vars mul_tensor_tensor mul_scalar_tensor
      mul_scalar_scalar add_tensor_tensor add_scalar_tensor add_scalar_scalar r2
      lhs
  in
  let hyp_rhs =
    term_to_z3_expr ctx exp_vars mul_tensor_tensor mul_scalar_tensor
      mul_scalar_scalar add_tensor_tensor add_scalar_tensor add_scalar_scalar r2
      rhs
  in
  let lhs_vars = extract_vars lhs |> List.map fst |> List.sort_uniq compare in
  let rhs_vars = extract_vars rhs |> List.map fst |> List.sort_uniq compare in
  let same_vars = lhs_vars = rhs_vars in
  let var_list = Hashtbl.fold (fun _ v acc -> v :: acc) exp_vars [] in
  let g = Expr.mk_const ctx (Symbol.mk_string ctx "g") tensor_sort in
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [f; g]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx e_fun
                 [Expr.mk_app ctx add_tensor_tensor [f; g]] )
              (Expr.mk_app ctx add_scalar_scalar
                 [Expr.mk_app ctx e_fun [f]; Expr.mk_app ctx e_fun [g]] ) )
           None [] [] None None ) ] ;
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [f; v]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx e_fun
                 [Expr.mk_app ctx add_scalar_tensor [v; f]] )
              (Expr.mk_app ctx add_scalar_scalar
                 [v; Expr.mk_app ctx e_fun [f]] ) )
           None [] [] None None ) ] ;
  (* E homomorphism over multiplication *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [f; g]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx e_fun
                 [Expr.mk_app ctx mul_tensor_tensor [f; g]] )
              (Expr.mk_app ctx mul_scalar_scalar
                 [Expr.mk_app ctx e_fun [f]; Expr.mk_app ctx e_fun [g]] ) )
           None [] [] None None ) ] ;
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [f; v]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx e_fun
                 [Expr.mk_app ctx mul_scalar_tensor [v; f]] )
              (Expr.mk_app ctx mul_scalar_scalar
                 [v; Expr.mk_app ctx e_fun [f]] ) )
           None [] [] None None ) ] ;
  (* operation semantics *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx operation [a; b])
              (z3_op ctx a b mul_scalar_scalar add_scalar_scalar) )
           None [] [] None None ) ] ;
  let c = Expr.mk_const ctx (Symbol.mk_string ctx "c") int_sort in
  if add_distributes then
    Solver.add solver
      [ Quantifier.expr_of_quantifier
          (Quantifier.mk_forall_const ctx [a; b; c]
             (Boolean.mk_eq ctx
                (Expr.mk_app ctx operation
                   [ Expr.mk_app ctx add_scalar_scalar [a; c]
                   ; Expr.mk_app ctx add_scalar_scalar [b; c] ] )
                (Expr.mk_app ctx add_scalar_scalar
                   [Expr.mk_app ctx operation [a; b]; c] ) )
             None [] [] None None ) ] ;
  if mul_distributes then
    Solver.add solver
      [ Quantifier.expr_of_quantifier
          (Quantifier.mk_forall_const ctx [a; b; c]
             (Boolean.mk_eq ctx
                (Expr.mk_app ctx operation
                   [ Expr.mk_app ctx mul_scalar_scalar [a; c]
                   ; Expr.mk_app ctx mul_scalar_scalar [b; c] ] )
                (Expr.mk_app ctx mul_scalar_scalar
                   [Expr.mk_app ctx operation [a; b]; c] ) )
             None [] [] None None ) ] ;
  (* MulScalarTensor distributes over AddScalarTensor *)
  let c_tensor = Expr.mk_const ctx (Symbol.mk_string ctx "C") tensor_sort in
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b; c_tensor]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_scalar_tensor
                 [a; Expr.mk_app ctx add_scalar_tensor [b; c_tensor]] )
              (Expr.mk_app ctx add_scalar_tensor
                 [ Expr.mk_app ctx mul_scalar_scalar [a; b]
                 ; Expr.mk_app ctx mul_scalar_tensor [a; c_tensor] ] ) )
           None [] [] None None ) ] ;
  (* AddTensorTensor commutativity *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [f; g]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx add_tensor_tensor [f; g])
              (Expr.mk_app ctx add_tensor_tensor [g; f]) )
           None [] [] None None ) ] ;
  (* MulTensorTensor commutativity *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [f; g]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_tensor_tensor [f; g])
              (Expr.mk_app ctx mul_tensor_tensor [g; f]) )
           None [] [] None None ) ] ;
  (* AddTensorTensor associativity *)
  let h = Expr.mk_const ctx (Symbol.mk_string ctx "h") tensor_sort in
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [f; g; h]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx add_tensor_tensor
                 [Expr.mk_app ctx add_tensor_tensor [f; g]; h] )
              (Expr.mk_app ctx add_tensor_tensor
                 [f; Expr.mk_app ctx add_tensor_tensor [g; h]] ) )
           None [] [] None None ) ] ;
  (* MulTensorTensor associativity *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [f; g; h]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_tensor_tensor
                 [Expr.mk_app ctx mul_tensor_tensor [f; g]; h] )
              (Expr.mk_app ctx mul_tensor_tensor
                 [f; Expr.mk_app ctx mul_tensor_tensor [g; h]] ) )
           None [] [] None None ) ] ;
  (* Scalar add commutes with tensor add nesting:
     (f + g) + a = (f + a) + g *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; f; g]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx add_scalar_tensor
                 [a; Expr.mk_app ctx add_tensor_tensor [f; g]] )
              (Expr.mk_app ctx add_tensor_tensor
                 [Expr.mk_app ctx add_scalar_tensor [a; f]; g] ) )
           None [] [] None None ) ] ;
  (* Scalar mul commutes with tensor mul nesting:
     (f * g) * a = (f * a) * g *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; f; g]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_scalar_tensor
                 [a; Expr.mk_app ctx mul_tensor_tensor [f; g]] )
              (Expr.mk_app ctx mul_tensor_tensor
                 [Expr.mk_app ctx mul_scalar_tensor [a; f]; g] ) )
           None [] [] None None ) ] ;
  (* MulScalarTensor distributes over AddTensorTensor *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; f; g]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_scalar_tensor
                 [a; Expr.mk_app ctx add_tensor_tensor [f; g]] )
              (Expr.mk_app ctx add_tensor_tensor
                 [ Expr.mk_app ctx mul_scalar_tensor [a; f]
                 ; Expr.mk_app ctx mul_scalar_tensor [a; g] ] ) )
           None [] [] None None ) ] ;
  (* MulTensorTensor distributes over AddTensorTensor *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [f; g; h]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_tensor_tensor
                 [f; Expr.mk_app ctx add_tensor_tensor [g; h]] )
              (Expr.mk_app ctx add_tensor_tensor
                 [ Expr.mk_app ctx mul_tensor_tensor [f; g]
                 ; Expr.mk_app ctx mul_tensor_tensor [f; h] ] ) )
           None [] [] None None ) ] ;
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b; c]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_scalar_scalar
                 [Expr.mk_app ctx add_scalar_scalar [a; b]; c] )
              (Expr.mk_app ctx add_scalar_scalar
                 [ Expr.mk_app ctx mul_scalar_scalar [a; c]
                 ; Expr.mk_app ctx mul_scalar_scalar [b; c] ] ) )
           None [] [] None None ) ] ;
  (* Associativity: (a * b) * c = a * (b * c) *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b; c]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx mul_scalar_scalar
                 [Expr.mk_app ctx mul_scalar_scalar [a; b]; c] )
              (Expr.mk_app ctx mul_scalar_scalar
                 [a; Expr.mk_app ctx mul_scalar_scalar [b; c]] ) )
           None [] [] None None ) ] ;
  (* Associativity: (a + b) + c = a + (b + c) *)
  Solver.add solver
    [ Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [a; b; c]
           (Boolean.mk_eq ctx
              (Expr.mk_app ctx add_scalar_scalar
                 [Expr.mk_app ctx add_scalar_scalar [a; b]; c] )
              (Expr.mk_app ctx add_scalar_scalar
                 [a; Expr.mk_app ctx add_scalar_scalar [b; c]] ) )
           None [] [] None None ) ] ;
  List.iteri
    (fun _idx (axiom_lhs, axiom_rhs) ->
      let axiom_vars =
        declare_vars ctx int_sort tensor_sort axiom_lhs axiom_rhs
      in
      let axiom_lhs_expr =
        term_to_z3_expr ctx axiom_vars mul_tensor_tensor mul_scalar_tensor
          mul_scalar_scalar add_tensor_tensor add_scalar_tensor
          add_scalar_scalar r2 axiom_lhs
      in
      let axiom_rhs_expr =
        term_to_z3_expr ctx axiom_vars mul_tensor_tensor mul_scalar_tensor
          mul_scalar_scalar add_tensor_tensor add_scalar_tensor
          add_scalar_scalar r2 axiom_rhs
      in
      let axiom_var_list =
        Hashtbl.fold (fun _ v acc -> v :: acc) axiom_vars []
      in
      Solver.add solver
        [ Quantifier.expr_of_quantifier
            (Quantifier.mk_forall_const ctx axiom_var_list
               (Boolean.mk_eq ctx axiom_lhs_expr axiom_rhs_expr)
               None [] [] None None ) ] )
    proven_axioms ;
  (* Counterexample *)
  let cex_vars = Hashtbl.create (Hashtbl.length exp_vars) in
  Hashtbl.iter
    (fun name expr ->
      let sort = Expr.get_sort expr in
      let cex_name = name ^ "0" in
      let cex_const = Expr.mk_const ctx (Symbol.mk_string ctx cex_name) sort in
      Hashtbl.add cex_vars name cex_const )
    exp_vars ;
  let cex_lhs =
    term_to_z3_expr ctx cex_vars mul_tensor_tensor mul_scalar_tensor
      mul_scalar_scalar add_tensor_tensor add_scalar_tensor add_scalar_scalar r1
      lhs
  in
  let cex_rhs =
    term_to_z3_expr ctx cex_vars mul_tensor_tensor mul_scalar_tensor
      mul_scalar_scalar add_tensor_tensor add_scalar_tensor add_scalar_scalar r1
      rhs
  in
  Solver.add solver [Boolean.mk_not ctx (Boolean.mk_eq ctx cex_lhs cex_rhs)] ;
  (* Extract integer variables for bounds search *)
  let scalar_vars =
    Hashtbl.fold
      (fun k v acc ->
        if Sort.equal (Expr.get_sort v) int_sort then (k, v) :: acc else acc )
      cex_vars []
  in
  let initial_bounds =
    List.map
      (fun (name, _) ->
        ( name
        , {lower= None; lower_strict= false; upper= None; upper_strict= false}
        ) )
      scalar_vars
  in
  let queue = Queue.create () in
  Queue.add initial_bounds queue ;
  let check_axiom_for_var expr b_bound is_mul =
    let solver2 = Solver.mk_solver ctx None in
    let params2 = Params.mk_params ctx in
    Params.add_int params2 (Symbol.mk_string ctx "timeout") 1000 ;
    Solver.set_parameters solver2 params2 ;
    let at_var = Expr.mk_const ctx (Symbol.mk_string ctx "at") int_sort in
    let bt_var = Expr.mk_const ctx (Symbol.mk_string ctx "bt") int_sort in
    Solver.add solver2
      [ Quantifier.expr_of_quantifier
          (Quantifier.mk_forall_const ctx [a; b]
             (Boolean.mk_eq ctx
                (Expr.mk_app ctx add_scalar_scalar [a; b])
                (Arithmetic.mk_add ctx [a; b]) )
             None [] [] None None ) ] ;
    Solver.add solver2
      [ Quantifier.expr_of_quantifier
          (Quantifier.mk_forall_const ctx [a; b]
             (Boolean.mk_eq ctx
                (Expr.mk_app ctx mul_scalar_scalar [a; b])
                (Arithmetic.mk_mul ctx [a; b]) )
             None [] [] None None ) ] ;
    Solver.add solver2
      [ Quantifier.expr_of_quantifier
          (Quantifier.mk_forall_const ctx [a; b]
             (Boolean.mk_eq ctx
                (Expr.mk_app ctx operation [a; b])
                (z3_op ctx a b mul_scalar_scalar add_scalar_scalar) )
             None [] [] None None ) ] ;
    ( match b_bound.lower with
    | Some l ->
        let num = Expr.mk_numeral_int ctx l (Arithmetic.Real.mk_sort ctx) in
        if b_bound.lower_strict then
          Solver.add solver2 [Arithmetic.mk_gt ctx expr num]
        else Solver.add solver2 [Arithmetic.mk_ge ctx expr num]
    | None ->
        () ) ;
    ( match b_bound.upper with
    | Some u ->
        let num = Expr.mk_numeral_int ctx u (Arithmetic.Real.mk_sort ctx) in
        if b_bound.upper_strict then
          Solver.add solver2 [Arithmetic.mk_lt ctx expr num]
        else Solver.add solver2 [Arithmetic.mk_le ctx expr num]
    | None ->
        () ) ;
    let op_scalar = if is_mul then mul_scalar_scalar else add_scalar_scalar in
    Solver.add solver2
      [ Boolean.mk_not ctx
          (Boolean.mk_eq ctx
             (Expr.mk_app ctx operation
                [ Expr.mk_app ctx op_scalar [at_var; expr]
                ; Expr.mk_app ctx op_scalar [bt_var; expr] ] )
             (Expr.mk_app ctx op_scalar
                [Expr.mk_app ctx operation [at_var; bt_var]; expr] ) ) ] ;
    match Solver.check solver2 [] with
    | Solver.UNSATISFIABLE ->
        true
    | _ ->
        false
  in
  let rec cegis_loop attempts =
    if verbose then
      Printf.printf "Attempt %d, queue size %d\n%!" attempts
        (Queue.length queue) ;
    if attempts > 20 then (false, [])
    else if Queue.is_empty queue then (false, [])
    else begin
      let bounds = Queue.pop queue in
      Solver.push solver ;
      if use_inductive_hypothesis && same_vars then begin
        let conds =
          Hashtbl.fold
            (fun name v acc ->
              if Sort.equal (Expr.get_sort v) int_sort then
                match List.assoc_opt name bounds with
                | Some b_bound ->
                    let c = ref [] in
                    ( match b_bound.lower with
                    | Some l ->
                        let num =
                          Expr.mk_numeral_int ctx l
                            (Arithmetic.Real.mk_sort ctx)
                        in
                        if b_bound.lower_strict then
                          c := Arithmetic.mk_gt ctx v num :: !c
                        else c := Arithmetic.mk_ge ctx v num :: !c
                    | None ->
                        () ) ;
                    ( match b_bound.upper with
                    | Some u ->
                        let num =
                          Expr.mk_numeral_int ctx u
                            (Arithmetic.Real.mk_sort ctx)
                        in
                        if b_bound.upper_strict then
                          c := Arithmetic.mk_lt ctx v num :: !c
                        else c := Arithmetic.mk_le ctx v num :: !c
                    | None ->
                        () ) ;
                    !c @ acc
                | None ->
                    acc
              else acc )
            exp_vars []
        in
        let hyp_body =
          if conds = [] then Boolean.mk_eq ctx hyp_lhs hyp_rhs
          else
            Boolean.mk_implies ctx (Boolean.mk_and ctx conds)
              (Boolean.mk_eq ctx hyp_lhs hyp_rhs)
        in
        Solver.add solver
          [ Quantifier.expr_of_quantifier
              (Quantifier.mk_forall_const ctx var_list hyp_body None [] [] None
                 None ) ]
      end ;
      List.iter
        (fun (name, b_bound) ->
          let expr = List.assoc name scalar_vars in
          ( match b_bound.lower with
          | Some l ->
              let num =
                Expr.mk_numeral_int ctx l (Arithmetic.Real.mk_sort ctx)
              in
              if b_bound.lower_strict then
                Solver.add solver [Arithmetic.mk_gt ctx expr num]
              else Solver.add solver [Arithmetic.mk_ge ctx expr num]
          | None ->
              () ) ;
          ( match b_bound.upper with
          | Some u ->
              let num =
                Expr.mk_numeral_int ctx u (Arithmetic.Real.mk_sort ctx)
              in
              if b_bound.upper_strict then
                Solver.add solver [Arithmetic.mk_lt ctx expr num]
              else Solver.add solver [Arithmetic.mk_le ctx expr num]
          | None ->
              () ) ;
          if check_axiom_for_var expr b_bound true then
            Solver.add solver
              [ Quantifier.expr_of_quantifier
                  (Quantifier.mk_forall_const ctx [a; b]
                     (Boolean.mk_eq ctx
                        (Expr.mk_app ctx operation
                           [ Expr.mk_app ctx mul_scalar_scalar [a; expr]
                           ; Expr.mk_app ctx mul_scalar_scalar [b; expr] ] )
                        (Expr.mk_app ctx mul_scalar_scalar
                           [Expr.mk_app ctx operation [a; b]; expr] ) )
                     None [] [] None None ) ] ;
          if check_axiom_for_var expr b_bound false then
            Solver.add solver
              [ Quantifier.expr_of_quantifier
                  (Quantifier.mk_forall_const ctx [a; b]
                     (Boolean.mk_eq ctx
                        (Expr.mk_app ctx operation
                           [ Expr.mk_app ctx add_scalar_scalar [a; expr]
                           ; Expr.mk_app ctx add_scalar_scalar [b; expr] ] )
                        (Expr.mk_app ctx add_scalar_scalar
                           [Expr.mk_app ctx operation [a; b]; expr] ) )
                     None [] [] None None ) ] )
        bounds ;
      let res = Solver.check solver [] in
      let branch_on_counterexample env bounds =
        List.iter
          (fun (name, v) ->
            let b = List.assoc name bounds in
            let valid_lower =
              b.lower = None
              ||
              if b.lower_strict then Option.get b.lower < v
              else Option.get b.lower <= v
            in
            let valid_upper =
              b.upper = None
              ||
              if b.upper_strict then Option.get b.upper > v
              else Option.get b.upper >= v
            in
            if valid_lower && valid_upper then begin
              let b1 = {b with lower= Some v; lower_strict= true} in
              let b2 = {b with upper= Some v; upper_strict= true} in
              if is_valid b1 then
                Queue.add
                  (List.map
                     (fun (n, old_b) -> if n = name then (n, b1) else (n, old_b))
                     bounds )
                  queue ;
              if is_valid b2 then
                Queue.add
                  (List.map
                     (fun (n, old_b) -> if n = name then (n, b2) else (n, old_b))
                     bounds )
                  queue
            end )
          env
      in
      let split_unknown bounds =
        let split_var =
          List.find_opt (fun (_, b) -> b.lower = None && b.upper = None) bounds
        in
        match split_var with
        | Some (name, b) ->
            let b1 = {b with lower= Some 0; lower_strict= true} in
            let b2 =
              { upper= Some 0
              ; lower= Some 0
              ; upper_strict= false
              ; lower_strict= false }
            in
            let b3 = {b with upper= Some 0; upper_strict= true} in
            if is_valid b1 then
              Queue.add
                (List.map
                   (fun (n, old_b) -> if n = name then (n, b1) else (n, old_b))
                   bounds )
                queue ;
            if is_valid b2 then
              Queue.add
                (List.map
                   (fun (n, old_b) -> if n = name then (n, b2) else (n, old_b))
                   bounds )
                queue ;
            if is_valid b3 then
              Queue.add
                (List.map
                   (fun (n, old_b) -> if n = name then (n, b3) else (n, old_b))
                   bounds )
                queue
        | None ->
            ()
      in
      match res with
      | Solver.UNSATISFIABLE -> (
          Solver.pop solver 1 ;
          match check_index bounds with
          | Proven ->
              if verbose then
                print_endline
                  ("PROVEN universally with bounds: " ^ print_bounds bounds) ;
              (true, bounds)
          | Counterexample env ->
              if verbose then
                print_endline
                  ( "SAT (Index Counterexample) with bounds: "
                  ^ print_bounds bounds ) ;
              branch_on_counterexample env bounds ;
              cegis_loop (attempts + 1)
          | Unknown ->
              if verbose then
                print_endline
                  ("UNKNOWN index with bounds: " ^ print_bounds bounds) ;
              split_unknown bounds ;
              cegis_loop (attempts + 1) )
      | Solver.SATISFIABLE ->
          if verbose then
            print_endline
              ("SAT (Value Counterexample) with bounds: " ^ print_bounds bounds) ;
          let model = Option.get (Solver.get_model solver) in
          Solver.pop solver 1 ;
          let env =
            List.filter_map
              (fun (name, expr) ->
                match Model.eval model expr true with
                | Some v_expr -> (
                    let s = Expr.to_string v_expr in
                    let s_clean =
                      if String.length s > 0 && s.[0] = '(' then
                        let inner = String.sub s 1 (String.length s - 2) in
                        match String.split_on_char ' ' inner with
                        | ["-"; n] ->
                            "-" ^ n
                        | _ ->
                            inner
                      else s
                    in
                    try Some (name, int_of_string s_clean) with _ -> None )
                | None ->
                    None )
              scalar_vars
          in
          branch_on_counterexample env bounds ;
          cegis_loop (attempts + 1)
      | Solver.UNKNOWN ->
          if verbose then
            print_endline ("UNKNOWN with bounds: " ^ print_bounds bounds) ;
          Solver.pop solver 1 ;
          split_unknown bounds ;
          cegis_loop (attempts + 1)
    end
  in
  if verbose then begin
    print_endline (Solver.to_string solver) ;
    print_endline "---------" ;
    print_endline (term_to_s lhs) ;
    print_endline (term_to_s rhs)
  end ;
  cegis_loop 0
