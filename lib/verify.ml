open Term
open Z3

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

let verify ?(use_inductive_hypothesis = true) ?(verbose = false) lhs rhs z3_op
    proven_axioms =
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
  if use_inductive_hypothesis && same_vars then
    Solver.add solver
      [ Quantifier.expr_of_quantifier
          (Quantifier.mk_forall_const ctx var_list
             (Boolean.mk_eq ctx hyp_lhs hyp_rhs)
             None [] [] None None ) ] ;
  (* E homomorphism over addition *)
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
  (* Check *)
  if verbose then begin
    print_endline (Solver.to_string solver) ;
    print_endline "---------" ;
    print_endline (term_to_s lhs) ;
    print_endline (term_to_s rhs)
  end ;
  match Solver.check solver [] with
  | Solver.SATISFIABLE ->
      if verbose then print_endline "SAT" ;
      false
  | Solver.UNSATISFIABLE ->
      if verbose then print_endline "UNSAT" ;
      true
  | Solver.UNKNOWN ->
      if verbose then print_endline "UNKNOWN" ;
      false
