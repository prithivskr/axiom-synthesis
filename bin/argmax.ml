open Printf
open Z3
open Axiomatization.Term
open Axiomatization.Verify
open Axiomatization.Verify_index

let z3_argmax ctx v0 i0 v1 i1 =
  let v_gt = Arithmetic.mk_gt ctx v0 v1 in
  let v_lt = Arithmetic.mk_lt ctx v0 v1 in
  let i_lt = Arithmetic.mk_lt ctx i0 i1 in
  let res_v = Boolean.mk_ite ctx (Arithmetic.mk_ge ctx v0 v1) v0 v1 in
  let res_i =
    Boolean.mk_ite ctx v_gt i0
      (Boolean.mk_ite ctx v_lt i1 (Boolean.mk_ite ctx i_lt i0 i1))
  in
  (res_v, res_i)

let () =
  let c = Var "c" in
  let t = Tensor "T" in
  let op_max = max in
  let lhs = Mult (c, Reduction ("X", op_max, t)) in
  let rhs = Reduction ("X", op_max, Mult (c, t)) in
  printf "Candidate Theorem: %s == %s\n" (term_to_s lhs) (term_to_s rhs) ;
  printf "========================================\n" ;
  printf "Verifying argmax reduction...\n" ;
  let value_proven =
    verify ~use_inductive_hypothesis:true lhs rhs
      (fun ctx v0 v1 _ _ ->
        fst
          (z3_argmax ctx v0
             (Arithmetic.Integer.mk_numeral_i ctx 0)
             v1
             (Arithmetic.Integer.mk_numeral_i ctx 1) ) )
      []
  in
  if value_proven then print_endline "SAT" else print_endline "UNSAT" ;
  printf "----------------------------------------\n" ;
  let index_proven =
    verify_index lhs rhs (fun ctx v0 i0 v1 i1 ->
        snd (z3_argmax ctx v0 i0 v1 i1) )
  in
  printf "========================================\n" ;
  if value_proven && index_proven then
    printf "Result: Theorem is fully PROVEN for Argmax tuple reduction!\n"
  else printf "Result: Theorem is NOT PROVEN.\n"
