open Printf
open Z3
open Axiomatization.Parser
open Axiomatization.Term
open Axiomatization.Verify
open Axiomatization.Verify_index

(*
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
*)

let hlo_comparator1 =
  {|
  %region_0.2 (Arg_0.3: f32[], Arg_1.4: s32[], Arg_2.5: f32[], Arg_3.6: s32[]) -> (f32[], s32[]) {
    %Arg_0.3 = f32[] parameter(0)
    %Arg_2.5 = f32[] parameter(2)
    %compare.7 = pred[] compare(%Arg_0.3, %Arg_2.5), direction=GT
    %compare.8 = pred[] compare(%Arg_0.3, %Arg_0.3), direction=NE
    %or.9 = pred[] or(%compare.7, %compare.8)
    %select.14 = f32[] select(%or.9, %Arg_0.3, %Arg_2.5)
    %compare.10 = pred[] compare(%Arg_0.3, %Arg_2.5), direction=EQ
    %Arg_1.4 = s32[] parameter(1)
    %Arg_3.6 = s32[] parameter(3)
    %compare.11 = pred[] compare(%Arg_1.4, %Arg_3.6), direction=LT
    %and.12 = pred[] and(%compare.10, %compare.11)
    %or.13 = pred[] or(%or.9, %and.12)
    %select.15 = s32[] select(%or.13, %Arg_1.4, %Arg_3.6)
    ROOT %tuple.16 = (f32[], s32[]) tuple(%select.14, %select.15)
  }
|}

let hlo_comparator2 =
  {|
  %region_0.2 (Arg_0.3: pred[], Arg_1.4: s32[], Arg_2.5: pred[], Arg_3.6: s32[]) -> (pred[], s32[]) {
    %Arg_0.3 = pred[] parameter(0)
    %Arg_2.5 = pred[] parameter(2)
    %compare.7 = pred[] compare(%Arg_0.3, %Arg_2.5), direction=LT
    %select.12 = pred[] select(%compare.7, %Arg_0.3, %Arg_2.5)
    %compare.8 = pred[] compare(%Arg_0.3, %Arg_2.5), direction=EQ
    %Arg_1.4 = s32[] parameter(1)
    %Arg_3.6 = s32[] parameter(3)
    %compare.9 = pred[] compare(%Arg_1.4, %Arg_3.6), direction=LT
    %and.10 = pred[] and(%compare.8, %compare.9)
    %or.11 = pred[] or(%compare.7, %and.10)
    %select.13 = s32[] select(%or.11, %Arg_1.4, %Arg_3.6)
    ROOT %tuple.14 = (pred[], s32[]) tuple(%select.12, %select.13)
  }
|}

let () =
  let c = Var "c" in
  let d = Var "d" in
  let t = Tensor "T" in
  let op_max = max in
  let lhs = Mult (d, Mult (c, Reduction ("X", op_max, t))) in
  let rhs = Add (c, Reduction ("X", op_max, Mult (d, t))) in
  printf "Candidate Theorem: %s == %s\n" (term_to_s lhs) (term_to_s rhs) ;
  printf "========================================\n" ;
  printf "Verifying argmax reduction...\n" ;
  let hlo_comparator ctx v0 i0 v1 i1 =
    let root = translate_comparator ctx [v0; i0; v1; i1] hlo_comparator2 in
    (List.nth root 0, List.nth root 1)
  in
  let check_index bounds =
    verify_index_step bounds lhs rhs (fun ctx v0 i0 v1 i1 ->
        snd (hlo_comparator ctx v0 i0 v1 i1) )
  in
  let value_proven, value_bounds =
    verify ~use_inductive_hypothesis:true lhs rhs ~check_index ~verbose:true
      (fun ctx v0 v1 _ _ ->
        fst
          (hlo_comparator ctx v0
             (Arithmetic.Integer.mk_numeral_i ctx 0)
             v1
             (Arithmetic.Integer.mk_numeral_i ctx 1) ) )
      []
  in
  if value_proven then
    printf
      "Result: Theorem is fully PROVEN for Argmax tuple reduction! Bounds: %s\n"
      (print_bounds value_bounds)
  else printf "Result: Theorem is NOT PROVEN.\n"
