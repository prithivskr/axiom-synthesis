open Term

let latex_escape s =
  let b = Buffer.create (String.length s) in
  String.iter
    (fun c ->
      match c with
      | '_' ->
          Buffer.add_string b "\\_"
      | '^' ->
          Buffer.add_string b "\\^{}"
      | '\\' ->
          Buffer.add_string b "\\textbackslash{}"
      | '{' ->
          Buffer.add_string b "\\{"
      | '}' ->
          Buffer.add_string b "\\}"
      | '&' ->
          Buffer.add_string b "\\&"
      | '%' ->
          Buffer.add_string b "\\%"
      | '$' ->
          Buffer.add_string b "\\$"
      | '#' ->
          Buffer.add_string b "\\#"
      | '~' ->
          Buffer.add_string b "\\~{}"
      | c ->
          Buffer.add_char b c )
    s ;
  Buffer.contents b

let rec term_to_latex ?(reduction_symbol = "\\bigoplus") term =
  match term with
  | Var x ->
      latex_escape x
  | Tensor x ->
      latex_escape x
  | Add (a, b) ->
      let la = term_to_latex ~reduction_symbol a in
      let lb = term_to_latex ~reduction_symbol b in
      Printf.sprintf "%s + %s" la lb
  | Mult (a, b) ->
      let la = term_to_latex ~reduction_symbol a in
      let lb = term_to_latex ~reduction_symbol b in
      let paren_if_add s =
        if String.contains s '+' then Printf.sprintf "(%s)" s else s
      in
      Printf.sprintf "%s * %s" (paren_if_add la) (paren_if_add lb)
  | Reduction (axis, _op, inner) ->
      let inner_l = term_to_latex ~reduction_symbol inner in
      Printf.sprintf "%s_{%s}\\left(%s\\right)" reduction_symbol
        (latex_escape axis) inner_l

let eq_to_latex_math ?(reduction_symbol = "\\operatorname{Red}^+") t1 t2 =
  Printf.sprintf "\\[%s \\rightarrow %s\\]"
    (term_to_latex ~reduction_symbol t1)
    (term_to_latex ~reduction_symbol t2)

let pair_key a b =
  let sa = term_to_s a in
  let sb = term_to_s b in
  if sa <= sb then sa ^ " == " ^ sb else sb ^ " == " ^ sa
