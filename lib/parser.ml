open Z3

type hlo_sort = F32 | S32 | Pred

type hlo_op =
  | Parameter of int
  | Compare of string * string * string
  | And of string * string
  | Or of string * string
  | Not of string
  | Select of string * string * string
  | Tuple of string list

type instr = {name: string; sort: hlo_sort option; op: hlo_op; is_root: bool}

let strip s = String.trim s

let strip_pct s =
  let s = strip s in
  if s <> "" && s.[0] = '%' then String.sub s 1 (String.length s - 1) else s

let parse_sort = function
  | "f32[]" ->
      Some F32
  | "s32[]" ->
      Some S32
  | "pred[]" ->
      Some Pred
  | _ ->
      None

let between_parens s =
  match (String.index_opt s '(', String.rindex_opt s ')') with
  | Some i, Some j when j > i ->
      String.sub s (i + 1) (j - i - 1)
  | _ ->
      ""

let split_args s =
  let buf = Buffer.create 16 in
  let depth = ref 0 in
  let args = ref [] in
  String.iter
    (fun c ->
      match c with
      | '(' ->
          incr depth ; Buffer.add_char buf c
      | ')' ->
          decr depth ; Buffer.add_char buf c
      | ',' when !depth = 0 ->
          args := strip_pct (Buffer.contents buf) :: !args ;
          Buffer.clear buf
      | _ ->
          Buffer.add_char buf c )
    s ;
  let last = strip_pct (Buffer.contents buf) in
  if last <> "" then args := last :: !args ;
  List.rev !args

let find_direction s =
  match String.rindex_opt s ')' with
  | None ->
      None
  | Some j ->
      String.sub s (j + 1) (String.length s - j - 1)
      |> String.split_on_char ','
      |> List.find_map (fun part ->
          let p = strip part in
          let prefix = "direction=" in
          let plen = String.length prefix in
          if String.length p >= plen && String.sub p 0 plen = prefix then
            Some (String.sub p plen (String.length p - plen))
          else None )

(* split "f32[] compare(...)" or "(f32[], s32[]) tuple(...)" into (sort, op_string) *)
let split_type_and_op rest =
  let rest = strip rest in
  if rest <> "" && rest.[0] = '(' then
    match String.index_opt rest ')' with
    | None ->
        (None, rest)
    | Some j ->
        let op_str =
          strip (String.sub rest (j + 1) (String.length rest - j - 1))
        in
        (None, op_str)
  else
    match String.index_opt rest ' ' with
    | None ->
        (None, rest)
    | Some k ->
        let sort = parse_sort (String.sub rest 0 k) in
        let op_str =
          strip (String.sub rest (k + 1) (String.length rest - k - 1))
        in
        (sort, op_str)

let parse_instr line =
  let line = strip line in
  if line = "" || line.[0] = '{' || line.[0] = '}' then None
  else
    let is_root = String.length line >= 4 && String.sub line 0 4 = "ROOT" in
    let line =
      if is_root then strip (String.sub line 4 (String.length line - 4))
      else line
    in
    match String.index_opt line '=' with
    | None ->
        None
    | Some eq ->
        let name = strip_pct (String.sub line 0 eq) in
        let rest =
          strip (String.sub line (eq + 1) (String.length line - eq - 1))
        in
        let sort, op_str = split_type_and_op rest in
        let op_name =
          match String.index_opt op_str '(' with
          | Some i ->
              strip (String.sub op_str 0 i)
          | None ->
              op_str
        in
        let args = split_args (between_parens op_str) in
        let dir = find_direction op_str in
        let op =
          match op_name with
          | "parameter" -> (
            match args with
            | [n] ->
                Some (Parameter (int_of_string n))
            | _ ->
                None )
          | "compare" -> (
            match (args, dir) with
            | [a; b], Some d ->
                Some (Compare (a, b, d))
            | _ ->
                None )
          | "and" -> (
            match args with [a; b] -> Some (And (a, b)) | _ -> None )
          | "or" -> (
            match args with [a; b] -> Some (Or (a, b)) | _ -> None )
          | "not" -> (
            match args with [a] -> Some (Not a) | _ -> None )
          | "select" -> (
            match args with [c; t; f] -> Some (Select (c, t, f)) | _ -> None )
          | "tuple" ->
              Some (Tuple args)
          | _ ->
              None
        in
        Option.map (fun op -> {name; sort; op; is_root}) op

let hlo_sort_to_z3 ctx = function
  | F32 ->
      Arithmetic.Real.mk_sort ctx
  | S32 ->
      Arithmetic.Integer.mk_sort ctx
  | Pred ->
      Boolean.mk_sort ctx

let parse_params_from_sig line =
  let inner = between_parens line in
  String.split_on_char ',' inner
  |> List.filter_map (fun part ->
      match String.split_on_char ':' part with
      | [name; typ] ->
          let name = strip_pct name in
          let sort = parse_sort (strip typ) in
          Option.map (fun s -> (name, s)) sort
      | _ ->
          None )

let translate_comparator ctx param_exprs hlo_text =
  let env : (string, Expr.expr) Hashtbl.t = Hashtbl.create 16 in
  let lookup name =
    match Hashtbl.find_opt env name with
    | Some e ->
        e
    | None ->
        failwith ("Unbound HLO variable: %" ^ name)
  in
  let root = ref [] in
  String.split_on_char '\n' hlo_text
  |> List.filter_map parse_instr
  |> List.iter (fun instr ->
      let bind e = Hashtbl.add env instr.name e in
      match instr.op with
      | Parameter n ->
          bind (List.nth param_exprs n)
      | Compare (a, b, dir) ->
          let l = lookup a and r = lookup b in
          bind
            ( match dir with
            | "GT" ->
                Arithmetic.mk_gt ctx l r
            | "LT" ->
                Arithmetic.mk_lt ctx l r
            | "GE" ->
                Arithmetic.mk_ge ctx l r
            | "LE" ->
                Arithmetic.mk_le ctx l r
            | "EQ" ->
                Boolean.mk_eq ctx l r
            | "NE" ->
                Boolean.mk_not ctx (Boolean.mk_eq ctx l r)
            | d ->
                failwith ("Unknown compare direction: " ^ d) )
      | And (a, b) ->
          bind (Boolean.mk_and ctx [lookup a; lookup b])
      | Or (a, b) ->
          bind (Boolean.mk_or ctx [lookup a; lookup b])
      | Not a ->
          bind (Boolean.mk_not ctx (lookup a))
      | Select (c, t, f) ->
          bind (Boolean.mk_ite ctx (lookup c) (lookup t) (lookup f))
      | Tuple ops when instr.is_root ->
          root := List.map lookup ops
      | Tuple _ ->
          () ) ;
  !root

type hlo_val = VFloat of float | VInt of int | VBool of bool

let compile_hlo hlo_text =
  let instrs =
    String.split_on_char '\n' hlo_text |> List.filter_map parse_instr
  in
  fun params ->
    let env = Hashtbl.create 16 in
    let lookup name = Hashtbl.find env name in
    let root = ref [] in
    List.iter
      (fun instr ->
        let res =
          match instr.op with
          | Parameter n ->
              List.nth params n
          | Compare (a, b, dir) -> (
              let l = lookup a and r = lookup b in
              match (l, r) with
              | VFloat fl, VFloat fr ->
                  VBool
                    ( match dir with
                    | "GT" ->
                        fl > fr
                    | "LT" ->
                        fl < fr
                    | "GE" ->
                        fl >= fr
                    | "LE" ->
                        fl <= fr
                    | "EQ" ->
                        fl = fr
                    | "NE" ->
                        fl <> fr
                    | _ ->
                        failwith "dir" )
              | VInt il, VInt ir ->
                  VBool
                    ( match dir with
                    | "GT" ->
                        il > ir
                    | "LT" ->
                        il < ir
                    | "GE" ->
                        il >= ir
                    | "LE" ->
                        il <= ir
                    | "EQ" ->
                        il = ir
                    | "NE" ->
                        il <> ir
                    | _ ->
                        failwith "dir" )
              | VBool bl, VBool br ->
                  VBool
                    ( match dir with
                    | "EQ" ->
                        bl = br
                    | "NE" ->
                        bl <> br
                    | _ ->
                        failwith "dir" )
              | _ ->
                  failwith "type mismatch in compare" )
          | And (a, b) -> (
            match (lookup a, lookup b) with
            | VBool al, VBool bl ->
                VBool (al && bl)
            | _ ->
                failwith "type mismatch in and" )
          | Or (a, b) -> (
            match (lookup a, lookup b) with
            | VBool al, VBool bl ->
                VBool (al || bl)
            | _ ->
                failwith "type mismatch in or" )
          | Not a -> (
            match lookup a with
            | VBool al ->
                VBool (not al)
            | _ ->
                failwith "type mismatch in not" )
          | Select (c, t, f) -> (
            match lookup c with
            | VBool cond ->
                if cond then lookup t else lookup f
            | _ ->
                failwith "type mismatch in select" )
          | Tuple ops ->
              if instr.is_root then root := List.map lookup ops ;
              VBool false (* dummy *)
        in
        Hashtbl.add env instr.name res )
      instrs ;
    !root
