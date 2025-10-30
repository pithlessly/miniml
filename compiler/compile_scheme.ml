open Util
open Common_syntax
open Core

let go_char c =
  let code = int_of_char c in
  if 32 < code && code < 128 then
    "#\\" ^ String.make 1 c
  else if c = ' ' then
    "#\\space"
  else if c = '\n' then
    "#\\newline"
  else if c = '\r' then
    "(integer->char 13)"
  else
    invalid_arg ("we don't yet support this character code: " ^ string_of_int code)
and go_int = string_of_int
and go_str s =
  let rec go acc i =
    if i < 0 then String.concat "" ("\"" :: acc) else
    let c = match String.get s i with
            | '"'  -> "\\\""
            | '\\' -> "\\\\"
            | '\n' -> "\\n"
            | '\r' -> "\\r"
            | c    -> let code = int_of_char c in
                      if 32 <= code && code < 128 then
                        String.make 1 c
                      else
                        invalid_arg ("we don't yet support this character code: "
                                    ^ string_of_int code)
    in go (c :: acc) (i - 1)
  in go ["\""] (String.length s - 1)

let safe_in_scheme_identifiers = function
  | '|'
  | '\'' -> false
  | _    -> true

let go_var ({ name; id; provenance; _ } : var) =
  match provenance with
  | User ->
    (* TODO: don't recompute this every time we have to compile a variable *)
    "v" ^ String.filter safe_in_scheme_identifiers name ^ "-" ^ string_of_int id
  | Builtin prefix ->
    match name with
    | "|>" -> "miniml-ap"
    | "||" -> "miniml-or"
    | ";"  -> "miniml-semicolon"
    | "::" -> "miniml-cons"
    | _    -> "miniml-" ^ prefix ^ name

let go_cvar ({ provenance; name; id; _ } : cvar) =
  match (provenance, name) with
  (* TODO: avoid special casing these constructors *)
  | (Builtin "StringMap.", "DupErr")
  | (Builtin "", ("Error" | "Ok")) -> "'" ^ name
  | (User, _) -> "'" ^ name ^ string_of_int id
  | _ -> invalid_arg "builtin constructors are handled specially"

let scheme (_ : Elab.elaborator) (decls : core) =
  let result = ref [] in
  let emit s = result := (s :: deref result) in
  let tmp_var =
    let next_id = counter () in
    fun () -> ("t" ^ string_of_int (next_id ()))
  in
  let indent = ref 0 in
  let indent n f =
    let old = deref indent in
    indent := old + n;
    let result = f () in
    indent := old;
    result
  and emit_ln s = emit (String.make (deref indent) ' ' ^ s ^ "\n")
  in
  let sequence expr =
    let v = tmp_var () in
    emit_ln ("(define " ^ v ^ " " ^ expr ^ ")");
    v
  in
  let rec go_pat : pat -> string =
    (* TODO: a lot of opportunities to generate more sensible/idiomatic code here *)
    function
    | POr (p1, p2) -> "(or " ^ go_pat p1 ^ " " ^ go_pat p2 ^ ")"
    | PTuple [] -> "#t"
    | PTuple ps -> "(and" ^ (String.concat ""
                     (List.mapi
                       (fun idx p ->
                         " (let ((scrutinee (vector-ref scrutinee " ^ string_of_int idx ^ "))) "
                         ^ go_pat p ^ ")") ps)) ^ ")"
    | PList [] -> "(null? scrutinee)"
    | PList (p :: ps) ->
      "(and (pair? scrutinee) " ^
          " (let ((scrutinee (car scrutinee))) " ^ go_pat p          ^ ")" ^
          " (let ((scrutinee (cdr scrutinee))) " ^ go_pat (PList ps) ^ "))"
    | PCon (cv, ps) ->
      let ps = Option.unwrap ps in
      let vector_layout () =
        match ps with
        | [] -> "(eq? scrutinee " ^ go_cvar cv ^ ")"
        | _ ->
          "(and (vector? scrutinee) (eq? (vector-ref scrutinee 0) " ^ go_cvar cv ^ ")" ^ (String.concat ""
            (List.mapi
              (fun idx p ->
                " (let ((scrutinee (vector-ref scrutinee " ^ string_of_int (idx + 1) ^ "))) "
                ^ go_pat p ^ ")") ps)) ^ ")"
      in (
      match cv.provenance with
      | User -> vector_layout ()
      | Builtin _ ->
        match (cv.name, ps) with
        | ("true",  []) -> "scrutinee"
        | ("false", []) -> "(not scrutinee)"
        | ("::", [p1; p2]) ->
          "(and (pair? scrutinee)" ^
              " (let ((scrutinee (car scrutinee))) " ^
                  go_pat p1 ^ ")" ^
              " (let ((scrutinee (cdr scrutinee))) " ^
                  go_pat p2 ^ "))"
        | ("None", [])  -> "(null? scrutinee)"
        | ("Some", [p]) -> "(and (pair? scrutinee)" ^
                               " (let ((scrutinee (car scrutinee))) " ^
                                   go_pat p ^ "))"
        (* TODO: DupErr could use newtype layout *)
        | (("Ok" | "Error" | "DupErr"), _) -> vector_layout ()
        | (_, ps) -> invalid_arg ("unsupported builtin constructor: " ^ cv.name ^ "/"
                           ^ string_of_int (List.length ps)))
    | PCharLit c -> "(char=? scrutinee " ^ go_char c ^ ")"
    | PIntLit i -> "(= scrutinee " ^ go_int i ^ ")"
    | PStrLit s -> "(string=? scrutinee " ^ go_str s ^ ")"
    | PVar v -> "(begin (set! " ^ go_var v ^ " scrutinee) #t)"
    | POpenIn (_, _) -> invalid_arg "POpenIn should no longer be present in Core.pat"
    | PAsc (_, vd) -> Void.absurd vd
    | PRecord (_, fields) ->
      "(and " ^ String.concat " "
        (List.map (fun ((fld : field), p) ->
          "(let ((scrutinee (vector-ref scrutinee " ^ string_of_int fld.position ^ "))) "
          ^ go_pat p ^ ")") fields) ^ ")"
    | PWild -> "#t"
  in
  let rec go_expr : expr -> bool * string =
    function
    | Tuple [] ->
      (true, "'()")
    | Tuple es ->
      (true, "(vector " ^ (String.concat " " (List.map go_expr_pure es)) ^ ")")
    | List es ->
      (true,
        List.fold_right (fun e acc -> "(cons " ^ e ^ " " ^ acc ^ ")")
          (List.map go_expr_pure es) "'()")
    | Con (cv, es) ->
      let es = Option.unwrap es in
      let vector_layout () =
        (true,
          match es with
          | [] -> go_cvar cv
          | _ ->
            "(vector " ^ go_cvar cv ^ (String.concat ""
              (List.map (fun e -> " " ^ go_expr_pure e) es)) ^ ")")
      in (
      match cv.provenance with
      | User -> vector_layout ()
      | Builtin _ ->
        match (cv.name, es) with
        | ("true",  [])  -> (true, "#t")
        | ("false", [])  -> (true, "#f")
        | ("None",  [])  -> (true, "'()")
        | ("Some",  [e]) -> (true, "(list " ^ go_expr_pure e ^ ")")
        (* TODO: DupErr could use newtype layout *)
        | (("Ok" | "Error" | "DupErr"), _) -> vector_layout ()
        | (_, es) -> invalid_arg ("unsupported builtin constructor: " ^ cv.name ^ "/"
                           ^ string_of_int (List.length es)))
    | CharLit c -> (true, go_char c)
    | IntLit i -> (true, go_int i)
    | StrLit s -> (true, go_str s)
    | Var v -> (true, go_var v)
    | OpenIn (_, _) ->
      invalid_arg "OpenIn should no longer be present in Core.expr"
    | Project (e, field) ->
      let (p, e') = go_expr e in
      (p, "(vector-ref " ^ e' ^ " " ^ string_of_int field.position ^ ")")
    | MkRecord fields ->
      (* perform side effects in declaration order *)
      let fields = List.map (fun (fld, rhs) -> (fld, go_expr_pure rhs)) fields in
      (* but then, sort the fields by their index *)
      let fields = list_sort (fun ({ position = p1; _ }, _) ({ position = p2; _ }, _) -> p1 - p2)
                             fields
      in
      (* and now we can forget about field order *)
      let fields = List.map snd fields in
      (true, "(vector " ^ String.concat " " fields ^ ")")
    | App (e1, e2) ->
      (false, (
        let (p1, e1') = go_expr e1 in
        if p1 then
          let e2' = go_expr_impure e2 in
          "(" ^ e1' ^ " " ^ e2' ^ ")"
        else
          let e1' = sequence e1' in
          let e2' = go_expr_impure e2 in
          "(" ^ e1' ^ " " ^ e2' ^ ")"
      ))
    | LetIn (bs, e) ->
      bindings bs;
      go_expr e
    | Match (scrutinee, branches) ->
      (
        let locals = List.concat_map (fun (p, _) -> Elab.pat_local_vars p) branches in
        emit_ln (String.concat " " (List.map (fun v -> "(define " ^ go_var v ^ " '())") locals))
      );
      let scrutinee' = go_expr_impure scrutinee in
      let tv = tmp_var () in
      emit_ln ("(define " ^ tv ^ " (let ((scrutinee " ^ scrutinee' ^ "))");
      indent 2 (fun () ->
        emit_ln "(cond";
        let last_is_t = ref false in
        branches |> List.iter (fun (pat, e) ->
          let pat' = go_pat pat in
          last_is_t := (pat' = "#t");
          emit_ln (" (" ^ go_pat pat);
          emit_ln ("  (let ()");
          indent 4 (fun () -> emit_ln (go_expr_impure e ^ "))"))
        );
        emit_ln (if deref last_is_t then " )))"
                                    else " (else (miniml-match-failure)))))"));
      (true, tv)
    | IfThenElse (e_cond, e_then, e_else) ->
      let e_cond' = go_expr_impure e_cond in
      let tv = tmp_var () in
      emit_ln ("(define " ^ tv ^ " (if " ^ e_cond');
      indent 2 (fun () ->
        emit_ln "(let ()";
        indent 2 (fun () -> emit_ln (go_expr_impure e_then ^ ")"));
        emit_ln "(let ()";
        indent 2 (fun () -> emit_ln (go_expr_impure e_else ^ ")))"))
      );
      (true, tv)
    | Fun ([], body) ->
      go_expr body
    | Fun ([arg], body) ->
      let tv = tmp_var () in
      emit_ln ("(define " ^ tv ^ " (lambda (scrutinee)");
      indent 2 (fun () ->
        let locals = Elab.pat_local_vars arg in
        emit_ln (String.concat " " (List.map (fun v -> "(define " ^ go_var v ^ " '())") locals));
        emit_ln ("(miniml-fun-guard " ^ go_pat arg ^ ")");
        emit_ln (go_expr_impure body ^ "))")
      );
      (true, tv)
    | Fun (arg :: args, body) ->
      go_expr (Fun ([arg], Fun (args, body)))
    | Function _ ->
      invalid_arg "Function should no longer be present in Core.expr"
  and go_expr_pure : expr -> string =
    fun e ->
    match go_expr e with
    | (true, e) -> e
    | (false, e) -> sequence e
  and go_expr_impure : expr -> string =
    fun e -> snd (go_expr e)
  and bindings (Bindings (_, bs)) =
    (* TODO: if the bindings aren't recursive, we can declare all these one binding a time *)
    let locals = List.concat_map (fun (p, _, _, _) -> Elab.pat_local_vars p) bs in
    emit_ln (String.concat " " (List.map (fun v -> "(define " ^ go_var v ^ " '())") locals));
    emit_ln "(miniml-let-guard (and";
    indent 2 (fun () ->
      bs |> List.iter (fun (head, args, _, rhs) ->
        let rhs = Fun (args, rhs) in
        emit_ln "(let ((scrutinee (let ()";
        indent 2 (fun () ->
          indent 6 (fun () -> emit_ln (go_expr_impure rhs ^ ")))"));
          emit_ln (go_pat head ^ ")")
        )
      )
    );
    emit_ln " ))"
  in
  List.iter bindings decls;
  String.concat "" (List.rev (deref result))

let () = Compile.add_backend "scheme" scheme
