open Util
open Token
open Common_syntax
open Ast

(* precedence walker *)

type 'a associativity =
  | AssocLeft  of ('a -> 'a -> 'a)
  | AssocRight of ('a -> 'a -> 'a)
  | AssocNone  of ('a list -> 'a)

let resolve_precedence (operands: 'a list) (operators: 'o list)
      (operator_info: 'o -> int * 'a associativity): 'a =
  (* removes n+1 elements of `xs` and n elements of `opers` *)
  let rec go prec xs opers =
    match (xs, opers) with
    (* no more operators (end of the input) *)
    | (x :: [], [])         -> (x, [], [])
    | (x :: xs, o :: opers) ->
      let (o_prec, assoc) = operator_info o in
      if o_prec < prec then
        (x, xs, o :: opers)
      else (
        match assoc with
        | AssocLeft f ->
          let (rhs, xs, opers) = go (o_prec + 1) xs opers in
          go prec (f x rhs :: xs) opers
        | AssocRight f ->
          let (rhs, xs, opers) = go o_prec xs opers in
          go prec (f x rhs :: xs) opers
        | AssocNone f ->
          (* removes n+1 elements of `xs` and n elements of `opers` *)
          let rec walk_nary acc xs opers =
            let (x, xs, opers) = go (o_prec + 1) xs opers in
            let acc = x :: acc in
            match opers with
            | o' :: opers ->
              let same_operator =
                (* We formerly used (=) to check that o and o' were the same.
                   In the interest of avoiding use of polymorphic comparison,
                   we instead check that `operator_info o'` has the same
                   precedence and verify that its associativity is also
                   AssocNone - we require that the caller doesn't try to
                   declare two non-associative operators at the same precedence
                   level *)
                match operator_info o' with
                | (o'_prec, AssocNone _) -> o_prec = o'_prec
                | (o'_prec, _) -> if o_prec = o'_prec then
                                    invalid_arg "non-associative operators must be in their own precedence level"
                                  else false
              in
              if same_operator then walk_nary acc xs opers
                               else (acc, xs, o' :: opers)
            | [] -> (acc, xs, [])
          in
          let (args, xs, opers) = walk_nary (x :: []) xs opers in
          go prec (f (List.rev args) :: xs) opers
      )
    | _ -> invalid_arg "input lists weren't the appropriate lengths"
  in
  match go 0 operands operators with
  | (res, [], []) -> res
  | _ -> invalid_arg "`resolve_precedence` couldn't consume the whole input"

(* parser combinators *)

type 'a parser =
  token list ->
  (token list -> 'a -> ast m_result) ->
  ast m_result

let pure x = fun input k -> k input x

type ('f, 'g, 'a) chain =
  | Chain of ('g -> 'a) parser * 'f

let (@>) p1 (Chain (p2, f)) = let p3 = fun input k ->
                                p1 input (fun input x ->
                                  p2 input (fun input g ->
                                    k input (fun g' -> g (g' x))))
                              in Chain (p3, f)

let fin f: ('f, 'a, 'a) chain = Chain (pure Fun.id, f)
let seq (Chain (p, f): ('f, 'f, 'a) chain): 'a parser =
  fun input k -> p input (fun input a_of_f -> k input (a_of_f f))
let force (e: string) (p: 'a option parser): 'a parser =
  fun input k -> p input (fun input opt -> match opt with | Some x -> k input x
                                                          | None -> Error (E e))
let many (p: 'a option parser): 'a list parser =
  fun input k ->
    let rec go input acc = p input (fun input opt ->
                                    match opt with
                                    | Some x -> go input (x :: acc)
                                    | None -> k input (List.rev acc))
    in go input []
(* append an artificial token to the input *)
let dummy tok input = tok :: input

(* helpers for parsing specific tokens *)

let is_rec      : bool parser
                = fun input k -> match input with | KRec      :: input -> k input true
                                                  | _                  -> k input false
and equal       : unit parser
                = fun input k -> match input with | Equal     :: input -> k input ()
                                                  | _                  -> Error (E "expected '='")
and arrow       : unit parser
                = fun input k -> match input with | Arrow     :: input -> k input ()
                                                  | _                  -> Error (E "expected '->'")
and colon       : unit parser
                = fun input k -> match input with | Colon     :: input -> k input ()
                                                  | _                  -> Error (E "expected ':'")
and semicolon   : unit parser
                = fun input k -> match input with | Semicolon :: input -> k input ()
                                                  | _                -> Error (E "expected ':'")
and k_struct    : unit parser
                = fun input k -> match input with | KStruct   :: input -> k input ()
                                                  | _                  -> Error (E "expected 'struct'")
and k_end       : unit parser
                = fun input k -> match input with | KEnd      :: input -> k input ()
                                                  | _                  -> Error (E "expected 'end'")
and k_in        : unit parser
                = fun input k -> match input with | KIn       :: input -> k input ()
                                                  | _                  -> Error (E "expected 'in'")
and k_then      : unit parser
                = fun input k -> match input with | KThen     :: input -> k input ()
                                                  | _                  -> Error (E "expected 'then'")
and k_else      : unit parser
                = fun input k -> match input with | KElse     :: input -> k input ()
                                                  | _                  -> Error (E "expected 'else'")
and k_with      : unit parser
                = fun input k -> match input with | KWith     :: input -> k input ()
                                                  | _                  -> Error (E "expected 'with'")
and ident_upper : (string * Token.span) parser
                = fun input k -> match input with | IdentUpper (name, sp) :: input -> k input (name, sp)
                                                  | _                              -> Error (E "expected uppercase identifier")

(* parsing types *)

let ty_params: string list parser =
  fun input k ->
  match input with
  (* TODO: care about spans in quoted identifiers? *)
  | IdentQuote (v, _) :: input -> k input (v :: []) (* single variable *)
  | OpenParen :: IdentQuote (v1, sp) :: input ->
    let rec go input vs = match input with
                          | Comma :: IdentQuote (v, _) :: input -> go input (v :: vs)
                          | CloseParen :: input -> k input (List.rev vs)
                          | _ -> Error (E "couldn't finish parsing type parameter list")
    in go input (v1 :: [])
  | OpenParen :: _ -> Error (E "expected type parameters")
  | _ -> k input []
let ty_name: string parser =
  (* TODO: care about spans of type names *)
  fun input k -> match input with | IdentLower (s, _) :: Equal :: input -> k input s
                                  | _ -> Error (E "expected type name")

let rec ty_atomic: typ parser =
  let rec ty_base input k =
    match input with
    | IdentQuote (v, sp) :: input -> k input (TVar (v, sp) :: [])
    | IdentLower (v, sp) :: input -> k input (TCon ([], v, sp, []) :: [])
    | IdentUpper (name, _) :: Dot :: input ->
      ty_base input (fun input ts ->
      match ts with
      | TCon (modules, v, sp, params) :: [] ->
          k input (TCon (MModule name :: modules, v, sp, params) :: [])
      | _  -> Error (E "only do 'Module.tycon' please"))
    | OpenParen :: input ->
      let rec go input ts =
        match input with
        | Comma :: input -> ty input (fun input t -> go input (t :: ts))
        | CloseParen :: input -> k input (List.rev ts)
        | _ -> Error (E "couldn't finish parsing type argument list")
      (* artificially prepend "," to the input stream
         to simplify the parsing here *)
      in go (dummy Comma input) []
    | _ -> Error (E "couldn't start parsing a type")
  in
  fun input k ->
  (* parse out all suffixed type constructors *)
  let rec go input params =
    let rec tycon (modules : mod_expr list) : (mod_expr list * string * span) option parser = fun input k ->
      match input with
      | IdentUpper (name, _) :: Dot :: input -> tycon (MModule name :: modules) input k
      | IdentLower (v, sp)          :: input -> k input (Some (List.rev modules, v, sp))
      | _                                    -> k input None
    in
    tycon [] input (fun input tycon_info_opt ->
    match tycon_info_opt with
    | Some (modules, v, sp) -> let params' = TCon (modules, v, sp, params) :: [] in
                               go input params'
    | None -> match params with
              | [] -> invalid_arg "should be impossible"
              | t :: [] -> k input t
              | _ -> Error (E "you may have been trying to use Haskell tuple syntax"))
  in ty_base input go
and ty: typ parser =
  fun input k ->
  (* TODO: migrate to use 'many', which is used for binary operators
     in parsing patterns, expressions, etc. *)
  let rec go input ty_operands ty_operators =
    ty_atomic input (fun input operand ->
    let ty_operands = operand :: ty_operands in
    match input with
    | Arrow :: input ->
      go input ty_operands ("->" :: ty_operators)
    | IdentSymbol ("*", _) :: input ->
      go input ty_operands ("*" :: ty_operators)
    | IdentSymbol (op, sp) :: _ ->
      Error (E ("invalid type operator: " ^ op ^ " " ^ describe_span sp))
    | _ ->
      let ty_expr: typ =
        resolve_precedence
          (List.rev ty_operands)
          (List.rev ty_operators)
          (function
           | "->" -> (0, AssocRight (fun l r -> TCon ([], "->", dummy_span, l :: r :: [])))
           | "*"  -> (1, AssocNone (fun ts -> TCon ([], "*", dummy_span, ts)))
           | _    -> invalid_arg "should be impossible")
      in k input ty_expr)
  in go input [] []

let record_decl_after_open_brace : record_decl parser =
  fun input k ->
  let rec fields input field_names fs =
    match input with
    | CloseBrace :: input -> k input (List.rev fs)
    | IdentLower (s, sp) :: input ->
        colon input (fun input () ->
        ty input (fun input t ->
        let* field_names =
          match StringMap.insert s () field_names with
          | Some field_names -> Ok field_names
          | None -> Error (E ("duplicate field name: " ^ s ^ " " ^ describe_span sp))
        in
        let fs = (s, sp, t) :: fs in
        (* support both { a : int; } and { a : int } *)
        match input with
        | Semicolon :: CloseBrace :: input
        | CloseBrace :: input ->
          k input (List.rev fs)
        | Semicolon :: input ->
          fields input field_names fs
        | _ -> Error (E "expected ';' or '}' after record field")))
    | _ -> Error (E "expected more record fields or end of record")
  in fields input StringMap.empty []

let ty_decl: (string list * string * typ_decl) option parser =
  fun input k ->
  match input with
  | KAnd :: input ->
    let p' =
      seq (ty_params @>
           ty_name   @>
           (
              fun input k ->
              match input with
              | Pipe :: _ ->
                let rec adt_constructors input cs =
                  match input with
                  (* TODO: use sp here *)
                  | Pipe :: IdentUpper (c, sp) :: KOf :: input ->
                    let rec go input ts =
                      match input with
                      | IdentSymbol ("*", _) :: input ->
                        ty_atomic input (fun input t -> go input (t :: ts))
                      | _ ->
                        adt_constructors input ((c, List.rev ts) :: cs)
                    (* artificially prepend "*" to the input stream
                       to simplify the parsing here *)
                    in go (IdentSymbol ("*", dummy_span) :: input) []
                  (* TODO: use sp here *)
                  | Pipe :: IdentUpper (c, sp) :: input ->
                    adt_constructors input ((c, []) :: cs)
                  | _ -> k input (Datatype (List.rev cs))
                in adt_constructors input []
              | OpenBrace :: input ->
                record_decl_after_open_brace input
                  (fun input record -> k input (Record record))
              | _ ->
                ty input (fun input t -> k input (Alias t))
           ) @>
      fin (fun vars name decl -> Some (vars, name, decl)))
    in
    p' input k
  | _ -> k input None

(* an optional type annotation *)
let ty_annot: typ option parser =
  fun input k ->
  match input with
  | Colon :: input ->
    ty input (fun input typ -> k input (Some typ))
  | _ -> k input None

(* an optional projection *)
let projection : field option parser =
  fun input k ->
  match input with
  | Dot :: IdentLower (s, sp) :: input -> k input (Some (s, sp))
  | _                                  -> k input None

(* parsing patterns *)

let rec pattern3 : pat option parser = fun input k ->
  match input with
  | KTrue        :: input -> k input (Some (PCon (("true", dummy_span), None)))
  | KFalse       :: input -> k input (Some (PCon (("false", dummy_span), None)))
  | IdentUpper (mod_name, sp) :: Dot
                 :: input -> (* See NOTE "OpenIn" *)
                             force ("expected pattern " ^ describe_span sp) pattern3 input (fun input sub_pat ->
                             k input (Some (POpenIn (MModule mod_name, sub_pat))))
  | TkCharLit c  :: input -> k input (Some (PCharLit c))
  | TkIntLit i   :: input -> k input (Some (PIntLit i))
  | TkStrLit s   :: input -> k input (Some (PStrLit s))
  | IdentLower (s, sp)
                 :: input -> k input (Some (PVar (s, sp)))
  | KUnder       :: input -> k input (Some PWild)
  | OpenBracket :: CloseBracket
                 :: input -> k input (Some (PList []))
  | OpenBracket  :: _     -> Error (E "only empty list literals are supported")
  | OpenParen :: KLet :: IdentSymbol (s, sp) :: CloseParen
                 :: input -> k input (Some (PVar ("let" ^ s, sp))) (* FIXME: span is slightly wrong *)
  | OpenParen :: IdentSymbol (s, sp) :: CloseParen
                 :: input -> k input (Some (PVar (s, sp)))
  | OpenParen :: CloseParen
                 :: input -> k input (Some (PTuple []))
  | OpenParen    :: input -> pattern0 input (fun input e ->
                             match input with
                             | CloseParen :: input -> k input (Some e)
                             | _ -> Error (E "expected ')'"))
  | _                     -> k input None
and pattern2 : pat option parser = fun input k ->
  match (input, (match input with
                 | IdentUpper (_, _) :: Dot :: _ -> false
                 | IdentUpper (_, _)        :: _ -> true
                 |                             _ -> false))
  with
  | (IdentUpper (constructor, sp) :: input, true) ->
    let constructor = (constructor, sp) in
    pattern3 input (fun input constructor_args_opt -> k input (
      (* See NOTE "constructor parsing hack" *)
      match constructor_args_opt with
      | None               -> Some (PCon (constructor, None))
      | Some (PTuple args) -> Some (PCon (constructor, Some args))
      | Some pat           -> Some (PCon (constructor, Some (pat :: [])))
    ))
  (* application isn't a pattern, so we don't have to worry about it :) *)
  | _ -> pattern3 input k
and pattern1 : pat option parser = fun input k ->
  pattern2 input (fun input first_operand_opt ->
  match first_operand_opt with
  | None -> k input None
  | Some first_operand ->
    (* parse a pattern operator and its RHS operand *)
    let next_operand: (string * pat) option parser = fun input k ->
      let continue input s =
        force "expected pattern" pattern2 input (fun input operand ->
        k input (Some (s, operand)))
      in
      match input with
      | Pipe                  :: input -> continue input "|"
      | IdentSymbol ("::", _) :: input -> continue input "::"
      | IdentSymbol (s, sp)   :: input -> Error (E ("invalid symbol in pattern: " ^ s
                                                    ^ " " ^ describe_span sp))
      | _                              -> k input None
    in
    many next_operand input (fun input (operands: (string * pat) list) ->
    let operators = List.map fst operands in
    let operands = first_operand :: List.map snd operands in
    let result = resolve_precedence operands operators (
      function
      | "|"  -> (0, AssocLeft (fun a b -> POr (a, b)))
      | "::" -> (1, AssocRight (fun a b -> PCon (("::", dummy_span), Some (a :: b :: []))))
      | _    -> invalid_arg "impossible operator")
    in
    k input (Some result)))
and pattern0 : pat parser = fun input k ->
  (* first operand *)
  force "expected pattern" pattern1 input (fun input first_operand ->
  (* additional operands *)
  let next_operand: pat option parser = fun input k ->
    match input with
    | Comma :: input ->
      force "expected pattern" pattern1 input (fun input operand ->
      k input (Some operand))
    | _ -> k input None
  in
  many next_operand input (fun input (operands: pat list) ->
  let pat = match first_operand :: operands with
            | single :: [] -> single
            | many         -> PTuple many
  in
  (* type ascription *)
  ty_annot input (fun input annot ->
  let pat = match annot with
            | None -> pat
            | Some ty -> PAsc (pat, ty)
  in
  k input pat)))

(* parsing expressions *)

(* TODO: introduce a dedicated AST form for this *)
let semicolon e1 e2 = App (App (Var (";", dummy_span),
                                e1),
                           e2)

let rec expr0 : expr option parser = fun input k ->
  expr1 input (fun input first_statement_opt ->
  match first_statement_opt with
  | None -> k input None
  | Some first_statement ->
    match input with
    | Semicolon :: input ->
      force_expr0 input (fun input rest ->
      k input (Some (semicolon first_statement rest)))
    | _ -> k input (Some first_statement))
and expr1 : expr option parser = fun input k ->
  expr1' expr2 input k
and expr1' fallback : expr option parser = fun input k ->
  match input with
  | KLet :: IdentSymbol (s, sp) :: input ->
    (* FIXME: span is slightly wrong *)
    let p' =
      seq (force "expected pattern" pattern3 @>
           equal                             @>
           force_expr0                       @>
           k_in                              @>
           force_expr0                       @>
      fin (fun pat () rhs () rest -> Some (
        App (App (Var ("let" ^ s, sp), rhs),
             Fun (pat :: [], rest))
      )))
    in
    p' input k
  | KLet :: input ->
    let p' =
      seq (val_bindings  @>
           k_in          @>
           force_expr0   @>
      fin (fun bindings () rest -> Some (
        LetIn (bindings, rest)
      )))
    in p' input k
  | KIf :: input ->
    (* FIXME: it's wrong to have `;` in the else clause; for example,
       (if true then 1 else 2; 3) = (if true then 1 else 2); 3 = 3
                      rather than   if true then 1 else (2; 3) = 1 *)
    (* FIXME: support omitting else? *)
    let p' =
      seq (force_expr0 @>
           k_then      @>
           force_expr0 @>
           k_else      @>
           force_expr1 @>
      fin (fun condition_expr () then_expr () else_expr -> Some (
        IfThenElse (condition_expr, then_expr, else_expr)
      )))
    in p' input k
  | KMatch :: input ->
    let p' =
      seq (force_expr0 @>
           k_with      @>
           many branch @>
      fin (fun scrutinee () branches -> Some (
        Match (scrutinee, branches)
      )))
    in p' input k
  | KFun :: input ->
    let p' =
      seq (many pattern3 @>
           arrow         @>
           force_expr0   @>
      fin (fun params () body -> Some (
        Fun (params, body)
      )))
    in p' input k
  | KFunction :: input ->
    many branch input (fun input branches -> k input (Some (Function branches)))
  | _ -> fallback input k
and branch : (pat * expr) option parser = fun input k ->
  match input with
  | Pipe :: input ->
    let p' =
      seq (pattern0    @>
           arrow       @>
           force_expr0 @>
      fin (fun pat () expr -> Some (pat, expr)))
    in p' input k
  | _ -> k input None
and expr2 = fun input k ->
  expr3 input (fun input first_operand_opt ->
  match first_operand_opt with
  | None -> k input None
  | Some first_operand ->
    (* parse an operator and its RHS operand *)
    let next_operand: ((string * span) * expr) option parser =
      fun input k ->
      let continue input s_and_sp =
        force "expected expression" (expr1' expr3) input (fun input operand ->
        k input (Some (s_and_sp, operand)))
      in
      match input with
      | Comma               :: input -> continue input (",", dummy_span)
      | Equal               :: input -> continue input ("=", dummy_span)
      | IdentSymbol (s, sp) :: input -> continue input (s,   sp)
      | _                            -> k input None
    in
    many next_operand input (fun input (operands: ((string * span) * expr) list) ->
    let operators = List.map fst operands in
    let operands = first_operand :: List.map snd operands in
    let result = resolve_precedence operands operators
      (fun (s, sp) ->
        let operator_function l r = App (App (Var (s, sp), l), r) in
        match String.get s 0 with
        | ';' -> (0, AssocRight operator_function)
        | ',' -> (1, AssocNone (fun es -> Tuple es))
        | '|' -> (2, AssocRight operator_function)
        | '&' -> (3, AssocRight operator_function)
        | '=' | '<' | '>' | '!'
              -> (4, AssocLeft operator_function)
        | '@' | '^'
              -> (5, AssocRight operator_function)
        | ':' -> (6, AssocRight operator_function)
        | '+' | '-'
              -> (7, AssocLeft operator_function)
        | '*' | '/'
              -> (8, AssocLeft operator_function)
        | _   -> invalid_arg ("can't determine precedence of operator '" ^ s ^ "' "
                              ^ describe_span sp))
    in
    k input (Some result)))
and expr3 = fun input k ->
  match (input, (match input with
                 | IdentUpper (_, _) :: Dot :: _ -> false
                 | IdentUpper (_, _)        :: _ -> true
                 |                             _ -> false))
  with
  | (IdentUpper (constructor, sp) :: input, true) ->
    let constructor = (constructor, sp) in
    expr4 input (fun input constructor_args_opt -> k input (
      (* NOTE "constructor parsing hack":
         The reader might be wondering: "isn't it hacky to detect
         multi-argument constructors by just matching on whether the
         argument is a tuple literal? After all, this would mean
         we would incorrectly parse something like `A ((1, 2))` as a
         two-argument constructor since parens are transparent to the
         AST."
         Well, as it turns out, the real OCaml parser does the same hack ;)
         *)
      match constructor_args_opt with
      | None              -> Some (Con (constructor, None))
      | Some (Tuple args) -> Some (Con (constructor, Some args))
      | Some e            -> Some (Con (constructor, Some (e :: [])))
    ))
  | _ ->
    expr4 input (fun input head_exp_opt ->
    match head_exp_opt with
    | None -> k input None
    | Some head_exp ->
      many expr4 input (fun input arg_exps ->
      let applications = List.fold_left (fun f x -> App (f, x)) head_exp arg_exps in
      k input (Some applications)))
and expr4 = fun input k ->
  expr5 input (fun input head_exp_opt ->
  match head_exp_opt with
  | None -> k input None
  | Some head_exp ->
    many projection input (fun input projections ->
    let projected = List.fold_left (fun e fld -> Project (e, fld)) head_exp projections in
    k input (Some projected)))
and expr5 = fun input k ->
  match input with
  | KTrue  :: input -> k input (Some (Con (("true", dummy_span), None)))
  | KFalse :: input -> k input (Some (Con (("false", dummy_span), None)))
  | IdentUpper (mod_name, _) :: Dot :: input ->
    (* TODO: care about spans *)
    (* NOTE "OpenIn": What we are dong here is desugaring
           Module.e = Module.(e) = let open Module in e
       This handles simple cases like `String.foo`, but incorrectly
       looks up non-existent identifiers in the enclosing scope, so:
           List.String.print_endline = print_endline
       *)
    force "expected expression" expr5 input (fun input sub_expr ->
      k input (Some (OpenIn (MModule mod_name, sub_expr)))
    )
  | IdentUpper (s, sp)
                 :: input -> k input (Some (Con ((s, sp), None))) (* duplicated from expr3 *)
  | TkCharLit c  :: input -> k input (Some (CharLit c))
  | TkIntLit i   :: input -> k input (Some (IntLit i))
  | TkStrLit s   :: input -> k input (Some (StrLit s))
  | IdentLower (s, sp)
                 :: input -> k input (Some (Var (s, sp)))
  | OpenBracket :: CloseBracket
                 :: input -> k input (Some (List []))
  | OpenBracket  :: _     -> Error (E "only empty list literals are supported")
  | OpenParen :: KLet :: IdentSymbol (s, sp) :: CloseParen (* FIXME: span is slightly wrong *)
                 :: input -> k input (Some (Var ("let" ^ s, sp)))
  | OpenParen :: IdentSymbol (s, sp) :: CloseParen
                 :: input -> k input (Some (Var (s, sp)))
  | OpenParen :: CloseParen
                 :: input -> k input (Some (Tuple []))
  | OpenParen    :: input ->
    force_expr0 input (fun input e ->
    match input with
    | CloseParen :: input -> k input (Some e)
    | _ -> Error (E "expected ')'"))
  | _ -> k input None
and force_expr0 input k = force "Expected expression" expr0 input k
and force_expr1 input k = force "Expected expression" expr1 input k
and val_binding : binding option parser = fun input k ->
  match input with
  | KAnd :: input ->
    let p' =
      seq (force "expected function name or pattern" pattern3 @>
           many pattern3 @>
           ty_annot      @>
           equal         @>
           force_expr0   @>
      fin (fun head_pat arg_pats annot () rhs -> Some (head_pat, arg_pats, annot, rhs)))
    in p' input k
  | _ -> k input None
and val_bindings : bindings parser = fun input k ->
  is_rec input (fun input is_rec ->
  many val_binding (dummy KAnd input) (fun input bindings ->
  k input (Bindings (is_rec, bindings))))

(* declarations *)

let rec decls input k =
  many (fun input k ->
    match input with
    | KType :: input ->
      many ty_decl (dummy KAnd input) (fun input ty_decls ->
      k input (Some (Types ty_decls)))
    | KLet :: input ->
      val_bindings input (fun input bindings ->
      k input (Some (Let bindings)))
    | KModule :: input ->
      module_decl input (fun input (name, decls) ->
      k input (Some (Module (name, decls))))
    | KOpen :: input ->
      ident_upper input (fun input name ->
      k input (Some (Open name)))
    | _ -> k input None
  ) input k
and module_decl input k =
  let p =
    seq (ident_upper @>
         equal       @>
         k_struct    @>
         decls       @>
         k_end       @>
    fin (fun ident () () decls () ->
      (ident, decls)))
  in p input k

let parse: token list -> ast m_result =
  fun tokens ->
  decls tokens (fun remaining ds ->
  match remaining with | [] -> Ok ds
                       | _ -> Error (E "unexpected tokens at EOF"))
