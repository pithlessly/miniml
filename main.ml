type token =
  | OpenParen
  | CloseParen
  | OpenBracket
  | CloseBracket
  | Dot
  | Colon
  | Comma
  | Semicolon
  | Equal
  | Pipe
  | Arrow
  | KTrue | KFalse
  | KType | KOf
  | KLet | KRec | KAnd | KIn
  | KIf | KThen | KElse
  | KMatch | KWith
  | KFun
  | KUnder
  | IdentLower of string
  | IdentUpper of string
  | IdentSymbol of string
  | IdentQuote of string
  | CharLit of char
  | IntLit of int
  | StrLit of string

let lex str =
  (* character properties *)
  let lower c = ('a' <= c && c <= 'z') || c = '_' || c = '\'' in
  let upper c = 'A' <= c && c <= 'Z' in
  let numer c = '0' <= c && c <= '9' in
  let ident c = upper c || lower c || numer c in
  let symbolic c = match c with | '&' | '*' | '+' | '-' | '.' | ':'
                                | '<' | '>' | '=' | '^' | '|' | '@' -> true
                                | _ -> false
  in
  (* main logic *)
  let length = String.length str in
  let char i = if i < length then Some (String.get str i) else None in
  let rec go i tokens =
    let adv t = go (i + 1) (t :: tokens) in
    let take_range d (included : char -> bool) (mk_tok : string -> token) =
      let rec scan d = match char (i + d) with
                       | Some c -> if included c then scan (d + 1) else d
                       | None -> d
      in
      let d = scan d in go (i + d) (mk_tok (String.sub str i d) :: tokens)
    in
    match char i with
    | Some '\n'
    | Some ' ' -> go (i + 1) tokens
    | Some '"' ->
      let rec scan i parts escaped =
        match (char i, escaped) with
        | (None, _) -> Error "expected trailing quote for string literal, got EOF"
        | (Some '"',  false) -> Ok (i + 1, StrLit (String.concat "" (List.rev parts)))
        | (Some '\\', false) -> scan (i + 1) parts true
        | (Some c,    false) -> scan (i + 1) (String.make 1 c :: parts) false
        | (Some '"',  true)  -> scan (i + 1) ("\"" :: parts) false
        | (Some '\\', true)  -> scan (i + 1) ("\\" :: parts) false
        | (Some _,    true)  -> Error "invalid escape sequence in string literal"
      in
      (match scan (i + 1) [] false with
       | Error e -> Error e
       | Ok (i, tok) -> go i (tok :: tokens))
    | Some '\'' ->
      let char_done c i =
        match char i with
        | None -> Error "expected trailing quote for character literal, got EOF"
        | Some '\'' -> go (i + 1) (CharLit c :: tokens)
        | Some _ -> if lower c then take_range 1 ident (fun s -> IdentQuote s)
                    else Error "unterminated character literal"
      in
      (match char (i + 1) with
       | Some '\\' ->
         (match char (i + 2) with
          | Some 'n' -> char_done '\n' (i + 3)
          | Some '\\' -> char_done '\\' (i + 3)
          | Some '\'' -> char_done '\'' (i + 3)
          | _ -> Error "invalid escape sequence in character literal")
       | Some c -> char_done c (i + 2)
       | _ -> Error "malformed character literal")
    | Some '(' ->
      (match char (i + 1) with
       | Some '*' ->
           let rec scan i =
             match (char i, char (i + 1)) with
             | (Some '*', Some ')') -> go (i + 2) tokens
             | (Some _,   _       ) -> scan (i + 1)
             | (None,     _       ) -> Error "got EOF while scanning comment"
           in scan (i + 2)
       | _        -> adv OpenParen)
    | Some ')' -> adv CloseParen
    | Some '[' -> adv OpenBracket
    | Some ']' -> adv CloseBracket
    | Some ',' -> adv Comma
    | Some ';' -> adv Semicolon
    | Some c ->
      let mk_lower_ident s = match s with
                             | "true" -> KTrue | "false" -> KFalse
                             | "type" -> KType | "of" -> KOf
                             | "let" -> KLet | "rec" -> KRec
                             | "and" -> KAnd | "in" -> KIn
                             | "if" -> KIf | "then" -> KThen | "else" -> KElse
                             | "match" -> KMatch | "with" -> KWith
                             | "fun" -> KFun
                             | "_" -> KUnder
                             | _ -> IdentLower s
      in
      let mk_symbolic_ident s = match s with
                                | "."  -> Dot
                                | ":"  -> Colon
                                | "="  -> Equal
                                | "|"  -> Pipe
                                | "->" -> Arrow
                                | _    -> IdentSymbol s
      in
      if upper c then take_range 0 ident (fun s -> IdentUpper s) else
      if lower c then take_range 0 ident mk_lower_ident else
      if numer c then take_range 0 numer (fun s -> IntLit (int_of_string s)) else
      if symbolic c then take_range 0 symbolic mk_symbolic_ident else
        Error ("unexpected character: " ^ String.make 1 c
               ^ " at position: " ^ string_of_int i)
    | None -> Ok (List.rev tokens)
  in
  go 0 []

type ('var, 'con, 'ty) typ_decl =
                               | Datatype of (string * 'ty list) list
                               | Alias    of 'ty
type ('var, 'con, 'ty) pat =
                               | POr      of ('var, 'con, 'ty) pat
                                           * ('var, 'con, 'ty) pat
                               | PTuple   of ('var, 'con, 'ty) pat list
                               | PList    of ('var, 'con, 'ty) pat list
                               | PCon     of 'con
                                           * ('var, 'con, 'ty) pat list option
                               | PCharLit of char
                               | PIntLit  of int
                               | PStrLit  of string
                               | PVar     of 'var
                               | PAsc     of ('var, 'con, 'ty) pat * 'ty
                               | PWild
type ('var, 'con, 'ty) binding = ('var, 'con, 'ty) pat      (* head pattern *)
                               * ('var, 'con, 'ty) pat list (* argument patterns *)
                               * 'ty option              (* return type annotation *)
                               * ('var, 'con, 'ty) expr     (* RHS *)
and  ('var, 'con, 'ty) bindings =
                               | Bindings of bool (* recursive? *)
                                           * ('var, 'con, 'ty) binding list
and  ('var, 'con, 'ty) expr =
                               | Tuple      of ('var, 'con, 'ty) expr list
                               | List       of ('var, 'con, 'ty) expr list
                               | Con        of 'con
                                             * ('var, 'con, 'ty) expr list option
                               | CharLit    of char
                               | IntLit     of int
                               | StrLit     of string
                               | Var        of 'var
                               | LetOpen    of mod_expr
                                             * ('var, 'con, 'ty) expr
                               | App        of ('var, 'con, 'ty) expr
                                             * ('var, 'con, 'ty) expr
                               | LetIn      of ('var, 'con, 'ty) bindings
                                             * ('var, 'con, 'ty) expr
                               | Match      of ('var, 'con, 'ty) expr
                                             * ( ('var, 'con, 'ty) pat
                                               * ('var, 'con, 'ty) expr
                                               ) list
                               | IfThenElse of ('var, 'con, 'ty) expr
                                             * ('var, 'con, 'ty) expr
                                             * ('var, 'con, 'ty) expr
                               | Fun        of ('var, 'con, 'ty) pat list
                                             * ('var, 'con, 'ty) expr
and mod_expr =                 | Module of string
type ('var, 'con, 'ty) decl =
                               | Let      of ('var, 'con, 'ty) bindings
                               | Types    of ( string list
                                             * string
                                             * ('var, 'con, 'ty) typ_decl
                                             ) list

type ast_typ = | TVar of string
               | TCon of string * ast_typ list
type ast_pat = (string, string, ast_typ) pat
type ast_binding = (string, string, ast_typ) binding
type ast_bindings = (string, string, ast_typ) bindings
type ast_expr = (string, string, ast_typ) expr
type ast_typ_decl = (string, string, ast_typ) typ_decl
type ast_decl = (string, string, ast_typ) decl
type ast = ast_decl list

(* parser combinators *)

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
              (* FIXME: use of polymorphic compare is bad - this should
               * be replaced by checking `operator_info o'` has the same
               * precedence and verifying that its associativity is also
               * AssocNone - we require that the caller doesn't try to
               * declare two non-associative operators at the same
               * precedence level *)
              if o = o' then walk_nary acc xs opers
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

type 'a parser =
  token list ->
  (token list -> 'a -> (ast, string) result) ->
  (ast, string) result

let pure x = fun input k -> k input x

type ('f, 'g, 'a) chain =
  | Chain of ('g -> 'a) parser * 'f

(* basic combinators *)
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
                                                          | None -> Error e)
let many (p: 'a option parser): 'a list parser =
  fun input k ->
    let rec go input acc = p input (fun input opt ->
                                    match opt with
                                    | Some x -> go input (x :: acc)
                                    | None -> k input (List.rev acc))
    in go input []
let dummy tok input = tok :: input

let parse: token list -> (ast, string) result =
  (* parsing types *)
  let ty_params: string list parser =
    fun input k ->
    match input with
    | IdentQuote v :: input -> k input (v :: []) (* single variable *)
    | OpenParen :: IdentQuote v1 :: input ->
      let rec go input vs = match input with
                            | Comma :: IdentQuote v :: input -> go input (v :: vs)
                            | CloseParen :: input -> k input (List.rev vs)
                            | _ -> Error "couldn't finish parsing type parameter list"
      in go input (v1 :: [])
    | OpenParen :: _ -> Error "expected type parameters"
    | _ -> k input []
  in
  let ty_name: string parser =
    fun input k -> match input with | IdentLower s :: Equal :: input -> k input s
                                    | _ -> Error "expected type name"
  in
  let rec ty_atomic: ast_typ parser =
    let ty_base input k =
      match input with
      | IdentQuote v :: input -> k input (TVar v       :: [])
      | IdentLower v :: input -> k input (TCon (v, []) :: [])
      | OpenParen :: input ->
        let rec go input ts =
          match input with
          | Comma :: input -> ty input (fun input t -> go input (t :: ts))
          | CloseParen :: input -> k input (List.rev ts)
          | _ -> Error "couldn't finish parsing type argument list"
        (* artificially prepend "," to the input stream
           to simplify the parsing here *)
        in go (dummy Comma input) []
      | _ -> Error "couldn't start parsing a type"
    in
    fun input k ->
    (* parse out all suffixed type constructors *)
    let rec go input params =
      match input with
      | IdentLower v :: input -> go input (TCon (v, params) :: [])
      | _ -> match params with
             | [] -> invalid_arg "should be impossible"
             | t :: [] -> k input t
             | _ -> Error "you may have been trying to use Haskell tuple syntax"
    in ty_base input go
  and ty: ast_typ parser =
    fun input k ->
    (* TODO: migrate to use 'many', which is used for binary operators
       in parsing patterns, expressions, etc. *)
    let rec go input ty_operands ty_operators =
      ty_atomic input (fun input operand ->
      let ty_operands = operand :: ty_operands in
      match input with
      | Arrow :: input ->
        go input ty_operands ("->" :: ty_operators)
      | IdentSymbol "*" :: input ->
        go input ty_operands ("*" :: ty_operators)
      | IdentSymbol op :: _ ->
        Error ("invalid type operator: " ^ op)
      | _ ->
        let ty_expr: ast_typ =
          resolve_precedence
            (List.rev ty_operands)
            (List.rev ty_operators)
            (fun op ->
              match op with
              | "->" -> (0, AssocRight (fun l r -> TCon ("->", l :: r :: [])))
              | "*"  -> (1, AssocNone (fun ts -> TCon ("*", ts)))
              | _    -> invalid_arg "should be impossible")
        in k input ty_expr)
    in go input [] []
  in
  let ty_decl: (string list * string * ast_typ_decl) option parser =
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
                    | Pipe :: IdentUpper c :: KOf :: input ->
                      let rec go input ts =
                        match input with
                        | IdentSymbol "*" :: input ->
                          ty_atomic input (fun input t -> go input (t :: ts))
                        | _ ->
                          adt_constructors input ((c, List.rev ts) :: cs)
                      (* artificially prepend "*" to the input stream
                         to simplify the parsing here *)
                      in go (IdentSymbol "*" :: input) []
                    | Pipe :: IdentUpper c :: input ->
                      adt_constructors input ((c, []) :: cs)
                    | _ -> k input (Datatype (List.rev cs))
                  in adt_constructors input []
                | _ ->
                  ty input (fun input t -> k input (Alias t))
             ) @>
        fin (fun vars name decl -> Some (vars, name, decl)))
      in
      p' input k
    | _ -> k input None
  in
  let ty_annot: ast_typ option parser =
    fun input k ->
    match input with
    | Colon :: input ->
      ty input (fun input typ -> k input (Some typ))
    | _ -> k input None
  in

  (* helpers for parsing specific tokens *)
  let is_rec : bool parser
             = fun input k -> match input with | KRec  :: input -> k input true
                                               | _              -> k input false
  and equal  : unit parser
             = fun input k -> match input with | Equal :: input -> k input ()
                                               | _              -> Error "expected '='"
  and arrow  : unit parser
             = fun input k -> match input with | Arrow :: input -> k input ()
                                               | _              -> Error "expected '->'"
  and k_in   : unit parser
             = fun input k -> match input with | KIn   :: input -> k input ()
                                               | _              -> Error "expected 'in'"
  and k_then : unit parser
             = fun input k -> match input with | KThen :: input -> k input ()
                                               | _              -> Error "expected 'then'"
  and k_else : unit parser
             = fun input k -> match input with | KElse :: input -> k input ()
                                               | _              -> Error "expected 'else'"
  and k_with : unit parser
             = fun input k -> match input with | KWith :: input -> k input ()
                                               | _              -> Error "expected 'with'"
  in

  (* parsing patterns *)
  let rec pattern3 : ast_pat option parser = fun input k ->
    match input with
    | KTrue        :: input -> k input (Some (PCon ("true", None)))
    | KFalse       :: input -> k input (Some (PCon ("false", None)))
    | CharLit c    :: input -> k input (Some (PCharLit c))
    | IntLit i     :: input -> k input (Some (PIntLit i))
    | StrLit s     :: input -> k input (Some (PStrLit s))
    | IdentLower s :: input -> k input (Some (PVar s))
    | KUnder       :: input -> k input (Some PWild)
    | OpenBracket :: CloseBracket
                   :: input -> k input (Some (PList []))
    | OpenBracket  :: _     -> Error "only empty list literals are supported"
    | OpenParen :: IdentSymbol s :: CloseParen
                   :: input -> k input (Some (PVar s))
    | OpenParen :: CloseParen
                   :: input -> k input (Some (PTuple []))
    | OpenParen    :: input -> pattern0 input (fun input e ->
                               match input with
                               | CloseParen :: input -> k input (Some e)
                               | _ -> Error "expected ')'")
    | _                     -> k input None
  and pattern2 : ast_pat option parser = fun input k ->
    (* NOTE: we don't have the same guard as in expr2 because we aren't bothering
       to handle the Module.(...) pattern syntax. *)
    match input with
    | IdentUpper constructor :: input ->
      pattern3 input (fun input constructor_args_opt -> k input (
        (* See NOTE "constructor parsing hack" *)
        match constructor_args_opt with
        | None               -> Some (PCon (constructor, None))
        | Some (PTuple args) -> Some (PCon (constructor, Some args))
        | Some pat           -> Some (PCon (constructor, Some (pat :: [])))
      ))
    (* application isn't a pattern, so we don't have to worry about it :) *)
    | _ -> pattern3 input k
  and pattern1 : ast_pat option parser = fun input k ->
    pattern2 input (fun input first_operand_opt ->
    match first_operand_opt with
    | None -> k input None
    | Some first_operand ->
      (* parse a pattern operator and its RHS operand *)
      let next_operand: (string * ast_pat) option parser = fun input k ->
        let continue input s =
          force "expected pattern" pattern2 input (fun input operand ->
          k input (Some (s, operand)))
        in
        match input with
        | Pipe             :: input -> continue input "|"
        | IdentSymbol "::" :: input -> continue input "::"
        | IdentSymbol s    :: input -> Error "invalid symbol in pattern: "
        | _                         -> k input None
      in
      many next_operand input (fun input (operands: (string * ast_pat) list) ->
      let operators = List.map fst operands in
      let operands = first_operand :: List.map snd operands in
      let result = resolve_precedence operands operators (fun op ->
        match op with
        | "|"  -> (0, AssocLeft (fun a b -> POr (a, b)))
        | "::" -> (1, AssocRight (fun a b -> PCon ("::", Some (a :: b :: []))))
        | _    -> invalid_arg "impossible operator")
      in
      k input (Some result)))
  and pattern0 : ast_pat parser = fun input k ->
    (* first operand *)
    force "expected pattern" pattern1 input (fun input first_operand ->
    (* additional operands *)
    let next_operand: ast_pat option parser = fun input k ->
      match input with
      | Comma :: input ->
        force "expected pattern" pattern1 input (fun input operand ->
        k input (Some operand))
      | _ -> k input None
    in
    many next_operand input (fun input (operands: ast_pat list) ->
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
  in

  (* parsing expressions *)
  let rec expr0 : ast_expr option parser = fun input k ->
    match input with
    | KLet :: input ->
      let p' =
        seq (val_bindings  @>
             k_in          @>
             force_expr    @>
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
        seq (force_expr @>
             k_then     @>
             force_expr @>
             k_else     @>
             force_expr @>
        fin (fun condition_expr () then_expr () else_expr -> Some (
          IfThenElse (condition_expr, then_expr, else_expr)
        )))
      in p' input k
    | KMatch :: input ->
      let branch : (ast_pat * ast_expr) option parser = fun input k ->
        match input with
        | Pipe :: input ->
          let p' =
            seq (pattern0   @>
                 arrow      @>
                 force_expr @>
            fin (fun pat () expr -> Some (pat, expr)))
          in p' input k
        | _ -> k input None
      in
      let p' =
        seq (force_expr  @>
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
             force_expr    @>
        fin (fun params () body -> Some (
          Fun (params, body)
        )))
      in p' input k
    | _ -> expr1 input k
  and expr1 = fun input k ->
    expr2 input (fun input first_operand_opt ->
    match first_operand_opt with
    | None -> k input None
    | Some first_operand ->
      (* parse an operator and its RHS operand *)
      let next_operand: (string * ast_expr) option parser = fun input k ->
        let continue input s =
          force "expected expression" expr2 input (fun input operand ->
          k input (Some (s, operand)))
        in
        match input with
        | Comma         :: input -> continue input ","
        | Equal         :: input -> continue input "="
        | IdentSymbol s :: input -> continue input s
        (* NOTE: we treat semicolon as only an operator because we don't
           handle semicolons in list literals *)
        | Semicolon     :: input -> continue input ";"
        | _                      -> k input None
      in
      many next_operand input (fun input (operands: (string * ast_expr) list) ->
      let operators = List.map fst operands in
      let operands = first_operand :: List.map snd operands in
      let result = resolve_precedence operands operators
        (fun op ->
          let operator_function l r = App (App (Var op, l), r) in
          match String.get op 0 with
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
          | '*' -> (8, AssocLeft operator_function)
          | _   -> invalid_arg ("can't determine precedence of operator '" ^ op ^ "'"))
      in
      k input (Some result)))
  and expr2 = fun input k ->
    match (input, (match input with
                   | IdentUpper _ :: Dot :: _ -> false
                   | IdentUpper _        :: _ -> true
                   |                        _ -> false))
    with
    | (IdentUpper constructor :: input, true) ->
      expr3 input (fun input constructor_args_opt -> k input (
        (* NOTE "constructor parsing hack":
           The reader might be wondering: "isn't it hacky to detect
           multi-argument constructors by just matching on whether the
           argument is a tuple literal literal? After all, this would mean
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
      expr3 input (fun input head_exp_opt ->
      match head_exp_opt with
      | None -> k input None
      | Some head_exp ->
        many expr3 input (fun input arg_exps ->
        let applications = List.fold_left (fun f x -> App (f, x)) head_exp arg_exps in
        k input (Some applications)))
  and expr3 = fun input k ->
    match input with
    | KTrue  :: input -> k input (Some (Con ("true", None)))
    | KFalse :: input -> k input (Some (Con ("false", None)))
    | IdentUpper mod_name :: Dot :: input ->
      (* NOTE: what we are dong here is desugaring
             Module.e = Module.(e) = let open Module in e
         This handles simple cases like `String.foo`, but incorrectly
         looks up non-existent identifiers in the enclosing scope, so:
             List.String.print_endline = print_endline
         *)
      force "expected expression" expr3 input (fun input sub_expr ->
        k input (Some (LetOpen (Module mod_name, sub_expr)))
      )
    | IdentUpper s :: input -> k input (Some (Con (s, None))) (* duplicated from expr2 *)
    | CharLit c    :: input -> k input (Some (CharLit c))
    | IntLit i     :: input -> k input (Some (IntLit i))
    | StrLit s     :: input -> k input (Some (StrLit s))
    | IdentLower s :: input -> k input (Some (Var s))
    | OpenBracket :: CloseBracket
                   :: input -> k input (Some (List []))
    | OpenBracket  :: _     -> Error "only empty list literals are supported"
    | OpenParen :: CloseParen
                   :: input -> k input (Some (Tuple []))
    | OpenParen    :: input ->
      force_expr input (fun input e ->
      match input with
      | CloseParen :: input -> k input (Some e)
      | _ -> Error "expected ')'")
    | _ -> k input None
  and force_expr input k = force "Expected expression" expr0 input k
  and val_binding : ast_binding option parser = fun input k ->
    match input with
    | KAnd :: input ->
      let p' =
        seq (force "expected function name or pattern" pattern3 @>
             many pattern3 @>
             ty_annot      @>
             equal         @>
             force_expr    @>
        fin (fun head_pat arg_pats annot () rhs -> Some (head_pat, arg_pats, annot, rhs)))
      in p' input k
    | _ -> k input None
  and val_bindings : ast_bindings parser = fun input k ->
    is_rec input (fun input is_rec ->
    many val_binding (dummy KAnd input) (fun input bindings ->
    k input (Bindings (is_rec, bindings))))
  in

  let decls =
    many (fun input k ->
      match input with
      | KType :: input ->
        many ty_decl (dummy KAnd input) (fun input ty_decls ->
        k input (Some (Types ty_decls)))
      | KLet :: input ->
        val_bindings input (fun input bindings ->
        k input (Some (Let bindings)))
      | _ -> k input None
    )
  in

  fun tokens ->
  decls tokens (fun remaining ds ->
  match remaining with | [] -> Ok ds
                       | _ -> Error "unexpected tokens at EOF")

type core_level = int
type core_var_id = int
type core_qvar = | QVar of string * core_var_id
type core_con_id = int
type core_con  = | CCon of string * core_con_id
type core_type = | CQVar of core_qvar
                 | CUVar of core_uvar ref
                 | CTCon of core_con * core_type list
and  core_uvar = | Unknown of string * core_var_id * core_level
                 | Known   of core_type
(* ordinary variable binding *)
type core_var  = | Binding of string (* name in the syntax *)
                            * core_var_id (* numeric ID *)
                            * core_qvar list (* forall parameters *)
                            * core_type (* type *)
(* constructor variable binding *)
type core_cvar = | CBinding of string (* name in the syntax *)
                             * core_var_id (* numeric ID *)
                             * core_qvar list (* forall parameters *)
                             * core_type list (* parameter types *)
                             * core_type      (* return type *)

type core_pat = (core_var, core_cvar, unit) pat
type core_binding = (core_var, core_cvar, unit) binding
type core_bindings = (core_var, core_cvar, unit) bindings
type core_expr = (core_var, core_cvar, unit) expr
type core_typ_decl = (core_var, core_cvar, unit) typ_decl
type core_decl = (core_var, core_cvar, unit) decl
type core = core_decl list

(* some helpers *)
let map_m
  ((pure  : 'b list -> 'b_list_m),
   ((>>=) : 'b_m -> ('b -> 'b_list_m) -> 'b_list_m))
  (f : 'a -> 'b_m)
  : 'a list -> 'b_list_m =
  let rec go ys xs =
    match xs with
    | [] -> pure (List.rev ys)
    | x :: xs -> f x >>= fun y -> go (y :: ys) xs
  in go []
let fold_left_m
  ((pure  : 'b -> 'b_m),
   ((>>=) : 'b_m -> ('b -> 'b_m) -> 'b_m))
  (f : 'b -> 'a -> 'b_m)
  : 'b -> 'a list -> 'b_m =
  let rec go acc xs =
    match xs with
    | [] -> pure acc
    | x :: xs -> f acc x >>= fun y -> go y xs
  in go

let state_monad =
  let pure a    = (fun s -> (s, a))
  and (>>=) g f = (fun s -> let (s, a) = g s in f a s)
  in (pure, (>>=))
let error_monad =
  let pure a    = Ok a
  and (>>=) x f = match x with | Error e -> Error e | Ok a -> f a
  in (pure, (>>=))
let error_state_monad =
  let pure a    = (fun s -> Ok (s, a))
  and (>>=) g f = (fun s -> match g s with | Error e -> Error e | Ok (s, a) -> f a s)
  in (pure, (>>=))

let deref = (!)
let (>>=) x f = snd error_monad x f
let (=<<) f x = (>>=) x f
let (let*) x f = (>>=) x f
let counter () =
  let i = ref 0 in
  (fun () ->
    let v = deref i in
    i := 1 + v;
    v)

let show_ty : core_type -> string =
  let rec go prec ty =
    let wrap_if thresh f =
      if prec <= thresh then f else
      fun acc -> "(" :: f (")" :: acc) in
    match ty with
    | CQVar (QVar (s, _)) -> fun acc -> "'" :: s :: acc
    | CUVar r -> (match deref r with
                  | Known ty -> go prec ty
                  | Unknown (s, _, lvl) ->
                    fun acc -> s :: "(" :: string_of_int lvl :: ")" :: acc)
    | CTCon (CCon ("->", _), a :: b :: []) ->
      let a = go 1 a and b = go 0 b in
      wrap_if 0 (fun acc -> a (" -> " :: b acc))
    | CTCon (CCon ("*", _), []) -> fun acc -> "unit" :: acc
    | CTCon (CCon ("*", _), a :: args) ->
      let a = go 2 a and args = List.map (go 2) args in
      wrap_if 1 (fun acc -> a (List.fold_right
                                (fun arg acc -> " * " :: arg acc) args acc))
    | CTCon (CCon (con, _), []) -> fun acc -> con :: acc
    | CTCon (CCon (con, _), a :: []) ->
      let a = go 2 a in fun acc -> a (" " :: con :: acc)
    | CTCon (CCon (con, _), a :: args) ->
      let a = go 0 a and args = List.map (go 0) args in
      fun acc -> "(" :: a (List.fold_right
                            (fun arg acc -> ", " :: arg acc)
                            args
                            (") " :: con :: acc))
  in fun ty -> String.concat "" (go 0 ty [])

type 'a string_map = int * (string * 'a) list
(* TODO: replace with a more efficient implementation *)
let map_empty : 'a string_map = (0, [])
let map_singleton : (string * 'a) -> 'a string_map =
  fun entry -> (1, entry :: [])
let map_lookup k : 'a string_map -> 'a option =
  fun (_, map) -> Option.map snd (List.find_opt (fun (k', _) -> k = k') map)
let map_eql (elem_eql : 'a -> 'a -> bool) : 'a string_map -> 'a string_map -> bool =
  fun (n1, m1) (n2, m2) ->
    if n1 <> n2 then false else
    let rec go m1 m2 =
      match (m1, m2) with
      | ([], []) -> true
      | ([], _) -> invalid_arg "impossible - maps have different sizes"
      | ((k, v) :: m1, m2) ->
        let rec remove_key acc m2 =
          match m2 with
          | []             -> false (* k not present in m2 *)
          | (k', v') :: m2 ->
            if k <> k' then
              remove_key ((k', v') :: acc) m2
            else
              if not (elem_eql v v') then false else
              let m2 = List.fold_left (fun m2 pair -> pair :: m2) m2 acc in
              go m1 m2
        in remove_key [] m2
    in go m1 m2
let map_insert (k, v) : 'a string_map -> 'a string_map option =
  fun (n, m) -> match List.find_opt (fun (k', _) -> k = k') m with
                | None   -> Some (n + 1, (k, v) :: m)
                | Some _ -> None
type dup_err = | DupErr of string
let map_disjoint_union
  : 'a string_map -> 'a string_map -> ('a string_map, dup_err) result
  = fun map1 map2 ->
    (* sort by size *)
    let (map1, map2) =
      let (n1, _) = map1 in
      let (n2, _) = map2 in
      if n1 < n2 then (map1, map2) else (map2, map1)
    in
    let ((n1, m1), (n2, m2)) = (map1, map2) in
    let rec go m1 acc =
      match m1 with
      | [] -> Ok (n1 + n2, acc)
      | (k, v) :: m1 ->
        match map_lookup k map2 with
        | Some _ -> Error (DupErr k)
        | None   -> go m1 ((k, v) :: acc)
    in go m1 m2
let map_map (f : string -> 'a -> 'b) : 'a string_map -> 'b string_map =
  fun (n, m) -> (n, List.map (fun (k, v) -> (k, f k v)) m)
(* hopefully the order is irrelevant *)
let map_fold_left (f : 'a -> (string * 'b) -> 'a) : 'a -> 'b string_map -> 'a =
  let rec go acc m = (match m with
                      | [] -> acc
                      | kv :: m -> go (f acc kv) m)
  in fun init (_, m) -> go init m

let rec occurs_check : core_uvar ref -> core_type -> (unit, string) result = fun v ty ->
  match ty with
  | CQVar _ -> Ok ()
  | CTCon (_, tys) ->
    let rec go tys =
      match tys with
      | []         -> Ok ()
      | ty' :: tys -> let* () = occurs_check v ty' in go tys
    in go tys
  | CUVar v' ->
    if v == v' then
      Error "occurs check failed (cannot construct infinite type)"
    else
      match deref v' with
      | Known ty'                  -> occurs_check v ty'
      | Unknown (name', id', lvl') ->
        Ok (
          match deref v with
          | Known _             -> ()
          | Unknown (_, _, lvl) ->
            v' := Unknown (name', id', min lvl lvl');
        )

(* follow `Known`s until we get where we wanted *)
let ground : core_type -> core_type =
  let rec go ty (obligations : core_uvar ref list) =
    match ty with
    | CUVar r -> (
        match deref r with
        | Known ty -> go ty (r :: obligations)
        | _ -> (ty, obligations)
      )
    | _ -> (ty, obligations)
  in
  fun ty ->
    let (ty, obligations) = go ty [] in
    (* path compression *)
    List.iter (fun r -> r := Known ty) obligations;
    ty

let rec unify : core_type -> core_type -> (unit, string) result = fun t1 t2 ->
  (* FIXME: avoid physical equality on types? *)
  if t1 == t2 then Ok () else
  match (ground t1, ground t2) with
  | (CQVar qv, _) | (_, CQVar qv) ->
    let QVar (name, a) = qv in
    Error ("found CQVar (" ^ name ^ " " ^ string_of_int a ^ ") - should be impossible")
  | (CUVar r, t') | (t', CUVar r) ->
    (* r must be Unknown *)
    if
      match t' with
      | CUVar r' -> r == r'
      | _        -> false
    then
      Ok ()
    else
      let* () = occurs_check r t' in
      Ok (r := Known t')
  | (CTCon (c1, p1), CTCon (c2, p2)) ->
    let CCon (n1, id1) = c1 and CCon (n2, id2) = c2 in
    if id1 <> id2 then
      Error ("cannot unify different type constructors: " ^ n1 ^ " != " ^ n2)
    else unify_all p1 p2
and unify_all : core_type list -> core_type list -> (unit, string) result = fun ts1 ts2 ->
  match (ts1, ts2) with
  | ([], []) -> Ok ()
  | (t1 :: ts1, t2 :: ts2) -> let* () = unify t1 t2 in unify_all ts1 ts2
  | _ -> Error "cannot unify different numbers of arguments"

type ctx = Ctx of core_var list         (* variables *)
                * core_cvar list        (* constructors *)
                * (core_con * int) list (* type constructors & arities *)
                * (string * ctx) list   (* modules *)
let empty_ctx = Ctx ([], [], [], [])
let lookup : string -> ctx -> core_var option =
  fun name (Ctx (vars, _, _, _)) ->
    List.find_opt (fun (Binding (name', _, _, _)) -> name = name') vars
let lookup_con : string -> ctx -> core_cvar option =
  fun name (Ctx (_, cvars, _, _)) ->
    List.find_opt (fun (CBinding (name', _, _, _, _)) -> name = name') cvars
let lookup_ty : string -> ctx -> (core_con * int) option =
  fun name (Ctx (_, _, cons, _)) ->
    List.find_opt (fun (CCon (name', _), _) -> name = name') cons
let extend : ctx -> core_var -> ctx =
  fun (Ctx (vars, cvars, cons, modules)) v -> Ctx (v :: vars, cvars, cons, modules)
let extend_con : ctx -> core_cvar -> ctx =
  fun (Ctx (vars, cvars, cons, modules)) cv -> Ctx (vars, cv :: cvars, cons, modules)
let extend_ty : ctx -> (core_con * int) -> ctx =
  fun (Ctx (vars, cvars, cons, modules)) con -> Ctx (vars, cvars, con :: cons, modules)
let extend_mod : ctx -> (string * ctx) -> ctx =
  fun (Ctx (vars, cvars, cons, modules)) m -> Ctx (vars, cvars, cons, m :: modules)
let extend_open : ctx -> string -> ctx option =
  fun (Ctx (vars, cvars, cons, modules)) name ->
    match List.find_opt (fun (name', _) -> name = name') modules with
    | None -> None
    | Some (_, Ctx (vars', cvars', cons', modules')) ->
      Some (Ctx (vars' @ vars, cvars' @ cvars, cons' @ cons, modules' @ modules))

let initial_ctx
  (next_var_id : unit -> core_var_id)
  (next_con_id : unit -> core_con_id)
=
  (* it's okay to reuse QVars for multiple variables here -
     they have the same ID, but this is only used to distinguish
     them during instantiation *)
  let a = QVar ("a", next_var_id ()) in
  let qa = a :: [] in
  let a = CQVar a in
  let rec mk_ctx callback =
    let ctx = ref empty_ctx in
    let add name qvars ty =
      ctx := extend (deref ctx) (Binding (name, next_var_id (), qvars, ty))
    in
    let add_con name qvars params result =
      ctx := extend_con (deref ctx) (CBinding (name, next_var_id (), qvars, params, result))
    in
    let add_ty name arity =
      let con = CCon (name, next_con_id ()) in
      (ctx := extend_ty (deref ctx) (con, arity); con)
    in
    let add_mod name m =
      ctx := extend_mod (deref ctx) (name, m)
    in
    (callback add add_con add_ty add_mod; deref ctx)
  in
  mk_ctx (fun add add_con add_ty add_mod ->
    let ty0 name = CTCon (add_ty name 0, [])
    and ty1 name = let c = add_ty name 1 in fun a -> CTCon (c, a :: [])
    and ty2 name = let c = add_ty name 2 in fun a b -> CTCon (c, a :: b :: [])
    in
    let (-->) = ty2 "->"
    and t_tuple = add_ty "*" (-1) (* TODO: this feels janky? *)
    and t_char = ty0 "char" and t_int = ty0 "int"
    and t_string = ty0 "string" and t_bool = ty0 "bool"
    in
    add "&&" [] (t_bool --> (t_bool --> t_bool));
    add "||" [] (t_bool --> (t_bool --> t_bool));
    add "+"  [] (t_int --> (t_int --> t_int));
    add "-"  [] (t_int --> (t_int --> t_int));
    (* TODO: make ordered comparisons int-specific *)
    add ">=" qa (a --> (a --> t_bool));
    add "<=" qa (a --> (a --> t_bool));
    add "<"  qa (a --> (a --> t_bool));
    add ">"  qa (a --> (a --> t_bool));
    add "="  qa (a --> (a --> t_bool));
    add_con "true"  [] [] t_bool;
    add_con "false" [] [] t_bool;
    add_mod "String" (mk_ctx (fun add _ _ _ ->
      add "length" [] (t_string --> t_int);
      add "get"    [] (t_string --> (t_int --> t_char));
      add "sub"    [] (t_string --> (t_int --> (t_int --> t_string)));
      ()
    ));
    let t_option = ty1 "option" in
    add_con "None" qa [] (t_option a);
    add_con "Some" qa (a :: []) (t_option a);
    let t_list = ty1 "list" in
    add "::" qa (a --> (t_list a --> t_list a));
    ()
  )

let preprocess_constructor_args
  (* TODO: move into elab once we support generalizing nested functions *)
  (instantiate : core_qvar list -> unit -> core_type -> core_type)
  (mk_tuple : 'a list -> 'a) ctx name (args : 'a list option)
  : (core_cvar * core_type list * core_type * 'a list, string) result =
  let* cv =
    match lookup_con name ctx with
    | None    -> Error ("constructor not in scope: " ^ name)
    | Some cv -> Ok cv
  in
  let CBinding (_, _, qvars, param_tys, result_tys) = cv in
  let instantiate = instantiate qvars () in
  let param_tys = List.map instantiate param_tys in
  let result_ty = instantiate result_tys in
  (* make sure we're applying the constructor to the right number of arguments.
     as a special case, passing the "wrong" number of arguments to a 1-param
     tuple, like `Some (1, 2)`, causes it to be treated as a tuple. *)
  let* args =
    let num_params = List.length param_tys in
    match (num_params, args) with
    | (0, None)              -> Ok []
    | (0, Some _)            -> Error ("constructor " ^ name ^ " must be applied to 0 arguments")
    | (_, None)              -> Error ("constructor " ^ name ^ " must be applied to some arguments")
    | (1, Some (args :: [])) -> Ok (args :: [])
    | (1, Some args)         -> Ok (mk_tuple args :: [])
    | (_, Some args)         -> if num_params = List.length args
                                then Ok args
                                else Error ("constructor " ^ name
                                            ^ " is applied to the wrong number of arguments")
  in
  Ok (cv, param_tys, result_ty, args)

let elab (ast : ast) : (core, string) result =
  let next_var_id = counter ()
  and next_uvar_name = counter ()
  and next_con_id = counter ()
  in
  let initial_ctx = initial_ctx next_var_id next_con_id in
  let (ty0, ty1, ty2) =
    let expect_arity n name =
      match lookup_ty name initial_ctx with
      | Some (c, arity) ->
        if arity = n then c
        else invalid_arg ("impossible: expected arity " ^ string_of_int n)
      | None -> invalid_arg ("impossible: no such type " ^ name)
    in
    ((fun name -> let c = expect_arity 0 name in            CTCon (c, [])),
     (fun name -> let c = expect_arity 1 name in fun a   -> CTCon (c, a :: [])),
     (fun name -> let c = expect_arity 2 name in fun a b -> CTCon (c, a :: b :: [])))
  in
  let (-->)    = ty2 "->"
  and t_tuple  = let c = fst (Option.get (lookup_ty "*" initial_ctx)) in
                 fun args -> CTCon (c, args)
  and t_char   = ty0 "char"
  and t_int    = ty0 "int"
  and t_string = ty0 "string"
  and t_bool   = ty0 "bool"
  in
  let new_uvar lvl name () : core_uvar ref =
    let id = next_uvar_name () in
    let name = match name with
               | Some n -> n
               (* TODO: do this calculation lazily? *)
               | None   -> string_of_int id
    in ref (Unknown (name, id, lvl))
  in
  let generalize (lvl : core_level) : core_type list -> core_qvar list * core_type list =
    (* TODO: we don't need to return a new type list here *)
    let rec go ty qvars =
      match ty with
      | CQVar qv -> (qvars, ty)
      | CTCon (c, tys) ->
        let (qvars, tys) = go_list tys qvars in
        (qvars, (CTCon (c, tys)))
      | CUVar r ->
        match deref r with
        | Known ty -> go ty qvars
        | Unknown (name, id, lvl') ->
          if lvl' > lvl then
            let qv = QVar (name, next_var_id ()) in
            let qvars = qv :: qvars in
            r := Known (CQVar qv);
            (qvars, CQVar qv)
          else
            (qvars, ty)
    and go_list tys qvars =
      map_m state_monad go tys qvars
    in fun tys -> go_list tys []
  in
  let instantiate lvl (qvars : core_qvar list) () : core_type -> core_type =
    let qvars = List.map (fun var -> let QVar (name, _) = var in
                                     (var, new_uvar lvl (Some name) ())) qvars in
    let rec go ty = match ty with
                    | CQVar (QVar (n, id)) -> (
                      match List.find_opt (fun (QVar (_, id'), _) -> id = id') qvars with
                      | None -> CUVar (new_uvar lvl (
                                  Some ("<error: unexpected QVar here: " ^ n ^ ">")) ())
                      | Some (_, uv) -> CUVar uv)
                    | CUVar r -> (
                      match deref r with
                      | Known ty -> go ty
                      | Unknown _ -> ty)
                    | CTCon (c, tys) -> CTCon (c, List.map go tys)
    in go
  in
  (* Elaboration of patterns requires two phases. Originally we just traversed the pattern
     and added every variable we found to the context, with a new uvar for its type.
     The reason this doesn't work is because of 'or'-patterns, which require:
     (1) the set of variables bound in both branches be the same;
     (2) the resulting context contain only one copy of the variables;
     (3) each copy of a variable in the elaborated branches refer to the same var ID.
     So instead, elaboration proceeds in three steps:
     - traverse the pattern to determine the names of all bound variables
       (and checking consistency between branches);
     - create a new Var (with ids and new uvars for types) for each bound variable;
     - traverse the pattern again, translating each identifier to its corresponding Var.
     *)
  let pat_bound_vars : core_level -> ast_pat -> (core_var string_map, string) result =
    let rec go pat =
      match pat with
      | POr (p1, p2) -> let* v1 = go p1 in
                        let* v2 = go p2 in
                        if map_eql (fun () () -> true) v1 v2 then Ok v1
                        else Error "branches do not bind the same variables"
      | PTuple ps    -> go_list ps
      | PList ps     -> go_list ps
      | PCon (_, ps) -> (match ps with | Some ps -> go_list ps
                                       | None    -> Ok map_empty)
      | PCharLit _ | PIntLit _ | PStrLit _
      | PWild        -> Ok map_empty
      | PVar v       -> Ok (map_singleton (v, ()))
      | PAsc (p, _)  -> go p
    and go_list pats =
      List.fold_left merge (Ok map_empty) (List.map go pats)
    and merge ev1 ev2 =
      let* v1 = ev1 in
      let* v2 = ev2 in
      match map_disjoint_union v1 v2 with
      | Ok v' -> Ok v'
      | Error (DupErr v) -> Error "variable bound multiple times in the same pattern: v"
    in
    fun lvl pat ->
      go pat >>= fun bindings ->
      Ok (map_map
        (fun s () -> let uv = CUVar (new_uvar lvl (Some s) ()) in
                     Binding (s, next_var_id (), [], uv)
        ) bindings)
  (* TODO: exhaustiveness checking? *)
  and infer_pat_with_vars lvl ctx (bindings : core_var string_map) :
                          ast_pat -> (core_pat * core_type, string) result =
    let rec go pat =
      match pat with
      | POr (p1, p2) -> let* (p1', ty1) = go p1 in
                        let* (p2', ty2) = go p2 in
                        let* () = unify ty1 ty2 in
                        Ok (POr (p1', p2'), ty1)
      | PCon (name, args) ->
        let* (cv, param_tys, result_ty, args) =
          preprocess_constructor_args (instantiate lvl) (fun es -> PTuple es)
                                      ctx name args
        in
        let* args' = map_m error_monad go args in
        let* () = unify_all param_tys (List.map snd args') in
        let args' = List.map fst args' in
        Ok (PCon (cv, Some args'), ground result_ty)
      | PCharLit c   -> Ok (PCharLit c, t_char)
      | PIntLit c    -> Ok (PIntLit c, t_int)
      | PStrLit c    -> Ok (PStrLit c, t_string)
      | PVar s       -> (match map_lookup s bindings with
                         | None   -> Error "impossible: we should have created suitable bindings?"
                         | Some v -> let Binding (_, _, _, ty) = v in
                                     Ok (PVar v, ty))
      | PWild        -> let ty = CUVar (new_uvar lvl None ()) in
                        Ok (PWild, ty)
      (* TODO: implement PTuple, PList, PAsc *)
    in go
  in
  let infer_pat lvl : ctx -> ast_pat -> (ctx * (core_pat * core_type), string) result =
    fun ctx pat ->
    let* bindings = pat_bound_vars lvl pat in
    let* pat' = infer_pat_with_vars lvl ctx bindings pat in
    let ctx' = map_fold_left (fun ctx (_, v) -> extend ctx v) ctx bindings in
    Ok (ctx', pat')
  in
  let infer_pats lvl : ctx -> ast_pat list -> (ctx * (core_pat * core_type) list, string) result =
    Fun.flip (map_m error_state_monad (Fun.flip (infer_pat lvl)))
  in
  let rec infer lvl : ctx -> ast_expr -> (core_expr * core_type, string) result =
    fun ctx e ->
    match e with
    | Tuple es ->
      let* elab = map_m error_monad (infer lvl ctx) es in
      Ok (Tuple (List.map fst elab),
          t_tuple (List.map snd elab))
    | List es ->
      let ty_elem = CUVar (new_uvar lvl None ()) in
      map_m error_monad (fun e ->
                          let* (e', ty_e) = infer lvl ctx e in
                          let* () = unify ty_e ty_elem in
                          Ok e'
                        ) es >>= fun es' ->
        Ok (List es', ground ty_elem)
    | Con (name, args) ->
      let* (cv, param_tys, result_ty, args) =
        preprocess_constructor_args (instantiate lvl) (fun es -> Tuple es)
                                    ctx name args
      in
      let* args' = map_m error_monad (infer lvl ctx) args in
      let* () = unify_all param_tys (List.map snd args') in
      let args' = List.map fst args' in
      Ok (Con (cv, Some args'), ground result_ty)
    | CharLit c -> Ok (CharLit c, t_char)
    | IntLit i -> Ok (IntLit i, t_int)
    | StrLit s -> Ok (StrLit s, t_string)
    | Var s -> (match lookup s ctx with
                | None -> Error ("variable not in scope: " ^ s)
                | Some v ->
                  let Binding (_, _, qvars, ty) = v in
                  let ty = instantiate lvl qvars () ty in
                  Ok (Var v, ty))
    | LetOpen (Module name, e) -> (
      match extend_open ctx name with
      | Some ctx -> infer lvl ctx e
      | None     -> Error ("module not in scope: " ^ name))
    | App (e1, e2) ->
      let* (e1', ty_fun) = infer lvl ctx e1 in
      let* (e2', ty_arg) = infer lvl ctx e2 in
      let uv = new_uvar lvl None () in
      let ty_res = CUVar uv in
      let* () = unify ty_fun (ty_arg --> ty_res) in
      Ok (App (e1', e2'), ground ty_res)
    | LetIn (bindings, e) ->
      let* (ctx', bindings') = infer_bindings lvl ctx bindings in
      let* (e', ty_e) = infer lvl ctx' e in
      Ok (LetIn (bindings', e'), ground ty_e)
    | Match (e_scrut, cases) ->
      let ty_res = CUVar (new_uvar lvl None ()) in
      let* (e_scrut', ty_scrut) = infer lvl ctx e_scrut in
      let* cases' =
        map_m error_monad
            (fun (pat, e) ->
              let* (ctx', (pat', ty_pat)) = infer_pat lvl ctx pat in
              let* ()                     = unify ty_pat ty_scrut in
              let* (e', ty_e)             = infer lvl ctx' e      in
              let* ()                     = unify ty_e ty_res     in
              Ok (pat', e'))
            cases
      in
      Ok (
        Match (e_scrut', cases'),
        ground ty_res
      )
    | IfThenElse (e1, e2, e3) ->
      let* (e1', ty_cond) = infer lvl ctx e1      in
      let* ()             = unify ty_cond t_bool  in
      let* (e2', ty_then) = infer lvl ctx e2      in
      let* (e3', ty_else) = infer lvl ctx e3      in
      let* ()             = unify ty_then ty_else in
      Ok (IfThenElse (e1', e2', e3'), ground ty_then)
    | Fun (pats, e) ->
      let* (ctx', pats') = infer_pats lvl ctx pats in
      let* (e', ty_res) = infer lvl ctx' e in
      Ok (
        Fun (List.map fst pats', e'),
        List.fold_right (fun (_, ty1) ty2 -> (ty1 --> ty2)) pats' ty_res
      )
  and infer_bindings lvl : ctx -> ast_bindings -> (ctx * core_bindings, string) result =
    fun ctx (Bindings (is_rec, bindings)) ->
    (* for each binding, determine the variables bound by the head *)
    let* bindings =
      map_m error_monad
        (fun binding ->
          let (head, _, _, _) = binding in
          let* vars = pat_bound_vars lvl head in
          Ok (vars, binding)
        ) bindings
    in
    (* combine all the bindings *)
    let* vars =
      let sets = List.map fst bindings in
      match fold_left_m error_monad map_disjoint_union map_empty sets with
      | Ok combined      -> Ok combined
      | Error (DupErr v) ->
        Error ("variable bound multiple times in a group of definitions: " ^ v)
    in
    (* the context used for the bindings contains these variables iff the binding group
       is recursive *)
    let ctx_inner = if is_rec
                    then map_fold_left (fun ctx (_, v) -> extend ctx v) ctx vars
                    else ctx
    in
    (* infer each binding *)
    let* bindings =
      map_m error_monad
        (fun (bound_vars, (head, args, annot, rhs)) ->
          let* () =
            match annot with
            | Some _ -> Error "TODO: handle recursive bindings"
            | None   -> Ok ()
          in
          let* (head', ty_head)   = infer_pat_with_vars lvl ctx bound_vars head in
          let* (ctx_inner, args') = infer_pats (lvl + 1) ctx_inner args         in
          let* (rhs', ty_rhs)     = infer      (lvl + 1) ctx_inner rhs          in
          let* ()                 =
            unify ty_head (List.fold_right
                            (fun (_, ty1) ty2 -> (ty1 --> ty2))
                            args' ty_rhs)
          in
          let args' = List.map fst args' in
          let* can_generalize =
            (* TODO: the value restriction is a little looser than this *)
            match (args, rhs) with
            | (_ :: _, _)      -> Ok true
            | ([], Fun (_, _)) -> Ok true
            | _                -> if is_rec then
                                    Error "recursive bindings cannot have side effects"
                                  else
                                    Ok false
          in
          Ok (bound_vars, can_generalize, ((head', args', None, rhs') : core_binding))
        ) bindings
    in
    let bound_vars : core_var list =
      (* flatten the maps in `bindings`; order is irrelevant, and we
         already know them to be disjoint *)
      List.fold_left (fun acc (bv, _, _) ->
        map_fold_left (fun acc (_, v) -> v :: acc) acc bv
      ) [] bindings
    in
    (* conservatively assume that we can only generalize the whole group
       of definitions if every single one meets the criteria *)
    let can_generalize =
      List.fold_left (fun acc (_, cg, _) -> acc && cg) true bindings in
    let bound_vars : core_var list =
      if not can_generalize then
        bound_vars
      else
        let types = List.map (fun (Binding (_, _, [], ty)) -> ty) bound_vars in
        let (qvars, types) = generalize lvl types in
        List.map2 (fun var ty ->
          let Binding (name, id, _, _) = var in
          (* NOTE: What's going on here? We are allocating a "new" variable,
          but giving it the same ID as the above. This is fine, because (since
          generalization mutates the types it encounters, replacing the uvars
          with qvars) the references to this variable in the rhs's will all be
          of the form:
                        Var/PVar (Binding (name, id, [], ty'))
          where ty' is equivalent to ty modulo following `Known` links.
          Thus we can feel OK about saying that these two objects are "really"
          referring to the "same" variable binding, and we are just allowing it
          to have a more polymorphic type in the subsequent context.
          However, this does feel a little inelegant, and it would be nice to
          avoid it, e.g. by making the qvar list in Binding be a ref. *)
          (* TODO: maybe trim the qvars to those which appear in the ty? *)
          Binding (name, id, qvars, ty)
        ) bound_vars types
    in
    let bindings = List.map (fun (_, _, binding) -> binding) bindings in
    Ok (
      List.fold_left extend ctx bound_vars,
      Bindings (is_rec, bindings)
    )
  in
  let* (_, ast') =
    map_m error_state_monad
        (fun decl ctx ->
          match decl with
          | Let bindings -> let* (ctx, bindings') = infer_bindings (* lvl = *) 0 ctx bindings in
                            Ok (ctx, Let bindings')
          | _            -> Error "TODO: this type of binding is not yet supported"
        ) ast initial_ctx
  in Ok ast'

let text =
  let f = In_channel.open_text "scratchpad.mini-ml" in
  let text = In_channel.input_all f in
  In_channel.close f;
  text

let ast =
  elab =<< (parse =<< lex text)

