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
                                | '<' | '>' | '=' | '^' | '|' -> true
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

type (         'ty_id, 'ty_var) typ      = | TVar of 'ty_var
                                           | TCon of 'ty_id * ('ty_id, 'ty_var) typ list
type ('val_id, 'ty_id, 'ty_var) typ_decl = | Datatype of ('val_id * ('ty_id, 'ty_var) typ list) list
                                           | Alias    of ('ty_id, 'ty_var) typ
type ('val_id, 'ty_id, 'ty_var) pat      = | POr      of ('val_id, 'ty_id, 'ty_var) pat
                                                       * ('val_id, 'ty_id, 'ty_var) pat
                                           | PTuple   of ('val_id, 'ty_id, 'ty_var) pat list
                                           | PList    of ('val_id, 'ty_id, 'ty_var) pat list
                                           | PCon     of 'val_id
                                                       * ('val_id, 'ty_id, 'ty_var) pat list option
                                           | PCharLit of char
                                           | PIntLit  of int
                                           | PStrLit  of string
                                           | PVar     of 'val_id
                                           | PAsc     of ('val_id, 'ty_id, 'ty_var) pat
                                                       * (         'ty_id, 'ty_var) typ
                                           | PWild
type ('val_id, 'ty_id, 'ty_var) binding  =   ('val_id, 'ty_id, 'ty_var) pat        (* head pattern *)
                                           * ('val_id, 'ty_id, 'ty_var) pat list   (* argument patterns *)
                                           * (         'ty_id, 'ty_var) typ option (* return type annotation *)
                                           * ('val_id, 'ty_id, 'ty_var) expr       (* RHS *)
and  ('val_id, 'ty_id, 'ty_var) bindings = | Bindings of bool (* recursive? *)
                                                       * ('val_id, 'ty_id, 'ty_var) binding list
and  ('val_id, 'ty_id, 'ty_var) expr     = | Tuple      of ('val_id, 'ty_id, 'ty_var) expr list
                                           | List       of ('val_id, 'ty_id, 'ty_var) expr list
                                           | Con        of 'val_id
                                                         * ('val_id, 'ty_id, 'ty_var) expr list option
                                           | CharLit    of char
                                           | IntLit     of int
                                           | StrLit     of string
                                           | Var        of 'val_id
                                           | LetOpen    of ('val_id, 'ty_id, 'ty_var) mod_expr
                                                         * ('val_id, 'ty_id, 'ty_var) expr
                                           | App        of ('val_id, 'ty_id, 'ty_var) expr
                                                         * ('val_id, 'ty_id, 'ty_var) expr
                                           | LetIn      of ('val_id, 'ty_id, 'ty_var) bindings
                                                         * ('val_id, 'ty_id, 'ty_var) expr
                                           | Match      of ('val_id, 'ty_id, 'ty_var) expr
                                                         * ( ('val_id, 'ty_id, 'ty_var) pat
                                                           * ('val_id, 'ty_id, 'ty_var) expr
                                                           ) list
                                           | IfThenElse of ('val_id, 'ty_id, 'ty_var) expr
                                                         * ('val_id, 'ty_id, 'ty_var) expr
                                                         * ('val_id, 'ty_id, 'ty_var) expr
                                           | Fun        of ('val_id, 'ty_id, 'ty_var) pat list
                                                         * ('val_id, 'ty_id, 'ty_var) expr
and  ('val_id, 'ty_id, 'ty_var) mod_expr = | Module of string (* FIXME: change to use 'val_id? *)
type ('val_id, 'ty_id, 'ty_var) decl     = | Let      of ('val_id, 'ty_id, 'ty_var) bindings
                                           | Types    of ( 'ty_var list
                                                         * 'ty_id
                                                         * ('val_id, 'ty_id, 'ty_var) typ_decl
                                                         ) list

type ast_typ = (string, string) typ
type ast_pat = (string, string, string) pat
type ast_binding = (string, string, string) binding
type ast_bindings = (string, string, string) bindings
type ast_expr = (string, string, string) expr
type ast_typ_decl = (string, string, string) typ_decl
type ast_decl = (string, string, string) decl
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

let parse_decls: token list -> (ast, string) result =
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
    | CharLit c    :: input -> k input (Some (PCharLit c))
    | IntLit i     :: input -> k input (Some (PIntLit i))
    | StrLit s     :: input -> k input (Some (PStrLit s))
    | IdentLower s :: input -> k input (Some (PVar s))
    | KUnder       :: input -> k input (Some PWild)
    | OpenBracket :: CloseBracket
                   :: input -> k input (Some (PList []))
    | OpenBracket  :: _     -> Error "only empty list literals are supported"
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

let text =
  let f = In_channel.open_text "scratchpad.mini-ml" in
  let text = In_channel.input_all f in
  In_channel.close f;
  text

let ast =
  let (=<<) f x = match x with | Ok a -> f a | Error e -> Error e in
  parse_decls =<<
    lex text

