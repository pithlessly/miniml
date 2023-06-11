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
  let lower c = ('a' <= c && c <= 'z') || c = '_' in
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
    | Some '(' -> adv OpenParen
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
                                | "." -> Dot
                                | ":" -> Colon
                                | "=" -> Equal
                                | "|" -> Pipe
                                | _ -> IdentSymbol s
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

type ('ty_id, 'ty_var) typ =
  | TVar of 'ty_var
  | TCon of 'ty_id * ('ty_id, 'ty_var) typ list

type ('val_id, 'ty_id, 'ty_var) expr =
  | Tuple of ('val_id, 'ty_id, 'ty_var) expr list
  | App of ('val_id, 'ty_id, 'ty_var) expr
         * ('val_id, 'ty_id, 'ty_var) expr
  | CharLit of char
  | IntLit of int
  | StrLit of string
  | Var of 'val_id

type ('val_id, 'ty_id, 'ty_var) pat =
  | PVar of 'val_id

type ('val_id, 'ty_id, 'ty_var) decl =
  | Datatype of 'ty_var list * 'ty_id * ('val_id * ('ty_id, 'ty_var) typ list) list
  | Alias    of 'ty_var list * 'ty_id * ('ty_id, 'ty_var) typ
  | Let      of bool                                (* rec? *)
              * ( ('val_id, 'ty_id, 'ty_var) pat      (* head pattern *)
                * ('val_id, 'ty_id, 'ty_var) pat list (* argument patterns *)
                * ('val_id, 'ty_id, 'ty_var) expr     (* RHS *)
                ) list                              (* joined by 'and' *)

type ast_typ = (string, string) typ
type ast_pat = (string, string, string) pat
type ast_expr = (string, string, string) expr
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
    | ([x],     [])         -> (x, [], [])
    | (x :: xs, o :: opers) ->
      let (o_prec, assoc) = operator_info o in
      if o_prec < prec then
        (x, xs, o :: opers)
      else begin
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
          let (args, xs, opers) = walk_nary [x] xs opers in
          go prec (f (List.rev args) :: xs) opers
      end
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

let parse_decls: token list -> (ast, string) result =
  (* parsing specific tokens *)
  let ty_params: string list parser =
    fun input k ->
    match input with
    | IdentQuote v :: input -> k input [v] (* single variable *)
    | OpenParen :: IdentQuote v1 :: input ->
      let rec go input vs = match input with
                            | Comma :: IdentQuote v :: input -> go input (v :: vs)
                            | CloseParen :: input -> k input (List.rev vs)
                            | _ -> Error "couldn't finish parsing type parameter list"
      in go input [v1]
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
      | IdentQuote v :: input -> k input [TVar v]
      | IdentLower v :: input -> k input [TCon (v, [])]
      | OpenParen :: input ->
        let rec go input ts =
          match input with
          | Comma :: input -> ty input (fun input t -> go input (t :: ts))
          | CloseParen :: input -> k input (List.rev ts)
          | _ -> Error "couldn't finish parsing type argument list"
        (* artificially prepend "," to the input stream
           to simplify the parsing here *)
        in go (Comma :: input) []
      | _ -> Error "couldn't start parsing a type"
    in
    fun input k ->
    (* parse out all suffixed type constructors *)
    let rec go input params =
      match input with
      | IdentLower v :: input -> go input [TCon (v, params)]
      | _ -> match params with
             | [] -> invalid_arg "should be impossible"
             | [t] -> k input t
             | _ -> Error "you may have been trying to use Haskell tuple syntax"
    in ty_base input go
  and ty: ast_typ parser =
    fun input k ->
    let rec go input ty_operands ty_operators =
      ty_atomic input (fun input operand ->
      let ty_operands = operand :: ty_operands in
      match input with
      | IdentSymbol op :: input ->
        (match op with
         | "->" | "*" ->
           let ty_operators = op :: ty_operators in
           go input ty_operands ty_operators
         | _ -> Error ("invalid type operator: " ^ op))
      | _ ->
        let ty_expr: ast_typ =
          resolve_precedence
            (List.rev ty_operands)
            (List.rev ty_operators)
            (fun op ->
              match op with
              | "->" -> (0, AssocRight (fun l r -> TCon ("->", [l; r])))
              | "*"  -> (1, AssocNone (fun ts -> TCon ("*", ts)))
              | _    -> invalid_arg "should be impossible")
        in k input ty_expr)
    in go input [] []
  in
  let ty_decl: (string list -> string -> ast_decl) parser =
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
        | _ -> k input (fun vars name -> Datatype (vars, name, List.rev cs))
      in adt_constructors input []
    | _ ->
      ty input (fun input t ->
      k input (fun vars name -> Alias (vars, name, t)))
  in

  let is_rec : bool parser =
    fun input k ->
    match input with | KRec :: input -> k input true
                     | _             -> k input false
  in

  let equal : unit parser =
    fun input k ->
    match input with | Equal :: input -> k input ()
                     | _ -> Error "expected '='"
  in

  let pattern : ast_pat option parser =
    fun input k ->
    match input with | IdentLower s :: input -> k input (Some (PVar s))
                     | _                     -> k input None
  in

  let rec expr0 : ast_expr option parser = fun input k ->
    match input with
    (* TODO: handle 'let', 'match', 'function', 'fun' *)
    | _ -> expr1 input k
  and expr1 = fun input k ->
    expr2 input (fun input first_operand_opt ->
    match first_operand_opt with
    | None -> k input None
    | Some first_operand ->
      (* parse an operator and the RHS operand *)
      let next_operand: (string * ast_expr) option parser =
        fun input k ->
        let continue input s = force_expr input (fun input operand ->
                                                 k input (Some (s, operand))) in
        match input with
        | Comma         :: input -> continue input ","
        | IdentSymbol s :: input -> continue input s
        (* TODO: semicolon handling is weird, because the meaning
           depends on the context. For example:
             [1; let x = 2 in x; 3]
           is parsed as
             [1; (let x = 2 in (x; 3))] = [1; 3]
           . It can't be properly handled as an operator.
         *)
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
    expr3 input (fun input head_exp_opt ->
    match head_exp_opt with
    | None -> k input None
    | Some head_exp ->
      many expr3 input (fun input arg_exps ->
      let applications = List.fold_left (fun f x -> App (f, x)) head_exp arg_exps in
      k input (Some applications)))
  and expr3 = fun input k ->
    match input with
    | CharLit c    :: input -> k input (Some (CharLit c))
    | IntLit i     :: input -> k input (Some (IntLit i))
    | StrLit s     :: input -> k input (Some (StrLit s))
    | IdentLower s :: input -> k input (Some (Var s))
    | OpenParen    :: input ->
      force_expr input (fun input e ->
      match input with
      | CloseParen :: input -> k input (Some e)
      | _ -> Error "expected ')'")
    | _ -> k input None
  and force_expr input k = force "Expected expression" expr0 input k in

  let decls input k =
    let rec go input decls =
      match input with
      | KType :: input ->
        let p' =
          seq (ty_params @> ty_name @> ty_decl @>
          fin (fun vars name mk_decl -> mk_decl vars name))
        in p' input (fun input decl -> go input (decl :: decls))
      | KLet :: input ->
        let p' =
          seq (is_rec @>
               force "expected function name or pattern" pattern @>
               many pattern @>
               equal @>
               force_expr @>
          fin (fun is_rec head_pat arg_pats () rhs -> Let (is_rec, [(head_pat, arg_pats, rhs)])))
        in p' input (fun input decl -> go input (decl :: decls))
      | _ -> k input (List.rev decls)
    in go input []
  in

  fun tokens ->
  decls tokens (fun remaining ds ->
  match remaining with | [] -> Ok ds
                       | _ -> Error "unexpected tokens at EOF")

let tokens =
  let f = In_channel.open_text "main.ml" in
  let text = In_channel.input_all f in
  In_channel.close f;
  lex text

let ast =
  let (=<<) f x = match x with | Ok a -> f a | Error e -> Error e in
  parse_decls =<<
    lex "type ('u, 'v) s = 'a
         type t = | K of (s * s)
         type q = a -> b -> c
         let rec f x = (1+x)"
