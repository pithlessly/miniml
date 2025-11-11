open Util
open Token

(* character properties *)
let lower_letter c = Char.('a' <= c && c <= 'z')
let lower c = lower_letter c || c = '_'
let upper c = Char.('A' <= c && c <= 'Z')
let numer c = Char.('0' <= c && c <= '9')
let ident c = upper c || lower c || numer c || c = '\''
let symbolic = function | '!' | '&' | '*' | '+' | '-' | '.' | ':'
                        | '<' | '>' | '=' | '^' | '|' | '@' | '/' -> true
                        | _ -> false

let lex str =
  (* main logic *)
  let latest_line = ref 1
  and latest_idx = ref (0 - 1) in
  let char =
    let length = String.length str in
    fun i ->
    if i < length then
      let c = String.get str i in
      (if i > deref latest_idx then
        if i <> deref latest_idx + 1 then
          invalid_arg "lexer did not access tokens consecutively"
        else
          (latest_idx := i;
           if c = '\n' then latest_line := deref latest_line + 1 else ())
       else ());
      Some c
    else None
  in
  let rec go i tokens =
    let adv t = go (i + 1) (Snoc (tokens, t)) in
    let take_range d (included : char -> bool) (mk_tok : span -> string -> token) =
      let rec scan d = match char (i + d) with
                       | Some c -> if included c then scan (d + 1) else d
                       | None -> d
      in
      let d = scan d in
      let span = { line_no = deref latest_line } in
      go (i + d) (Snoc (tokens, mk_tok span (String.sub str i d)))
    in
    match char i with
    | Some '\n'
    | Some '\r'
    | Some ' ' -> go (i + 1) tokens
    | Some '"' ->
      let rec scan i parts escaped =
        match (char i, escaped) with
        | (None, _) -> Error (E "expected trailing quote for string literal, got EOF")
        | (Some '"',  false) -> Ok (i + 1, TkStrLit (String.concat "" (Snoc.to_list parts)))
        | (Some '\\', false) -> scan (i + 1) parts true
        | (Some c,    false) -> scan (i + 1) (Snoc (parts, String.make 1 c)) false
        | (Some '"',  true)  -> scan (i + 1) (Snoc (parts, "\"")) false
        | (Some '\\', true)  -> scan (i + 1) (Snoc (parts, "\\")) false
        | (Some 'n',  true)  -> scan (i + 1) (Snoc (parts, "\n")) false
        | (Some 'r',  true)  -> scan (i + 1) (Snoc (parts, "\r")) false
        | (Some _,    true)  -> Error (E "invalid escape sequence in string literal")
      in
      (match scan (i + 1) Nil false with
       | Error e -> Error e
       | Ok (i, tok) -> go i (Snoc (tokens, tok)))
    | Some '\'' ->
      let char_done c i =
        match char i with
        | None -> Error (E "expected trailing quote for character literal, got EOF")
        | Some '\'' -> go (i + 1) (Snoc (tokens, TkCharLit c))
        | Some _ -> if lower c then take_range 1 ident (fun sp s -> IdentQuote (s, sp))
                    else Error (E "unterminated character literal")
      in
      (match char (i + 1) with
       | Some '\\' ->
         (match char (i + 2) with
          | Some 'n' -> char_done '\n' (i + 3)
          | Some 'r' -> char_done '\r' (i + 3)
          | Some '\\' -> char_done '\\' (i + 3)
          | Some '\'' -> char_done '\'' (i + 3)
          | _ -> Error (E "invalid escape sequence in character literal"))
       | Some c -> char_done c (i + 2)
       | _ -> Error (E "malformed character literal"))
    | Some '(' ->
      (match char (i + 1) with
       | Some '*' ->
           let rec scan i =
             match (char i, char (i + 1)) with
             | (Some '*', Some ')') -> go (i + 2) tokens
             | (Some _,   _       ) -> scan (i + 1)
             | (None,     _       ) -> Error (E "got EOF while scanning comment")
           in scan (i + 2)
       | _        -> adv OpenParen)
    | Some ')' -> adv CloseParen
    | Some '[' -> adv OpenBracket
    | Some ']' -> adv CloseBracket
    | Some '{' -> adv OpenBrace
    | Some '}' -> adv CloseBrace
    | Some ',' -> adv Comma
    | Some ';' -> adv Semicolon
    | Some c ->
      let mk_lower_ident sp =
        function
        | "true" -> KTrue | "false" -> KFalse
        | "type" -> KType | "of" -> KOf
        | "module" -> KModule
        | "struct" -> KStruct | "end" -> KEnd
        | "open" -> KOpen
        | "let" -> KLet | "rec" -> KRec
        | "and" -> KAnd | "in" -> KIn
        | "if" -> KIf | "then" -> KThen | "else" -> KElse
        | "match" -> KMatch | "with" -> KWith
        | "fun" -> KFun
        | "function" -> KFunction
        | "_" -> KUnder
        | s -> IdentLower (s, sp)
      in
      let mk_symbolic_ident sp =
        function
        | "."  -> Dot
        | ":"  -> Colon
        | "="  -> Equal
        | "|"  -> Pipe
        | "->" -> Arrow
        | s    -> IdentSymbol (s, sp)
      in
      if upper c then take_range 0 ident (fun sp s -> IdentUpper (s, sp)) else
      if lower c then take_range 0 ident mk_lower_ident else
      if numer c then take_range 0 numer (fun _ s -> TkIntLit (int_of_string s)) else
      if symbolic c then take_range 0 symbolic mk_symbolic_ident else
        Error (E ("unexpected character: " ^ String.make 1 c
                  ^ " at position: " ^ string_of_int i))
    | None -> Ok (Snoc.to_list tokens)
  in
  go 0 Nil
