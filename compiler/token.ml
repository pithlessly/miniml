type span = { line_no : int }
let dummy_span = { line_no = 0 - 1 }
let describe_span (sp : span) =
  if sp.line_no = 0 - 1 then "(dummy)"
  else "(near line " ^ string_of_int sp.line_no ^ ")"

type token =
  | OpenParen
  | CloseParen
  | OpenBracket
  | CloseBracket
  | OpenBrace
  | CloseBrace
  | Dot
  | Colon
  | Comma
  | Semicolon
  | Equal
  | Pipe
  | Arrow
  | KTrue | KFalse
  | KType | KOf
  | KModule
  | KStruct | KEnd
  | KOpen
  | KLet | KRec | KAnd | KIn
  | KIf | KThen | KElse
  | KMatch | KWith
  | KFun
  | KFunction
  | KUnder
  | IdentLower of string * span
  | IdentUpper of string * span
  | IdentSymbol of string * span
  | IdentQuote of string * span
  | TkCharLit of char
  | TkIntLit of int
  | TkStrLit of string
