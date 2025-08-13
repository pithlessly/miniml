type span = | LineNo of int
let dummy_span = LineNo (0 - 1)
let describe_span (LineNo n) =
  if n = 0 - 1 then "(dummy)"
  else "(near line " ^ string_of_int n ^ ")"

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
