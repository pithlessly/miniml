type cvar = string * Token.span
type typ = | TVar of string * Token.span
           | TCon of Common_syntax.mod_expr list * string * Token.span * typ list
type pat      = (string * Token.span, cvar, typ) Common_syntax.pat
type binding  = (string * Token.span, cvar, typ) Common_syntax.binding
type bindings = (string * Token.span, cvar, typ) Common_syntax.bindings
type expr     = (string * Token.span, cvar, typ) Common_syntax.expr
type record_decl
              = (string * Token.span * typ) list
type typ_decl = | Datatype of (string * typ list) list
                | Record   of record_decl
                | Alias    of typ
type decl     = | Let      of bindings
                | Types    of ( string list
                              * string
                              * typ_decl
                              ) list
                | Module   of (string * Token.span) * decl list
                | Open     of (string * Token.span)
type ast = decl list
