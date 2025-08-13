type level = int
type var_id = int
type qvar = | QVar of string * var_id
type con_id = int
type con  = | CCon of string * con_id
type typ  = | CQVar of qvar
            | CUVar of uvar ref
            | CTCon of con * typ list
and  uvar = | Unknown of string * var_id * level
            | Known   of typ
and  prov = | User
            | Builtin of string (* module prefix *)
(* ordinary variable binding *)
type var  = | Binding of string    (* name in the syntax *)
                       * var_id    (* numeric ID *)
                       * prov      (* user-defined or builtin? *)
                       * qvar list (* forall parameters *)
                       * typ       (* type *)
(* constructor variable binding *)
type cvar = | CBinding of string    (* name in the syntax *)
                        * var_id    (* numeric ID *)
                        * prov      (* user-defined or builtin? *)
                        * qvar list (* forall parameters *)
                        * typ list  (* parameter types *)
                        * typ       (* return type *)

type pat      = (var, cvar, void) Common_syntax.pat
type binding  = (var, cvar, void) Common_syntax.binding
type bindings = (var, cvar, void) Common_syntax.bindings
type expr     = (var, cvar, void) Common_syntax.expr
type tydecl = | CDatatype of con * int (* arity *)
              | CAlias    of con * int (* name and arity *)
                           * qvar list (* parameters *)
                           * typ       (* definition *)
type core = bindings list
