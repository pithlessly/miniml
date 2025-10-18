type level = int
type var_id = int
type qvar = { name : string;
              id : var_id }
type con_id = int
type prov = | User
            | Builtin of string (* module prefix *)

(* ordinary variable binding *)
type var  = {
              name : string;
              id : var_id;
              provenance : prov;
              type_params : qvar list;
              ty : typ;
            }
(* constructor variable binding *)
and  cvar = {
              name : string;
              id : var_id;
              provenance : prov;
              type_params : qvar list;
              param_tys : typ list;
              adt_ty : typ;
            }
(* field binding *)
and  field = {
              name : string;
              id : var_id;
              position : int;
              type_params : qvar list;
              record_ty : typ;
              field_ty : typ;
             }
and  typ  = | CQVar of qvar
            | CUVar of uvar ref
            | CTCon of con * typ list
and  uvar = | Unknown of string * var_id * level
            | Known   of typ
and  con  = {
              name : string;
              id : con_id;
              arity : int;
              info : con_info;
            }
and  con_info =
            | CIAlias
            | CIDatatype
            | CIRecord of field list ref

type pat      = (var, cvar, field, void) Common_syntax.pat
type binding  = (var, cvar, field, void) Common_syntax.binding
type bindings = (var, cvar, field, void) Common_syntax.bindings
type expr     = (var, cvar, field, void) Common_syntax.expr
type tydecl = | CNominal  of con
              | CAlias    of con
                           * qvar list (* parameters *)
                           * typ       (* definition *)
type core = bindings list
