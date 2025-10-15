open Util
open Common_syntax
open Core

module Purity = struct
  (* description of the side effects associated with a piece of code *)
  type t =
    | Pure   (* no side effects and can be copied arbitrarily (e.g. 1, x) *)
    | Affine (* can be deleted but should not be copied (e.g. ref 2) *)
    | Impure (* has side effects, should only be emitted once *)

  let merge p1 p2 =
    match (p1, p2) with
    | (Impure, _) | (_, Impure) -> Impure
    | (Affine, _) | (_, Affine) -> Affine
    | (Pure, Pure)              -> Pure

  (* we can't use writer_monad here because of the value restriction *)
  let monad =
    let pure = fun x -> (Pure, x)
    and (>>=) x f = writer_bind merge x f
    in (pure, (>>=))
end

type should_inline = bool

type js_var = string * int

type js_expr =
  | JUnit (* can be anything *)
  | JStr    of string
  | JVar    of js_var
  | JConcat of js_expr list
  | JApply  of js_expr * js_expr list
  | JLam    of should_inline * js_var list * js_expr
  | JArray  of js_expr list

type js_stmt =
  | JExpr  of js_expr
  | JLet   of js_var list
  | JLetEq of js_var * js_expr

let js_null  = JStr "null"
let js_true  = JStr "true"
let js_false = JStr "false"

type constructor_layout =
  | LayoutTagged of string
  | LayoutUntagged
  | LayoutNewtype

type subst = js_expr IntMap.t
           * constructor_layout IntMap.t

let escape = function
  | '\n' -> "\\n"
  | '\r' -> "\\r"
  | '\\' -> "\\\\"
  | c    -> let code = int_of_char c in
            if 32 <= code && code < 128 then
              String.make 1 c
            else
              invalid_arg ("we don't yet support this character code: " ^ string_of_int code)

let gen_str s = "\"" ^ string_flat_map escape s ^ "\""

let go_char c = JStr ("\"" ^ escape c ^ "\"")
and go_int n = JStr (string_of_int n)
and go_str s = JStr (gen_str s)

let go_var ((vsub, _) : subst) : var -> js_expr =
  fun (Binding (_, id, _, _, _)) ->
    Option.unwrap (IntMap.lookup id vsub)

let go_cvar ((_, csub) : subst) : cvar -> constructor_layout =
  fun (CBinding (_, id, _, _, _, _)) ->
    Option.unwrap (IntMap.lookup id csub)

let safe_in_js_identifiers = function
  | '\'' -> false
  | _    -> true

let add_unbound_var : var -> subst -> subst * js_var =
  fun (Binding (name, id, _, _, _)) (vsub, csub) ->
  let var = (String.filter safe_in_js_identifiers name, id) in
  let vsub' = IntMap.insert id (JVar var) vsub in
  ((vsub', csub), var)

let tmp_var (elab : Elab.elaborator) : js_var =
  let id = Elab.next_var_id elab in
  ("$" ^ string_of_int id, id)

let rec go_expr (sub : subst) : expr -> Purity.t * js_expr = function
  | Tuple [] -> (Purity.Pure, JUnit)
  | Tuple es ->
      let (p, es') = map_m Purity.monad (go_expr sub) es in
      (Purity.merge Purity.Affine p, JArray es')
  | List es ->
      let (p, es') = map_m Purity.monad (go_expr sub) es in
      let e' = List.fold_right (fun e acc -> JArray (e :: acc :: [])) es' js_null in
      (Purity.merge Purity.Affine p, e')
  | Con (c, es) ->
      let es = Option.unwrap es in
      (
        match go_cvar sub c with
        | LayoutTagged tag ->
            let tag = go_str tag in
            let (p, es') = map_m Purity.monad (go_expr sub) es in
            (Purity.merge Purity.Affine p, JArray (tag :: es'))
        | LayoutUntagged ->
            let (p, es') = map_m Purity.monad (go_expr sub) es in
            (Purity.merge Purity.Affine p, JArray es')
        | LayoutNewtype ->
            go_expr sub (list_unwrap es)
      )
  | CharLit c -> (Purity.Pure, go_char c)
  | IntLit i  -> (Purity.Pure, go_int i)
  | StrLit s  -> (Purity.Pure, go_str s)
  | Var v     -> (Purity.Pure, go_var sub v)

and go_bindings (sub : subst) : bindings -> js_stmt list =
  (* TODO: as with the Scheme backend --
     if the bindings aren't recursive, we don't have to forward declare these like this *)
  fun (Bindings (_, bs)) ->
  let locals : var list = List.concat_map (fun (p, _, _, _) -> Elab.pat_local_vars p) bs in
  let (sub, (locals : js_var list)) = map_m state_monad add_unbound_var locals sub in
  let declarations_of_new_variables = JLet locals in
  declarations_of_new_variables :: []

let build_output : js_expr -> string = fun top_level_expr ->
  let parts = ref [] in
  let emit str =
    let ps = deref parts in
    parts := (str :: ps)
  in
  let emit_var (name, _) = emit name in
  let comma_separated emitter = function
    | [] -> ()
    | x1 :: xs ->
      emitter x1;
      List.iter (fun x ->
        emit ", ";
        emitter x
      ) xs
  in
  let rec go = function
    | JUnit -> emit "0"
    | JStr s -> emit s
    | JVar v -> emit_var v
    | JConcat es -> List.iter go es
    | JApply (f, xs) ->
        (* TODO: don't always put parens around the function *)
        emit "(";
        go f;
        emit ")(";
        comma_separated go xs;
        emit ")"
    | JLam (_, vars, body) ->
        (* TODO: don't always put parens around the argument list *)
        emit "(";
        comma_separated emit_var vars;
        emit ") => ";
        go body
    | JArray es ->
        emit "[";
        comma_separated go es;
        emit "]"
  in
  go top_level_expr;
  String.concat "" (List.rev (deref parts))

let js (_ : Elab.elaborator) (decls : core) = ""

let () = Compile.add_backend "nodejs" js
