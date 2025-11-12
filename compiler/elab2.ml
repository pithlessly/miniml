open Util
open Common_syntax

(* ========== The type language of Fω and 1ML ========== *
 * Note: we use 「...」 to note correspondences to 1ML.  *)

type span = Token.span
let err_sp = Token.err_sp

type level = int
type tvar_id = int (* ID of a type variable *)
type var_id = int (* ID of a value-level variable *)

(* Expresses that the first component should be seen as containing
   variables which should be considered bound in the second component. *)
type ('a, 'b) binder = 'a * 'b

(* an Fω kind 「κ」 *)
type kind = | KType | KFun of kind * kind

(* bound/abstract/nominal type variable 「α」 *)
type tvar = {
  name : string;
  id : var_id;
  kind : kind;
  info : tvar_info;
}
and tvar_info =
  (* this type variable is bound, abstract, or primitive *)
  | IOpaque
  (* this type variable is a proxy for a particular module variable in scope *)
  | IReflects of var
  (* this type variable represents a datatype constructor *)
  | IDatatype of level * (tvar list, (string * typ list) list) binder

(* source-level variable *)
and var = {
  name : string;
  id : var_id;
  typ : typ;
}

(* a semantic type 「Σ」 *)
and typ =
  | TPath   of typ_path
  | TTuple  of small_typ list
  | TSing   of signat
  | TStruct of (string * typ) list
  (* we use slightly different terminology for function types
     because what 1ML calls "purity" is actually the stronger
     property of _phase separability_. *)
  | TAFun   of (tvar list, typ *          typ) binder (*      auto function type 「η=A」 *)
  | TSFun   of (tvar list, typ *          typ) binder (*    static function type 「η=P」 *)
  | TEFun   of (tvar list, typ * eff * signat) binder (* effectful function type 「η=І」 *)
  | TUVar   of uvar

(* a semantic small type 「σ」 *)
and small_typ = typ

(* a semantic signature 「Ξ」 *)
and signat = (tvar list, typ) binder

(* a path 「π」 *)
and typ_path = tvar * small_typ list

(* an effect (a variable denoting an expression of type `effect`) *)
and eff = typ

(* a unification variable 「υ」 *)
and uvar = ucell ref
and ucell =
  | Unknown of string * span * var_id * level
  | Known   of typ

type show_s = string list -> string list

let show_paren : bool -> show_s -> show_s
  = function
    | false -> fun sh -> sh
    | true  -> fun sh acc -> "(" :: sh (")" :: acc)

let rec show_kind head = function
  | KType         -> fun acc -> "Ω" :: acc
  | KFun (k1, k2) -> show_paren head
                     (fun acc -> show_kind true k1 (" -> " :: show_kind false k2 acc))

let show_tvar_occurrence : tvar -> show_s =
  fun { name; id; _ } acc -> name :: "/" :: string_of_int id :: acc

and show_var_occurrence : var -> show_s =
  fun { name; id; _ } acc -> name :: "/" :: string_of_int id :: acc

let show_tvar_binder : tvar -> show_s =
  fun { name; id; kind; info } acc ->
    name :: "/" :: string_of_int id :: " : " ::
    show_kind false kind
    (match info with
     | IOpaque -> acc
     | IReflects v -> " ~ " :: show_var_occurrence v acc
     | IDatatype (_, _) -> " = <datatype>" :: acc)

let show_tvar_binders : tvar list -> show_s =
  List.fold_right (fun tv acc ->
                    " (" :: show_tvar_binder tv (")" :: acc))

let show_quantifier : string -> tvar list -> show_s =
  fun sym tvs acc ->
    match tvs with
    | [] -> acc
    | _  -> sym :: show_tvar_binders tvs (". " :: acc)

let rec show_sig : signat -> show_s =
  fun (tvs, ty) acc ->
    show_quantifier "∃" tvs (show_typ false ty acc)

and show_typ (atomic : bool) : typ -> show_s =
  function
  | TPath (p_head, p_args) -> fun acc ->
      show_tvar_occurrence p_head
      (List.fold_right (fun arg acc -> " " :: show_typ true arg acc) p_args acc)
  | TTuple tys -> fun acc ->
      "(" ::
      snd (List.fold_right (fun ty (sep, acc) ->
                             (" * ", show_typ false ty (sep :: acc)))
                           tys ("", ")" :: acc))
  | TSing sg -> fun acc ->
      "[= " :: show_sig sg ("]" :: acc)
  | TStruct fs -> fun acc ->
      "{" ::
      snd (List.fold_right (fun (name, ty) (sep, acc) ->
                             ("; ", name :: " : " :: show_typ false ty (sep :: acc)))
                           fs ("", "}" :: acc))
  | TAFun (tvs, (ty1, ty2)) ->
      show_paren atomic (fun acc ->
        show_quantifier "∀" tvs
        ("'" :: show_typ true ty1 (" => " :: show_typ false ty2 acc)))
  | TSFun (tvs, (ty1, ty2)) ->
      show_paren atomic (fun acc ->
        show_quantifier "∀" tvs
        (show_typ true ty1 (" => " :: show_typ false ty2 acc)))
  | TEFun (tvs, (ty1, eff, sg2)) ->
      show_paren atomic (fun acc ->
        show_quantifier "∀" tvs
        (show_typ true ty1 (" -> [" :: show_eff eff ("] " :: show_sig sg2 acc))))
  | TUVar uv ->
      match deref uv with
      | Known typ -> show_typ atomic typ
      | Unknown (name, _, id, level) -> fun acc ->
          "?" :: name :: "/" :: string_of_int id :: "@" :: string_of_int level :: acc

and show_eff : eff -> show_s =
  fun eff -> show_typ false eff

let show_var_binder : var -> show_s =
  fun { name; id; typ } acc ->
    name :: "/" :: string_of_int id :: " : " ::
      show_typ false typ acc

(* ========== Contexts ========== *)

module Ctx = struct

  type ctx = {
    num_tvars : int;
    tvars : tvar list;
    (* In the core calculus, value-, module-, and type-level variables
       all range over the same sort of thing (an expression).
       We distinguish them in the context only because they are separate namespaces in OCaml. *)
    vars  : var list;
    tcons : var list;
    mods  : var list;
  }
  type t = ctx

  let empty = { num_tvars = 0; tvars = []; vars = []; tcons = []; mods = [] }
  let extend_tvar tv { num_tvars; tvars; vars; tcons; mods } = { num_tvars = num_tvars + 1; tvars = tv :: tvars; vars; tcons; mods }
  let extend_var  x  { num_tvars; tvars; vars; tcons; mods } = { num_tvars; tvars; vars = x :: vars; tcons; mods }
  let extend_tcon tc { num_tvars; tvars; vars; tcons; mods } = { num_tvars; tvars; vars; tcons = tc :: tcons; mods }

  let dump (ctx : ctx) : unit =
    let print line = Miniml.debug (fun () -> line) in
    print "===== tyvars             =====";
    List.iter (fun line -> print (String.concat "" line))
      (List.mapi (fun i tv -> string_of_int i :: " " :: show_tvar_binder tv []) ctx.tvars);
    print "===== variables          =====";
    List.iter (fun v -> print (String.concat "" (show_var_binder v []))) ctx.vars;
    print "===== type constructors  =====";
    List.iter (fun v -> print (String.concat "" (show_var_binder v []))) ctx.tcons;
    print "===== modules            =====";
    List.iter (fun v -> print (String.concat "" (show_var_binder v []))) ctx.mods;
    ()

end

(* ========== Elaborator bootstrapping ========== *)

let next_tvar_id = counter ()
and next_var_id = counter ()

let kind_spine : kind -> kind * kind snoc =
  let rec go ks = function
    | KFun (k1, k2) -> go (Snoc (ks, k1)) k2
    | k             -> (k, ks)
  in go Nil

let new_opaque_tvar (name : string) (kind : kind) () : tvar =
  { name; id = next_var_id (); kind; info = IOpaque }

let new_primitive (name : string) (kind : kind) () : tvar * var =
  let tv = new_opaque_tvar name kind () in
  let typ : typ =
    match kind_spine kind with
    | (KType, arg_kinds) ->
        let arg_vars =
          Snoc.to_list arg_kinds
          |> List.mapi (fun i k -> new_opaque_tvar ("a" ^ string_of_int i) k ())
        in
        let rec build_function_type (tvars_to_bind : tvar list)
                                    (path_args : small_typ snoc)
                                    (tvars_remaining : tvar list) : typ
        = match tvars_remaining with
          | [] -> TSing ([], TPath (tv, Snoc.to_list path_args))
          | tv :: tvs ->
              let arg_ty = TPath (tv, []) in
              (* We create a nested sequence of `TSFun` constructors, but all the tvars
                 are bound in the outermost constructor.
                 It is possible for there to be no outermost `TSFun` constructor,
                 but only if `arg_vars` is empty, in which case `tvars_to_bind` is also empty. *)
              TSFun (tvars_to_bind,
                     (TSing ([], arg_ty),
                      build_function_type [] (Snoc (path_args, arg_ty)) tvs))
        in build_function_type arg_vars Nil arg_vars
    | _ -> invalid_arg "invalid kind head structure"
  in
  let v : var  = { name; id = next_var_id (); typ } in
  (tv, v)

(* ========== The initial context & primitive types ========== *)

let ctx = Ctx.empty

let (tv_int, v_int) = new_primitive "int" KType ()
let ctx = ctx |> Ctx.extend_tvar tv_int
              |> Ctx.extend_tcon v_int
let (tv_string, v_string) = new_primitive "string" KType ()
let ctx = ctx |> Ctx.extend_tvar tv_string
              |> Ctx.extend_tcon v_string
let (tv_char, v_char) = new_primitive "char" KType ()
let ctx = ctx |> Ctx.extend_tvar tv_char
              |> Ctx.extend_tcon v_char

let () = Ctx.dump ctx

(* type 'a elab = *)
