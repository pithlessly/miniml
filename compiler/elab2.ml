open Util
open Common_syntax

type span = Token.span
let err_sp = Token.err_sp

(* Throughout, we use 「...」 to note correspondences to 1ML. *)

(* ========== The type language of Fω and 1ML ========== *)

type level = int
type tvar_id = int (* ID of a type variable *)
type uvar_id = int (* ID of a uvar *)
type var_id = int (* ID of a value-level variable *)

(* Expresses that the first component should be seen as containing
   variables which should be considered bound in the second component. *)
type ('a, 'b) binder = 'a * 'b

(* an Fω kind 「κ」 *)
type kind = | Type | Fun of kind * kind

(* bound/abstract/nominal type variable 「α」 *)
type tvar = {
  name : string;
  id : var_id;
  kind : kind;
  info : tvar_info;
}
and tvar_info =
  (* this type variable is bound, abstract, or primitive *)
  | Opaque
  (* this type variable is a proxy for a particular module variable in scope *)
  | Reflects of var
  (* this type variable represents a datatype constructor *)
  | Datatype of level * (tvar list, (string * typ list) list) binder

(* source-level variable *)
and var = {
  name : string;
  id : var_id;
  typ : typ;
}

(* a semantic type 「Σ」 *)
and typ =
  | Path   of typ_path
  | Tuple  of small_typ list
  | Sing   of signat
  | Struct of (string * typ) list (* order matters; see subtype_struct *)
  (* we use slightly different terminology for function types
     because what 1ML calls "purity" is actually the stronger
     property of _phase separability_. *)
  | AFun   of (tvar list,                typ) binder (*      auto function type 「→ A」 *)
         (* AFun has the additional invariant that the ∀-bound variables have kind Type *)
  | SFun   of (tvar list, typ *          typ) binder (*    static function type 「→ P」 *)
  | EFun   of (tvar list, typ * eff * signat) binder (* effectful function type 「→ І」 *)
  (* the type-level λ-binder is a small type (constructor) that can appear in paths only.
     the paper doesn't mention it, but it's needed with higher-order functors in some cases. *)
  | Lambda of (tvar, small_typ) binder
  | UVar   of uvar

(* a semantic small type 「σ」 *)
and small_typ = typ

(* a semantic signature 「Ξ」 *)
and signat = (tvar list, typ) binder

(* a path 「π」 *)
and typ_path = tvar * small_typ snoc

(* an effect (a variable denoting an expression of type `effect`) *)
and eff = typ

(* a mutable variable tracking an upper bound on the known effect for
   a region of code. *)
and eff_var = eff_cell ref
and eff_cell =
  | EStatic
  | EDynamic of typ
  | EUnknown

(* an inference variable 「υ」 *)
and uvar = ucell ref
and ucell =
  | Unknown of string * uvar_id * level
  | Known   of typ

(* ========== Pretty-printing of types ========== *)

type show_s = string list -> string list

let show_paren : bool -> show_s -> show_s = function
  | false -> fun sh -> sh
  | true  -> fun sh acc -> "(" :: sh (")" :: acc)

let rec show_kind head = function
  | Type         -> fun acc -> "Ω" :: acc
  | Fun (k1, k2) -> show_paren head
                    (fun acc -> show_kind true k1 (" -> " :: show_kind false k2 acc))

let show_tvar_occurrence : tvar -> show_s =
  fun { name; id; _ } acc -> name :: "." :: string_of_int id :: acc

and show_var_occurrence : var -> show_s =
  fun { name; id; _ } acc -> name :: "/" :: string_of_int id :: acc

let show_tvar_binder : tvar -> show_s =
  fun { name; id; kind; info } acc ->
    name :: "." :: string_of_int id :: " : " ::
    show_kind false kind
    (match info with
     | Opaque -> acc
     | Reflects v -> " ~ " :: show_var_occurrence v acc
     | Datatype (_, _) -> " = <datatype>" :: acc)

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
  | Path p -> show_path p
  | Tuple tys -> fun acc ->
      "(" ::
      snd (List.fold_right (fun ty (sep, acc) ->
                             (" * ", show_typ false ty (sep :: acc)))
                           tys ("", ")" :: acc))
  | Sing sg -> fun acc ->
      "[= " :: show_sig sg ("]" :: acc)
  | Struct fs -> fun acc ->
      "{" ::
      snd (List.fold_right (fun (name, ty) (sep, acc) ->
                             ("; ", name :: " : " :: show_typ false ty (sep :: acc)))
                           fs ("", "}" :: acc))
  | AFun (tvs, ty) ->
      show_paren atomic (fun acc ->
        show_quantifier "∀" tvs
        ("'{} => " :: show_typ false ty acc))
  | SFun (tvs, (ty1, ty2)) ->
      show_paren atomic (fun acc ->
        show_quantifier "∀" tvs
        (show_typ true ty1 (" => " :: show_typ false ty2 acc)))
  | EFun (tvs, (ty1, eff, sg2)) ->
      show_paren atomic (fun acc ->
        show_quantifier "∀" tvs
        (show_typ true ty1 (" -> [" :: show_eff eff ("] " :: show_sig sg2 acc))))
  | Lambda (tv, ty) ->
      show_paren atomic (fun acc ->
        show_quantifier "λ" [tv] (show_typ false ty []))
  | UVar u ->
      match deref u with
      | Known ty -> show_typ atomic ty
      | Unknown (name, id, level) -> fun acc ->
          let dotted = function | "" -> "" | n -> n ^ "." in
          "?" :: dotted name :: string_of_int id :: "@" :: string_of_int level :: acc

and show_path : typ_path -> show_s =
  fun (p_head, p_args) acc ->
    show_tvar_occurrence p_head
    (Snoc.fold_right (fun arg acc -> " " :: show_typ true arg acc) p_args acc)

and show_eff : eff -> show_s =
  fun eff -> show_typ false eff

let show_var_binder : var -> show_s =
  fun { name; id; typ } acc ->
    name :: "/" :: string_of_int id :: " : " ::
      show_typ false typ acc

(* ========== Basic utility functions ========== *)

let rec is_small : typ -> bool = function
  | Path _ | UVar _            -> true (* don't even need to visit the UVar *)
  | Sing sg                    -> is_small_sig sg
  | Tuple ts                   -> List.for_all is_small ts
  | Struct fs                  -> List.for_all (fun (_, ty) -> is_small ty) fs
  | EFun ([], (ty1, eff, sg2)) -> is_small ty1 && is_small_sig sg2
  | AFun _ | SFun _ | EFun _   -> false
  | Lambda (_, ty)             -> is_small ty

and is_small_sig : signat -> bool = function | ([], ty) -> is_small ty
                                             | _        -> false

and is_small_eff : eff -> bool = fun e -> is_small e

let small_ty_of_sig : signat -> small_typ option = function
  | ([], ty) -> if is_small ty then Some ty else None
  | _        -> None

let rec kind_eql : kind -> kind -> bool =
  fun k1 k2 ->
    match (k1, k2) with
    | (Type,             Type            ) -> true
    | (Fun (k_i1, k_o1), Fun (k_i2, k_o2)) -> kind_eql k_i1 k_i2 && kind_eql k_o1 k_o2
    | _                                    -> false

let kind_spine : kind -> kind snoc * kind =
  let rec go ks = function
    | Fun (k1, k2) -> go (Snoc (ks, k1)) k2
    | k            -> (ks, k)
  in go Nil

let next_tvar_id = counter ()
and next_uvar_id = counter ()
and next_var_id = counter ()

let new_uvar lvl name () : typ =
  UVar (ref (Unknown (name, next_uvar_id (), lvl)))

let new_opaque_tvar (name : string) (kind : kind) () : tvar =
  { name; id = next_tvar_id (); kind; info = Opaque }

let freshen_tvar : tvar -> tvar =
  fun { name; id = _; kind; info } ->
    { name; id = next_tvar_id (); kind; info }

let (<?) : level option -> level -> bool =
  fun lvl1 lvl2 -> match lvl1 with
                   | Some lvl1 -> lvl1 < lvl2
                   | _         -> false

let assert_unknown : uvar -> string * uvar_id * level =
  fun u -> match deref u with
           | Unknown (name, id, lvl) -> (name, id, lvl)
           | Known _ -> invalid_arg "impossible: grounded type is a Known uvar"

(* follow `Known` links until we get to a concrete type or unsolved uvar *)
let ground : typ -> typ =
  let rec start ty = go [] ty
  and go (obligations : uvar list) ty =
    match ty with
    | UVar u ->
      (match deref u with
      | Known ty -> go (u :: obligations) ty
      | Unknown (_, _, _) -> finish obligations ty)
    | _ -> finish obligations ty
  and finish obligations ty =
    (* path compression *)
    List.iter (fun u -> u := Known ty) obligations;
    ty
  in start

(* ========== NBE-based simplification of Fω types ========== *)

module Subst = struct

  (* An intermediate result of type evaluation.
     We will eventually be able to eliminate all `IFun` constructors
     by converting them back into lambdas. *)
  type intermediate =
    | IValue of typ
    | IFun of string * kind * (intermediate -> intermediate)

  let var (tv : tvar) : intermediate = IValue (Path (tv, Nil))

  let rec extract_intermediate : intermediate -> typ = function
    | IValue ty -> ty
    | IFun (name, k_arg, f) ->
        let tv = new_opaque_tvar name k_arg () in
        Lambda (tv, extract_intermediate (f (var tv)))

  type env = intermediate IntMap.t

  let empty_env : env = IntMap.empty

  let extend_env : tvar -> intermediate -> env -> env =
    fun tv ty env ->
      match IntMap.lookup tv.id env with
      | Some _ -> invalid_arg (String.concat ""
                    ("impossible: attempt to shadow bound variable " :: show_tvar_binder tv []))
      | None -> IntMap.insert tv.id ty env

  (* extend an environment with a mapping from a given tvar to fresh version *)
  let freshen_one : tvar -> env -> env * tvar =
    fun tv env ->
      let tv' = freshen_tvar tv in
      let env' = extend_env tv (var tv') env in
      (env', tv')

  (* extend an environment with mappings from given tvars to fresh versions *)
  let freshen_all : tvar list -> env -> env * tvar list =
    map_m state_monad freshen_one

  let substitute_var (env : env) (tv : tvar) : intermediate =
    match IntMap.lookup tv.id env with
    | Some int -> int
    | None     -> var tv

  let rec substitute (env : env) : typ -> typ = function
    (* FIXME: don't reallocate when substitution doesn't change a type *)
    | Path (tv, ts) ->
        let tv' = substitute_var env tv in
        Snoc.fold_left (fun ty arg -> apply ty (IValue (substitute env arg))) tv' ts
          |> extract_intermediate
    | Tuple ts -> Tuple (List.map (substitute env) ts)
    | Sing sg -> Sing (substitute_sig env sg)
    | Struct fs -> Struct (List.map (fun (f, ty) -> (f, substitute env ty)) fs)
    | AFun (tvs, ty) ->
        let (env', tvs') = freshen_all tvs env in
        AFun (tvs', substitute env' ty)
    | SFun (tvs, (ty1, ty2)) ->
        let (env', tvs') = freshen_all tvs env in
        SFun (tvs', (substitute env' ty1, substitute env' ty2))
    | EFun (tvs, (ty1, eff, sg2)) ->
        let (env', tvs') = freshen_all tvs env in
        EFun (tvs', (substitute     env' ty1,
                     substitute_eff env' eff,
                     substitute_sig env' sg2))
    | Lambda (tv, ty) ->
        let (env', tv') = freshen_one tv env in
        Lambda (tv', substitute env' ty)
    | UVar u ->
        match deref u with
        | Known ty -> substitute env ty
        | Unknown (name, _, _) ->
            (* I'm not sure what behavior is appropriate here.
               There are a few possibilities:
               - It should be impossible to encounter an unsolved uvar while we are
                 doing substitution, so we can keep the error here.
               - Any such uvars are guaranteed not to ever be instantiated with
                 any bound variables that would be substituted, so we can leave
                 the uvar as-is.
               - We have to introduce the notion of a type expression containing
                 a stuck substitution that is waiting for a uvar to be solved
                 before it can be applied.
               The answer will become clear once I test the system a little
               and my understanding of 1ML improves. *)
            invalid_arg ("encountered an unsolved uvar during substitution: " ^ name)

  and substitute_sig (env : env) : signat -> signat =
    fun (tvs, ty) ->
      let (env', tvs') = freshen_all tvs env in
      (tvs', substitute env' ty)

  and substitute_eff env : eff -> eff = substitute env

  and apply : intermediate -> intermediate -> intermediate =
    fun f x ->
      match f with
      | IFun (_, _, f) -> f x
      | IValue ty ->
        match ty with
        | Path (tv, tys) ->
          let x = extract_intermediate x in
          if is_small x
          then IValue (Path (tv, Snoc (tys, x)))
          else invalid_arg "attempted to add a non-small type to a path"
        | _ -> invalid_arg (String.concat ""
                  ("impossible: attempted to apply non-function: " :: show_typ false ty []))

  and lambda : (tvar list, typ) binder -> intermediate =
    let rec go env (tvs : tvar list) body =
      match tvs with
      | []        -> IValue (substitute env body)
      | tv :: tvs -> IFun (tv.name, tv.kind, fun arg -> go (extend_env tv arg env) tvs body)
    in fun (tvs, body) -> go IntMap.empty tvs body

  (* checks the side condition 「δ Σ = Σ」 by just checking that no variables contained in
     a given substitution feature in a given type expression. *)
  let rec assert_fresh (env : env) : typ -> (unit, tvar) result = function
    (* TODO: can we avoid all these freshening substitutions? *)
    | Path p     -> assert_fresh_path env p
    | Tuple tys  -> for_m error_monad (assert_fresh env) tys
    | Sing sg    -> assert_fresh_binder env sg
    | Struct fs  -> for_m error_monad (fun (_, ty) -> assert_fresh env ty) fs
    | AFun (tvs, ty) ->
                    assert_fresh_binder env (tvs, ty)
    | SFun (tvs, (ty1, ty2)) ->
                    let (freshening, _) = freshen_all tvs empty_env in
                    let* () = assert_fresh env (substitute freshening ty1) in
                    let* () = assert_fresh env (substitute freshening ty2) in
                    Ok ()
    | EFun (tvs, (ty1, eff, (tvs2, ty2))) ->
                    let (freshening1, _) = freshen_all tvs empty_env in
                    let* () = assert_fresh env (substitute freshening1 ty1) in
                    let* () = assert_fresh env (substitute freshening1 eff) in
                    let (freshening2, _) = freshen_all tvs2 empty_env in
                    assert_fresh env (substitute freshening1 (substitute freshening2 ty2))
    | Lambda (tv, ty) ->
                    let (freshening, _) = freshen_one tv empty_env in
                    assert_fresh env (substitute freshening ty)
    | UVar u     -> match deref u with
                    | Known typ         -> assert_fresh env typ
                    | Unknown (_, _, _) -> Ok ()

  and assert_fresh_path env ((p_head, p_args) : typ_path) =
    match IntMap.lookup p_head.id env with
    | Some _ -> Error p_head
    | None   -> for_m error_monad (assert_fresh env) (Snoc.to_list p_args)

  and assert_fresh_binder env (tvs, ty) =
    let (freshening, _) = freshen_all tvs empty_env in
    assert_fresh env (substitute freshening ty)

end

(* ========== Contexts ========== *)

module Ctx = struct

  type ctx = {
    num_tvars : int;
    tvars : (tvar * level) IntMap.t;
    (* In the core calculus, value-, module-, and type-level variables
       all range over the same sort of thing (an expression).
       We distinguish them in the context only because they are separate namespaces in OCaml. *)
    vars  : var snoc;
    tcons : var snoc;
    mods  : var snoc;
  }
  type t = ctx

  (* Communicates that the context is only being used for the
     `num_tvars` and `tvars` fields. *)
  type typ_ctx = ctx

  let empty = { num_tvars = 0; tvars = IntMap.empty; vars = Nil; tcons = Nil; mods = Nil }
  let extend_tvar : tvar -> ctx -> ctx
            = fun tv { num_tvars; tvars; vars; tcons; mods }
                       -> let tvars = match IntMap.lookup tv.id tvars with
                                      | Some _ -> invalid_arg (String.concat ""
                                                    ("duplicate type variable in ctx: " ::
                                                      show_tvar_binder tv []))
                                      | None -> IntMap.insert tv.id (tv, num_tvars) tvars
                          and num_tvars = num_tvars + 1
                          in { num_tvars; tvars; vars; tcons; mods }
  let extend_var  x  { num_tvars; tvars; vars; tcons; mods }
                        = let vars = Snoc (vars, x)
                          in { num_tvars; tvars; vars; tcons; mods }
  let extend_tcon tc { num_tvars; tvars; vars; tcons; mods }
                        = let tcons = Snoc (tcons, tc)
                          in { num_tvars; tvars; vars; tcons; mods }

  let tvar_level : tvar -> typ_ctx -> level option =
    fun tv { tvars; _ } -> IntMap.lookup tv.id tvars |> Option.map (fun (_, lvl) -> lvl)

  let find (get_item : ctx -> 'a snoc) (get_name : 'a -> string) : string -> ctx -> 'a option =
    fun name ctx ->
      let rec start () = go (get_item ctx)
      and go = function | Nil -> None
                        | Snoc (items, item) -> if get_name item = name then Some item
                                                                        else go items
      in start ()

  let extend_tvars tvs ctx = List.fold_left (Fun.flip extend_tvar) ctx tvs

  (* 1ML has a notion of a local type variable extension for a judgement.
     Note the semicolon instead of a normal comma for a context extension:

     「 Γ; α:κ  ⊢  J 」

     The meaning of this is that the judgement J is applied as usual, but then
     after the outputs are computed, all unsolved inference variables still
     featuring in the outputs of J should have the variable α stripped from their
     Δ-set; in other words, this variable ceases to be considered in scope when
     the inference variable is ultimately solved.
     (The paper phrases this in terms of an input and output substitution,
     but it's more intuitive to think of it in terms of side effects.)

     The function `extend_locally` helps implement this behavior.
     It takes a context and a list of type variables by which to extend it,
     and returns the extended context, along with an additional function
     which conceptually strips the variables out of the Δ-sets of any
     unsolved uvars found in a given type (modifying this type in-place).
   *)

  type local_extension = {
    ctx : typ_ctx;
    strip : typ -> unit;
  }

  let extend_locally (ctx : typ_ctx) (tvs : tvar list) : local_extension =
    let base_lvl = ctx.num_tvars in
    let rec strip ty =
      match ground ty with
      (* plumbing *)
      | Path (_, tys)                  -> List.iter strip (Snoc.to_list tys)
      | Tuple tys                      -> List.iter strip tys
      | Sing (_, ty) | AFun (_, ty) | Lambda (_, ty)
                                       -> strip ty
      | Struct fs                      -> List.iter (fun (_, ty) -> strip ty) fs
      | SFun (_, (ty1, ty2))           -> strip ty1; strip ty2
      | EFun (_, (ty1, eff, (_, ty2))) -> strip ty1; strip eff; strip ty2
      (* the only real logic: u.lvl := min(u.lvl, base_lvl) *)
      | UVar u -> let (u_name, u_id, u_lvl) = assert_unknown u in
                  if base_lvl < u_lvl
                  then u := Unknown (u_name, u_id, base_lvl)
                  else ()
    in { ctx = extend_tvars tvs ctx; strip }

  let dump (ctx : ctx) : unit =
    let print line = Miniml.debug (fun () -> line) in
    print "===== tyvars             =====";
    (ctx.tvars
     |> IntMap.fold (fun acc _ (tv, lvl) -> (tv, lvl) :: acc) []
     |> list_sort (fun (_, lvl1) (_, lvl2) -> lvl1 - lvl2)
     |> List.map  (fun (tv, lvl) -> "@" :: string_of_int lvl :: " " :: show_tvar_binder tv [])
     |> List.iter (fun line -> print (String.concat "" line)));
    print "===== variables          =====";
    List.iter (fun v -> print (String.concat "" (show_var_binder v []))) (Snoc.to_list ctx.vars);
    print "===== type constructors  =====";
    List.iter (fun v -> print (String.concat "" (show_var_binder v []))) (Snoc.to_list ctx.tcons);
    print "===== modules            =====";
    List.iter (fun v -> print (String.concat "" (show_var_binder v []))) (Snoc.to_list ctx.mods);
    print "==============================";
    ()

end
type typ_ctx = Ctx.typ_ctx
type ctx = Ctx.t

(* ========== Core elaboration rules ========== *)

(* NOTE [The parsimonious contexts trick]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   As said above, when we perform a local context extension 「 Γ; α:κ  ⊢  J 」,
   we strip the variable α out of the Δ-sets of all inference variables
   remaining in J. Consider what purpose this actually serves.

   Any inference variable that already existed at the beginning of J
   wouldn't have α in its Δ-set to begin with.
   The only inference variables that we have to worry about
   are those which are created _during the exection of J_.
   These will have α in the Δ-set when they are born, but ultimately it
   must be removed if they are still unsolved by the time we return.

   However, there are places in the rules where the semicolon notation is used
   even though the nature of the judgement J is such that it couldn't possibly
   create any new inference variables featuring α, such as during the occurs check
   and unification. It's maybe conceptually correct to still use it, but operationally,
   we can get away with _not actually adding α to the context at all!_

   Functions accepting `typ_ctx` indicate that they only use the context
   for the `num_tvars` and `tvars` fields. This enables looking up the level
   associated with a given tvar to see whether it can be used in the solution
   to a uvar (the equivalent of a Δ-set query). A tvar absent from the context
   can be treated as absent from all Δ-sets we check.
   When we know that no new unconstrained uvars will be created,
   omitting a tvar from the context accomplishes the exact same thing
   as adding it to the context at a level higher than all the extant uvars.
 *)

let level_check (ctx : typ_ctx) (lvl : level) (tv : tvar) : unit m_result =
  let tv_lvl = Ctx.tvar_level tv ctx in
  if tv_lvl <? lvl then
    Ok ()
  else
    Error (E (String.concat ""
      ("type variable would escape its scope: " :: show_tvar_occurrence tv [])))

(* In the "standard" verison of Caml type inference (Kiselyov's `sound_eager.ml`),
   the occurs check simultaneously does a few things:
   - Checks that there are no occurrences of `u` in `ty`;
   - Checks that all abstract variables mentioned in `ty` are permissible to appear in the
     solution of `u` (their level is within the level of `u`);
   - Restricts the remaining unsolved metas in `ty` by changing their levels to match `u`.
   This is exactly what it needs to do in 1ML too; these operations are exactly what is needed
   to check all the premises of 「IUbind」. *)

let rec occurs_check (ctx : typ_ctx) (u : uvar) (u_lvl : level) (ty : typ) : unit m_result =
  match ground ty with
  (* TODO: can we avoid all these freshening substitutions? *)
  | Path (tv, tys)   -> let* () = level_check ctx u_lvl tv in (* 「∆υ ⊇ fv(σ)」 *)
                        for_m error_monad (occurs_check ctx u u_lvl) (Snoc.to_list tys)
  | Tuple tys        -> for_m error_monad (occurs_check ctx u u_lvl) tys
  | Sing sg          -> occurs_check_binder ctx u u_lvl sg
  | Struct fs        -> for_m error_monad (fun (_, ty) -> occurs_check ctx u u_lvl ty) fs
  | AFun (tvs, ty)   -> occurs_check_binder ctx u u_lvl (tvs, ty)
  | SFun (tvs, (ty1, ty2))
                     -> let (freshening, tvs') = Subst.freshen_all tvs Subst.empty_env in
                        (* Conceptually `ctx` is extended by `tvs'` here --
                           see note [The parsimonious contexts trick] *)
                        let _ = tvs' in
                        let* () = occurs_check ctx u u_lvl (Subst.substitute freshening ty1) in
                        let* () = occurs_check ctx u u_lvl (Subst.substitute freshening ty2) in
                        Ok ()
  | EFun (tvs, (ty1, eff, (tvs2, ty2)))
                     -> let (freshening1, tvs') = Subst.freshen_all tvs Subst.empty_env in
                        (* Conceptually `ctx` is extended by `tvs'` here --
                           see note [The parsimonious contexts trick] *)
                        let _ = tvs' in
                        let* () = occurs_check ctx u u_lvl (Subst.substitute freshening1 ty1) in
                        let* () = occurs_check ctx u u_lvl (Subst.substitute freshening1 eff) in
                        let (freshening2, tvs2') = Subst.freshen_all tvs2 Subst.empty_env in
                        (* Conceptually `ctx` is extended by `tvs'` and `tvs2'` here --
                           see note [The parsimonious contexts trick] *)
                        let _ = tvs2' in
                        occurs_check ctx u u_lvl (Subst.substitute freshening1
                                                    (Subst.substitute freshening2 ty2))
  | Lambda (tv, ty)  -> let (freshening, tv') = Subst.freshen_one tv Subst.empty_env in
                        (* Conceptually `ctx` is extended by `tv'` here --
                           see note [The parsimonious contexts trick] *)
                        let _ = tv' in
                        occurs_check ctx u u_lvl (Subst.substitute freshening ty)
  | UVar u'          -> let (u'_name, u'_id, u'_lvl) = assert_unknown u' in
                        if u' == u then
                          Error (E "occurs check failed: cannot construct infinite type")
                        else
                          (u' := Unknown (u'_name, u'_id, min u_lvl u'_lvl);
                           Ok ())

and occurs_check_binder ctx u u_lvl =
  fun (tvs, ty)      -> let (freshening, tvs') = Subst.freshen_all tvs Subst.empty_env in
                        (* Conceptually `ctx` is extended by `tvs'` here --
                           see note [The parsimonious contexts trick] *)
                        let _ = tvs' in
                        occurs_check ctx u u_lvl (Subst.substitute freshening ty)

let unify_failure (ty1 : typ) (ty2 : typ) : error =
  E (String.concat "" ("cannot unify types " :: show_typ false ty1
                        (" ≠ " :: show_typ false ty2 [])))

let subtype_failure (ty1 : typ) (ty2 : typ) : error =
  E (String.concat "" ("cannot establish subtyping: " ::
                        show_typ false ty1 (" ≤ " :: show_typ false ty2 [])))

(* 「Ξ = Ξ'」 *)
let rec unify (ctx : typ_ctx) (ty1 : typ) (ty2 : typ) : unit m_result =
  let* succeeded =
    match (ground ty1, ground ty2) with
    | (UVar  u,   ty)
    | (ty,        UVar u)    -> unify_uvar  ctx u   ty
    | (Path  p1,  Path  p2)  -> unify_path  ctx p1  p2
    | (Tuple ts1, Tuple ts2) -> unify_tuple ctx ts1 ts2
    | (Sing  sg1, Sing  sg2) -> unify_sig   ctx sg1 sg2
    | _ -> Ok false
  in
  if succeeded then Ok ()
  else Error (unify_failure ty1 ty2)

and unify_uvar (ctx : typ_ctx) (u : uvar) (ty : typ) : bool m_result =
  let* () =
    if is_small ty then Ok () else
      Error (E (String.concat "" ("cannot unify with non-small type: " ::
        show_typ false (UVar u) (" ~ " :: show_typ false ty []))))
  in
  if
    match ground ty with
    | UVar u' -> u == u'
    | _       -> false
  then
    (* 「IUrefl」 *)
    Ok true
  else
    (* 「IUbind」 *)
    let (_, _, u_lvl) = assert_unknown u in
    let* () = occurs_check ctx u u_lvl ty in
    u := Known ty;
    Ok true

(* 「IUpath」 *)
and unify_path : typ_ctx -> typ_path -> typ_path -> bool m_result =
  fun ctx (tv1, tys1) (tv2, tys2) ->
    if not (tv1.id = tv2.id && Snoc.length tys1 == Snoc.length tys2) then
      Ok false
    else
      let* () = unify_all ctx (Snoc.to_list tys1) (Snoc.to_list tys2) in
      Ok true

and unify_tuple : typ_ctx -> small_typ list -> small_typ list -> bool m_result =
  fun ctx ts1 ts2 ->
    if not (List.length ts1 == List.length ts2) then
      Ok false
    else
      let* () = unify_all ctx ts1 ts2 in
      Ok true

and unify_all : typ_ctx -> typ list -> typ list -> unit m_result = fun ctx ts1 ts2 ->
  match (ts1, ts2) with
  | ([],        [])        -> Ok ()
  | (t1 :: ts1, t2 :: ts2) -> let* () = unify ctx t1 t2 in
                              unify_all ctx ts1 ts2
  | _                      -> invalid_arg "cannot unify different numbers of arguments"

(* 「IUabs」 *)
and unify_sig : typ_ctx -> signat -> signat -> bool m_result =
  fun ctx (tvs1, ty1) (tvs2, ty2) ->
    if not ((tvs1, tvs2) ||> list_equal (fun tv1 tv2 -> kind_eql tv1.kind tv2.kind)) then
      Ok false
    else
      let tvs' : (tvar * tvar * tvar) list =
        List.map2 (fun tv1 tv2 -> (tv1, tv2, new_opaque_tvar tv1.name tv1.kind ())) tvs1 tvs2
      in
      let (env1, env2) =
        ((Subst.empty_env, Subst.empty_env), tvs')
        ||> List.fold_left (fun (env1, env2) (tv1, tv2, tv') ->
              let tv' = Subst.var tv' in
              let env1' = Subst.extend_env tv1 tv' env1
              and env2' = Subst.extend_env tv2 tv' env2
              in (env1', env2'))
      in
      (* see note [The parsimonious contexts trick] *)
      let* () = unify ctx (Subst.substitute env1 ty1)
                          (Subst.substitute env2 ty2)
      in Ok true

(* Remove from `paths` all variables bound in `env`. *)
let reduce_paths (paths : 'a IntMap.t) (env : 'b IntMap.t) : 'a IntMap.t =
  paths |> IntMap.filter
              (fun k _ -> match IntMap.lookup k env with
                          | Some _ -> false
                          | None   -> true)

(* Resolution 「Γ ⊢! υ ≈ Σ」 is an operation which solves for a uvar by
   figuring out the outermost constructor.
   The idea behind resolution is that some types have the property that
   encountering them as a bound on a uvar (during subtyping) tells us
   information about the uvar, _regardless of whether it was as an upper
   or lower bound_. This is because there is no top or bottom type,
   so for most kinds of types, the general shape of their supertypes
   and subtypes must match.
 *)
let resolve (ctx : typ_ctx) (u : uvar) (ty : typ) : unit m_result =
  Miniml.debug (fun () -> String.concat ""
    ("resolve " :: show_typ false (UVar u) (" ≈ " :: show_typ false ty [])));
  (* FIXME: do an occurs check here *)
  let (u_name, _, u_lvl) = assert_unknown u in
  match ground ty with
  | UVar u2 -> (* 「IRinfer」 *)
      let (_, _, u2_lvl) = assert_unknown u2 in
      let u3 = new_uvar (min u_lvl u2_lvl) u_name () in
      u  := Known u3;
      u2 := Known u3;
      Ok ()
  | Path (tv, tys) -> (* 「IRpath」 *)
      let* () = level_check ctx u_lvl tv in (* 「α ∈ Δυ」 *)
      let u_args = Snoc.map (fun _ -> new_uvar u_lvl "" ()) tys in
      u := Known (Path (tv, u_args));
      Ok ()
  | Tuple tys ->
      let u_args = List.map (fun _ -> new_uvar u_lvl "" ()) tys in
      u := Known (Tuple u_args);
      Ok ()
  | Sing _ -> (* 「IRtype」 *)
      let u' = new_uvar u_lvl "" () in
      u := Known (Sing ([], u'));
      Ok ()
  | _ -> invalid_arg (String.concat ""
          ("resolution is inapplicable here: Σ = " :: show_typ false ty []))

(* A type expression which should be solved for in the process of subtyping.
   It consists of a "head" 「α」 applied to a list of type variables 「overline(α)」
   which the solution should be regarded as a function of.
   1ML represents this using a path, which isn't really appropriate,
   since it neglects that everything in the spine is a variable. *)
type solute = tvar * tvar snoc

let paths_of_tvars : tvar list -> solute IntMap.t =
  List.fold_left (fun paths tv -> IntMap.insert tv.id (tv, Nil) paths) IntMap.empty

let solute_append : tvar list -> solute -> solute
  = fun tvs (head, args) ->
      (head, List.fold_left (fun acc tv -> Snoc (acc, tv)) args tvs)

(* Check that `ty1` is a subtype of `ty2`.
   `paths` is a set of solutes keyed by the IDs of their heads.
   The return type of subtyping is an environment 「δ」, which provides
   definitions for *some* of the variables mentioned in `paths`. *)
let rec subtype (ctx : typ_ctx) ty1 ty2 (paths : solute IntMap.t)
: Subst.env m_result =
  Miniml.debug (fun () -> String.concat ""
    ("subtype " :: show_typ false ty1 (" ≤ " :: show_typ false ty2 [])));
  match (ground ty1, ground ty2) with
  | (UVar u, ty2)  -> if match ty2 with
                         | UVar u' -> u == u'
                         | _       -> false
                      then Ok Subst.empty_env (* 「ISrefl」 typical case *)
                      else let* () = resolve ctx u ty2 in
                           subtype_resolved ctx ty1 ty2 paths (* 「ISresl」 *)
  | (ty1, UVar u)  -> let* () = resolve ctx u ty1 in
                      subtype_resolved ctx ty1 ty2 paths (* 「ISresr」 *)
  | (ty1, ty2)     -> subtype_resolved ctx ty1 ty2 paths

(* In 1ML, after performing ISresl and ISresr, the exact same subtyping check is re-attempted
   (but with the added knowledge introduced by resolution).
   They provide a justification for why this repetition cannot result in an infinite loop,
   which we make true-by-construction by stratifying subtyping into two judgements.
   This function comprises only the cases of subtyping that can occur after resolution. *)
and subtype_resolved (ctx : typ_ctx) ty1 ty2 (paths : solute IntMap.t)
: Subst.env m_result =
  Miniml.debug (fun () -> String.concat ""
    ("* resolved " :: show_typ false ty1 (" ≤ " :: show_typ false ty2 [])));
  paths |> IntMap.iter (fun _ (tv, args) ->
    Miniml.debug (fun () -> String.concat ""
      ("* path: " :: show_tvar_occurrence tv (
        Snoc.fold_right (fun arg acc -> " " :: show_tvar_occurrence arg acc) args []))
    )
  );
  match (ground ty1, ground ty2) with
  | (UVar u1, UVar u2) ->
      if u1 == u2 then Ok Subst.empty_env (* 「ISrefl」 when caused by IRinfer *)
      else invalid_arg "impossible"
  | (UVar _, _) | (_, UVar _) ->
      invalid_arg "impossible: ty1, ty2 should've been resolved already"
  | (Path _, Path _) -> (* 「ISpath」 *)
      let* () = unify ctx ty1 ty2 in
      Ok Subst.empty_env
  | (Sing sg1, Sing sg2) ->
      subtype_singleton ctx sg1 sg2 paths
  | (Struct fs1, Struct fs2) ->
      subtype_struct ctx fs1 fs2 paths
  | (SFun sf1, SFun sf2) ->
      subtype_sfun ctx sf1 sf2 paths
  | (SFun (tvs1, (ty_i1, ty_o1)), EFun ef2) ->
      subtype_efun ctx (tvs1, (ty_i1, None, ([], ty_o1))) ef2 paths
  | (EFun (tvs1, (ty_i1, eff1, sg_o1)), EFun ef2) ->
      subtype_efun ctx (tvs1, (ty_i1, Some eff1, sg_o1)) ef2 paths
  | (ty1, ty2) -> Error (subtype_failure ty1 ty2)

and subtype_singleton (ctx : typ_ctx) (sg1 : signat) (sg2 : signat) (paths : solute IntMap.t)
: Subst.env m_result =
  (* there are two applicable judgements here, IStype and ISforget.
     ISforget is used to solve for an abstract variable in `paths`,
     and has four conditions, two of which we must check up front: *)
  let path_solution : (tvar * small_typ snoc * tvar snoc) option =
    (* (1) sg2 must be a path 「α₀ overline(α)」... *)
    match sg2 with
    | ([], Path (tv_head, (ty_args : small_typ snoc))) ->
        (* (2) ... and the head 「α₀」 must occur in the set of to-be-solved paths *)
        IntMap.lookup tv_head.id paths
        |> Option.map (fun (_, (pat_vars : tvar snoc)) -> (tv_head, ty_args, pat_vars))
    | _ -> None
  in
  match path_solution with
  | None -> (* 「IStype」 *)
      (* TODO: it's probably possible to do these checks at the same time somehow *)
      let* () = subsig_no_paths ctx sg1 sg2 in
      let* () = subsig_no_paths ctx sg2 sg1 in
      Ok Subst.empty_env
  | Some (tv_head, ty_args, pat_vars) -> (* 「ISforget」 *)
      (* (3) sg1 must be a small type 「σ」 *)
      let* (ty1 : small_typ) =
        match small_ty_of_sig sg1 with
        | Some ty -> Ok ty
        | None    -> Error (E (String.concat ""
                       ("can't match path against a large type: " :: show_sig sg1 [])))
      in
      (* (4) ty_args and pat_vars must match 「overline(α)」 *)
      let pat_vars = Snoc.to_list pat_vars in
      let* () =
        try_zip (Snoc.to_list ty_args) pat_vars
        (* these paths have the same head variable, so its kind enforces matching lengths *)
        |> (function | Ok x    -> x
                     | Error _ -> invalid_arg "impossible: paths differ in length")
        |> Snoc.to_list
        |> List.for_all (fun (ty_arg, pat_var) ->
            match ty_arg with
            | Path (ty_var, Nil) -> ty_var.id == pat_var.id
            | _ -> false)
        |> (function | true  -> Ok ()
                     | false -> Error (E "path arguments don't match"))
      in
      let lambda = Subst.lambda (pat_vars, ty1) in
      Ok (Subst.extend_env tv_head lambda Subst.empty_env)

and subtype_struct (ctx : typ_ctx) (fs1 : (string * typ) list) (fs2 : (string * typ) list)
                   (paths : solute IntMap.t) : Subst.env m_result =
  match fs2 with
  | []               -> Ok Subst.empty_env (* 「ISempty」 *)
  | (f2, ty2) :: fs2 -> (* 「ISstr」 *)
    let* (ty1, fs1) =
      let rec go acc = function
        | []               -> Error (E ("subtyping failure: LHS has no field " ^ f2))
        | (f1, ty1) :: fs1 -> if f1 = f2 then Ok (ty1, Snoc.to_list_append acc fs1)
                                         else go (Snoc (acc, (f1, ty1))) fs1
      in go Nil fs1
    in
    let* env1 = subtype ctx ty1 ty2 paths in
    let paths' = reduce_paths paths env1 in
    let* env2 = subtype_struct ctx fs1 fs2 paths' in
    (* check side condition 「θ₂δ₂Σ₁ = θ₂Σ₁」 -- unsure whether it's really needed?
       it means that the order of fields in a struct does matter *)
    let* () =
      match Subst.assert_fresh env2 ty1 with
      | Error tv -> Error (E (String.concat ""
                              ("abstract variable mentioned before it could be solved"
                                :: show_tvar_occurrence tv [])))
      | Ok () -> Ok ()
    in
    (* env1 and env2 are disjoint, since env2 includes only keys in paths' *)
    Ok (IntMap.union env1 env2)

and subtype_sfun (ctx : typ_ctx) :
                 (tvar list, typ * typ) binder ->
                 (tvar list, typ * typ) binder ->
                 solute IntMap.t ->
                 Subst.env m_result
= fun (tvs1, (ty_i1, ty_o1))
      (tvs2, (ty_i2, ty_o2)) paths ->
  (* 「ISfun, η'=η=I」 *)
  let (freshening1, tvs1) = Subst.freshen_all tvs1 Subst.empty_env
  and (freshening2, tvs2) = Subst.freshen_all tvs2 Subst.empty_env in
  let ty_i1 = Subst.substitute freshening1 ty_i1
  and ty_i2 = Subst.substitute freshening2 ty_i2
  and ty_o1 = Subst.substitute freshening1 ty_o1
  and ty_o2 = Subst.substitute freshening2 ty_o2 in
  let* env_i =
    subtype_all_paths (Ctx.extend_tvars tvs2 ctx) ty_i2 ty_i1
                      (paths_of_tvars tvs1)
  in
  let* env_o =
    let xctx = Ctx.extend_locally ctx tvs2 in
    let* env_o =
      subtype xctx.ctx (Subst.substitute env_i ty_o1) ty_o2
                       (IntMap.map (fun _ path -> solute_append tvs2 path) paths)
    in
    IntMap.iter (fun _ interm -> xctx.strip (Subst.extract_intermediate interm)) env_o;
    Ok env_o
  in
  (* check side condition 「θ₂δ₂Σ = θ₂Σ」 -- unsure whether it's really needed? *)
  let* () =
    match Subst.assert_fresh env_o ty_i2 with
    | Error tv -> Error (E (String.concat ""
                            ("ISfun side condition failed: input type mentions abstract variables solved in output type? "
                              :: show_tvar_occurrence tv [])))
    | Ok () -> Ok ()
  in
  Ok env_o

and subtype_efun (ctx : typ_ctx) :
                 (tvar list, typ * eff option * signat) binder ->
                 (tvar list, typ * eff        * signat) binder ->
                 solute IntMap.t ->
                 Subst.env m_result
= fun (tvs1, (ty_i1, eff1, sg_o1))
      (tvs2, (ty_i2, eff2, sg_o2)) paths ->
  (* 「ISfun, η=E, η' arbitrary」 *)
  invalid_arg "TODO: subtype_efun"

and subsig : typ_ctx -> signat -> signat -> solute IntMap.t -> Subst.env m_result =
  fun ctx sg1 sg2 paths ->
    match (sg1, sg2) with
    | (([],   ty1), ([],   ty2)) -> subtype ctx ty1 ty2 paths
    | ((tvs1, ty1), (tvs2, ty2)) -> (* 「ISabs」 *)
        let (freshening1, tvs1) = Subst.freshen_all tvs1 Subst.empty_env
        and (freshening2, tvs2) = Subst.freshen_all tvs2 Subst.empty_env in
        let ty1 = Subst.substitute freshening1 ty1
        and ty2 = Subst.substitute freshening2 ty2 in
        let xctx = Ctx.extend_locally ctx tvs1 in
        let* env = subtype_all_paths xctx.ctx ty1 ty2 (paths_of_tvars tvs2) in
        IntMap.iter (fun _ interm -> xctx.strip (Subst.extract_intermediate interm)) env;
        Ok IntMap.empty

and subsig_no_paths : typ_ctx -> signat -> signat -> unit m_result =
  fun ctx sg1 sg2 ->
    let* env = subsig ctx sg1 sg2 IntMap.empty in
    if IntMap.fold (fun _ _ _ -> true) false env
    then invalid_arg "impossible: subsig_no_paths returned paths"
    else Ok ()

and subtype_all_paths : typ_ctx -> typ -> typ -> solute IntMap.t -> Subst.env m_result =
  fun ctx ty1 ty2 paths ->
    let* env = subtype ctx ty1 ty2 paths in
    let paths' = reduce_paths paths env in
    if IntMap.fold (fun _ _ _ -> true) false paths'
    then Error (E "subtyping was established, but not all variables could be solved")
    else Ok env

(* ========== The initial context & primitive types ========== *)

let new_primitive (name : string) (kind : kind) () : tvar * var =
  let tv = new_opaque_tvar name kind () in
  let typ : typ =
    match kind_spine kind with
    | (arg_kinds, Type) ->
        let arg_vars =
          Snoc.to_list arg_kinds
          |> List.mapi (fun i k -> new_opaque_tvar ("a" ^ string_of_int i) k ())
        in
        let rec build_function_type (tvars_to_bind : tvar list)
                                    (path_args : small_typ snoc)
                                    (tvars_remaining : tvar list) : typ
        = match tvars_remaining with
          | [] -> Sing ([], Path (tv, path_args))
          | tv :: tvs ->
              let arg_ty = Path (tv, Nil) in
              (* We create a nested sequence of `SFun` constructors, but all the tvars
                 are bound in the outermost constructor.
                 It is possible for there to be no outermost `SFun` constructor,
                 but only if `arg_vars` is empty, in which case `tvars_to_bind` is also empty. *)
              SFun (tvars_to_bind,
                    (Sing ([], arg_ty),
                     build_function_type [] (Snoc (path_args, arg_ty)) tvs))
        in build_function_type arg_vars Nil arg_vars
    | _ -> invalid_arg "invalid kind head structure"
  in
  let v : var = { name; id = next_var_id (); typ } in
  (tv, v)

let ctx = Ctx.empty

let (tv_int, v_int) = new_primitive "int" Type ()
let ctx = ctx |> Ctx.extend_tvar tv_int
              |> Ctx.extend_tcon v_int
let (tv_string, v_string) = new_primitive "string" Type ()
let ctx = ctx |> Ctx.extend_tvar tv_string
              |> Ctx.extend_tcon v_string
let (tv_char, v_char) = new_primitive "char" Type ()
let ctx = ctx |> Ctx.extend_tvar tv_char
              |> Ctx.extend_tcon v_char
let (tv_list, v_list) = new_primitive "list" (Fun (Type, Type)) ()
let ctx = ctx |> Ctx.extend_tvar tv_list
              |> Ctx.extend_tcon v_list

let t_int    = Path (tv_int,    Nil)
let t_string = Path (tv_string, Nil)
let t_char   = Path (tv_char,   Nil)
let t_list t = Path (tv_list,   Snoc (Nil, t))

let t_unit = Tuple []
let v_unit = { name = "unit"; id = next_var_id (); typ = Sing ([], t_unit) }

let () = Ctx.dump ctx

(* type 'a elab = *)
