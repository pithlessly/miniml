open Util
open Common_syntax
open Core

let show_ty : typ -> string =
  let rec go prec ty =
    let wrap_if thresh f =
      if prec <= thresh then f else
      fun acc -> "(" :: f (")" :: acc) in
    match ty with
    | CQVar (QVar (s, _)) -> fun acc -> "'" :: s :: acc
    | CUVar r -> (match deref r with
                  | Known ty -> go prec ty
                  | Unknown (s, _, lvl) ->
                    fun acc -> ("?" ^ s ^ "(" ^ string_of_int lvl ^ ")") :: acc)
    | CTCon (CCon ("->", _), a :: b :: []) ->
      let a = go 1 a and b = go 0 b in
      wrap_if 0 (fun acc -> a (" -> " :: b acc))
    | CTCon (CCon ("*", _), []) -> fun acc -> "unit" :: acc
    | CTCon (CCon ("*", _), a :: args) ->
      let a = go 2 a and args = List.map (go 2) args in
      wrap_if 1 (fun acc -> a (List.fold_right
                                (fun arg acc -> " * " :: arg acc) args acc))
    | CTCon (CCon (con, _), []) -> fun acc -> con :: acc
    | CTCon (CCon (con, _), a :: []) ->
      let a = go 2 a in fun acc -> a (" " :: con :: acc)
    | CTCon (CCon (con, _), a :: args) ->
      let a = go 0 a and args = List.map (go 0) args in
      fun acc -> "(" :: a (List.fold_right
                            (fun arg acc -> ", " :: arg acc)
                            args
                            (") " :: con :: acc))
  in fun ty -> String.concat "" (go 0 ty [])

type tvs = | TyvarScope of (string -> typ option)
let tvs_lookup (TyvarScope f) s = f s
let tvs_from_map (m : typ StringMap.t) =
  TyvarScope (fun s -> StringMap.lookup s m)
let tvs_new_dynamic (new_ty : string -> typ) () =
  let cache = ref StringMap.empty in
  TyvarScope (fun s ->
    match StringMap.lookup s (deref cache) with
    | Some ty -> Some ty
    | None ->
      let ty = new_ty s in
      cache := Option.unwrap (StringMap.insert s ty (deref cache));
      Some ty)

let rec occurs_check (v : uvar ref) : typ -> unit m_result =
  function
  | CQVar _ -> Ok ()
  | CTCon (_, tys) ->
    let rec go =
      function
      | []         -> Ok ()
      | ty' :: tys -> let* () = occurs_check v ty' in go tys
    in go tys
  | CUVar v' ->
    if v == v' then
      Error (E "occurs check failed (cannot construct infinite type)")
    else
      match deref v' with
      | Known ty'                  -> occurs_check v ty'
      | Unknown (name', id', lvl') ->
        Ok (
          match deref v with
          | Known _             -> ()
          | Unknown (_, _, lvl) ->
            v' := Unknown (name', id', min lvl lvl')
        )

(* follow `Known`s until we get where we wanted *)
let ground : typ -> typ =
  let rec go ty (obligations : uvar ref list) =
    match ty with
    | CUVar r -> (
        match deref r with
        | Known ty -> go ty (r :: obligations)
        | _ -> (ty, obligations)
      )
    | _ -> (ty, obligations)
  in
  fun ty ->
    let (ty, obligations) = go ty [] in
    (* path compression *)
    List.iter (fun r -> r := Known ty) obligations;
    ty

let rec unify : typ -> typ -> unit m_result = fun t1 t2 ->
  (* FIXME: avoid physical equality on types? *)
  if t1 == t2 then Ok () else
  match (ground t1, ground t2) with
  | (CQVar qv, _) | (_, CQVar qv) ->
    let (QVar (name, a)) = qv in
    Error (E ("found CQVar (" ^ name ^ " " ^ string_of_int a ^ ") - should be impossible"))
  | (CUVar r, t') | (t', CUVar r) ->
    (* r must be Unknown *)
    if
      match t' with
      | CUVar r' -> r == r'
      | _        -> false
    then
      Ok ()
    else
      let* () = occurs_check r t' in
      Ok (r := Known t')
  | (CTCon (c1, p1), CTCon (c2, p2)) ->
    let (CCon (n1, id1)) = c1 and (CCon (n2, id2)) = c2 in
    if id1 <> id2 then
      Error (E ("cannot unify different type constructors: " ^ n1 ^ " != " ^ n2))
    else unify_all p1 p2
and unify_all : typ list -> typ list -> unit m_result = fun ts1 ts2 ->
  match (ts1, ts2) with
  | ([], []) -> Ok ()
  | (t1 :: ts1, t2 :: ts2) -> let* () = unify t1 t2 in unify_all ts1 ts2
  | _ -> Error (E "cannot unify different numbers of arguments")

let initial_ctx
  (next_var_id : unit -> var_id)
  (next_con_id : unit -> con_id)
=
  (* it's okay to reuse QVars for multiple variables here -
     they have the same ID, but this is only used to distinguish
     them during instantiation *)
  let a = QVar ("a", next_var_id ()) in
  let qa  = a :: [] and a = CQVar a in
  let b = QVar ("b", next_var_id ()) in
  let qab = b :: qa and b = CQVar b in
  let c = QVar ("c", next_var_id ()) in
  let qabc = c :: qab and c = CQVar c in
  let rec mk_ctx callback prefix =
    let ctx = ref Ctx.empty_layer in
    let provenance = Builtin prefix in
    let add name qvars ty =
      ctx := Ctx.layer_extend (deref ctx)
               (Binding (name, next_var_id (), provenance, qvars, ty))
    in
    let add_con name qvars params result =
      ctx := Ctx.layer_extend_con (deref ctx)
               (CBinding (name, next_var_id (), provenance, qvars, params, result))
    in
    let add_ty name arity =
      let con = CCon (name, next_con_id ()) in
      (ctx := Ctx.layer_extend_ty (deref ctx) (CDatatype (con, arity)); con)
    in
    let add_alias name def =
      let con = CCon (name, next_con_id ()) in
      (ctx := Ctx.layer_extend_ty (deref ctx) (CAlias (con, 0, [], def)); def)
    in
    let add_mod name m =
      ctx := Ctx.layer_extend_mod (deref ctx) Ctx.(CModule (name, m (prefix ^ name ^ ".")))
    in
    (callback add add_con add_ty add_alias add_mod; deref ctx)
  in
  let top_level callback = Ctx.(Ctx (mk_ctx callback (* prefix: *) "", None)) in
  top_level (fun add add_con add_ty add_alias add_mod ->
    let ty0 name = CTCon (add_ty name 0, [])
    and ty1 name = let c = add_ty name 1 in fun a -> CTCon (c, a :: [])
    and ty2 name = let c = add_ty name 2 in fun a b -> CTCon (c, a :: b :: [])
    in
    let (-->) = ty2 "->"
    and t_tuple = add_ty "*" (0 - 1) (* TODO: this feels janky? *)
    and t_char = ty0 "char" and t_int = ty0 "int"
    and t_string = ty0 "string" and t_bool = ty0 "bool"
    in
    let t_unit = add_alias "unit" (CTCon (t_tuple, [])) in
    add "&&"  [] (t_bool --> (t_bool --> t_bool));
    add "||"  [] (t_bool --> (t_bool --> t_bool));
    add "not" [] (t_bool --> t_bool);
    add "+"   [] (t_int --> (t_int --> t_int));
    add "-"   [] (t_int --> (t_int --> t_int));
    add "*"   [] (t_int --> (t_int --> t_int));
    add "/"   [] (t_int --> (t_int --> t_int));
    add ">="  [] (t_int --> (t_int --> t_bool));
    add "<="  [] (t_int --> (t_int --> t_bool));
    add ">"   [] (t_int --> (t_int --> t_bool));
    add "<"   [] (t_int --> (t_int --> t_bool));
    (* TODO: figure out a better alternative to polymorphic physical equality *)
    add "="   qa (a --> (a --> t_bool));
    add "<>"  qa (a --> (a --> t_bool));
    add "=="  qa (a --> (a --> t_bool));
    add "^"   [] (t_string --> (t_string --> t_string));
    add ";"   qa (t_unit --> (a --> a));
    add "min" [] (t_int --> (t_int --> t_int));
    add "fst" qab (CTCon (t_tuple, a :: b :: []) --> a);
    add "snd" qab (CTCon (t_tuple, a :: b :: []) --> b);
    add "int_of_string" [] (t_string --> t_int);
    add "string_of_int" [] (t_int --> t_string);
    add "int_of_char"   [] (t_char --> t_int);
    add "char_of_int"   [] (t_int --> t_char);
    add "print_endline" [] (t_string --> t_unit);
    add "prerr_endline" [] (t_string --> t_unit);
    add "invalid_arg" qa (t_string --> a);
    add "exit"        qa (t_int --> a);
    add_con "true"  [] [] t_bool;
    add_con "false" [] [] t_bool;
    (
      let t_ref = ty1 "ref" in
      add "ref"   qa (a --> t_ref a);
      add "deref" qa (t_ref a --> a);
      add ":="    qa (t_ref a --> (a --> t_unit))
    );
    let t_list = ty1 "list" in
    add_con "::" qa (a :: t_list a :: []) (t_list a);
    add     "::" qa (a --> (t_list a --> t_list a));
    add     "@"  qa (t_list a --> (t_list a --> t_list a));
    let t_option = ty1 "option" in
    add_con "None" qa [] (t_option a);
    add_con "Some" qa (a :: []) (t_option a);
    let t_result = ty2 "result" in
    add_con "Ok"    qab (a :: []) (t_result a b);
    add_con "Error" qab (b :: []) (t_result a b);
    add_mod "List" (mk_ctx (fun add _ _ _ _ ->
      add "rev" qa (t_list a --> t_list a);
      add "fold_left"  qab  ((a --> (b --> a)) --> (a --> (t_list b --> a)));
      add "fold_right" qab  ((b --> (a --> a)) --> (t_list b --> (a --> a)));
      add "map"        qab  ((a --> b) --> (t_list a --> t_list b));
      add "map2"       qabc ((a --> (b --> c)) --> (t_list a --> (t_list b --> t_list c)));
      add "mapi"       qab  ((t_int --> (a --> b)) --> (t_list a --> t_list b));
      add "find_opt"   qa   ((a --> t_bool) --> (t_list a --> t_option a));
      add "iter"       qa   ((a --> t_unit) --> (t_list a --> t_unit));
      add "length"     qa   (t_list a --> t_int);
      add "concat"     qa   (t_list (t_list a) --> t_list a);
      add "concat_map" qab  ((a --> t_list b) --> (t_list a --> t_list b));
      ()
    ));
    add_mod "Char" (mk_ctx (fun add _ _ _ _ ->
      add ">=" [] (t_char --> (t_char --> t_bool));
      add "<=" [] (t_char --> (t_char --> t_bool));
      add ">"  [] (t_char --> (t_char --> t_bool));
      add "<"  [] (t_char --> (t_char --> t_bool));
      ()
    ));
    add_mod "String" (mk_ctx (fun add _ _ _ _ ->
      add "length"  [] (t_string --> t_int);
      add "get"     [] (t_string --> (t_int --> t_char));
      add "sub"     [] (t_string --> (t_int --> (t_int --> t_string)));
      add "concat"  [] (t_string --> (t_list t_string --> t_string));
      add "make"    [] (t_int --> (t_char --> t_string));
      add "for_all" [] ((t_char --> t_bool) --> (t_string --> t_bool));
      add "filter"  [] ((t_char --> t_bool) --> (t_string --> t_string));
      ()
    ));
    let t_void = ty0 "void" in
    add_mod "Void" (mk_ctx (fun add _ _ _ _ ->
      add "absurd" qa (t_void --> a);
      ()
    ));
    add_mod "Fun" (mk_ctx (fun add _ _ _ _ ->
      add "id"   qa   (a --> a);
      add "flip" qabc ((a --> (b --> c)) --> (b --> (a --> c)));
      ()
    ));
    add_mod "Option" (mk_ctx (fun add _ _ _ _ ->
      add "map" qab ((a --> b) --> (t_option a --> t_option b));
      add "unwrap" qa (t_option a --> a);
      ()
    ));
    (
      let t_in_channel = ty0 "in_channel" in
      add_mod "In_channel" (mk_ctx (fun add _ _ _ _ ->
        add "open_text" [] (t_string --> t_in_channel);
        add "input_all" [] (t_in_channel --> t_string);
        add "close"     [] (t_in_channel --> t_unit);
        ()
      ))
    );
    add_mod "StringMap" (mk_ctx (fun add add_con add_ty _ _ ->
      let ty0 name = CTCon (add_ty name 0, [])
      and ty1 name = let c = add_ty name 1 in fun a -> CTCon (c, a :: [])
      in
      let t = ty1 "t" in
      add "empty"     qa  (t a);
      add "singleton" qa  (t_string --> (a --> t a));
      add "lookup"    qa  (t_string --> (t a --> t_option a));
      add "eql"       qa  ((a --> (a --> t_bool)) --> (t a --> (t a --> t_bool)));
      add "insert"    qa  (t_string --> (a --> (t a --> t_option (t a))));
      add "map"       qab ((t_string --> (a --> b)) --> (t a --> t b));
      add "fold"      qab ((a --> (t_string --> (b --> a))) --> (a --> (t b --> a)));
      let t_dup_err = ty0 "dup_err" in
      add_con "DupErr" [] (t_string :: []) t_dup_err;
      add "disjoint_union" qa (t a --> (t a --> t_result (t a) (t_dup_err)));
      ()
    ));
    add_mod "IntMap" (mk_ctx (fun add _ add_ty _ _ ->
      let ty1 name = let c = add_ty name 1 in fun a -> CTCon (c, a :: []) in
      let t = ty1 "t" in
      add "empty"  qa (t a);
      add "lookup" qa (t_int --> (t a --> t_option a));
      add "insert" qa (t_int --> (a --> (t a --> t a)));
      add "union"  qa (t a --> (t a --> t a));
      ()
    ));
    add_mod "Miniml" (mk_ctx (fun add _ _ _ _ ->
      add "log_level" [] t_int;
      add "debug" [] ((t_unit --> t_string) --> t_unit);
      add "trace" [] ((t_unit --> t_string) --> t_unit);
      add "argv" [] (t_unit --> t_list t_string);
      ()
    ));
    ()
  )

let preprocess_constructor_args
  (instantiate : qvar list -> unit -> typ -> typ)
  (mk_tuple : 'a list -> 'a) ctx name (args : 'a list option)
  : (cvar * typ list * typ * 'a list) m_result =
  let* cv =
    match Ctx.lookup_con name ctx with
    | None    -> Error (E ("constructor not in scope: " ^ name))
    | Some cv -> Ok cv
  in
  let (CBinding (_, _, _, qvars, param_tys, result_tys)) = cv in
  let instantiate = instantiate qvars () in
  let param_tys = List.map instantiate param_tys in
  let result_ty = instantiate result_tys in
  (* make sure we're applying the constructor to the right number of arguments.
     as a special case, passing the "wrong" number of arguments to a 1-param
     tuple, like `Some (1, 2)`, causes it to be treated as a tuple. *)
  let* args =
    let num_params = List.length param_tys in
    match (num_params, args) with
    | (0, None)              -> Ok []
    | (0, Some _)            -> Error (E ("constructor " ^ name ^ " must be applied to 0 arguments"))
    | (_, None)              -> Error (E ("constructor " ^ name ^ " must be applied to some arguments"))
    | (1, Some (args :: [])) -> Ok (args :: [])
    | (1, Some args)         -> Ok (mk_tuple args :: [])
    | (_, Some args)         -> if num_params = List.length args
                                then Ok args
                                else Error (E ("constructor " ^ name
                                               ^ " is applied to the wrong number of arguments"))
  in
  Ok (cv, param_tys, result_ty, args)

type elaborator
  = (unit -> int) (* next_var_id *)
  * (unit -> int) (* next_con_id *)
    (* elaborate a module in the context of those already compiled *)
  * (string -> Ast.ast -> core m_result)

let new_elaborator () : elaborator =
  let next_var_id = counter ()
  and next_uvar_name = counter ()
  and next_con_id = counter ()
  in
  let initial_ctx = initial_ctx next_var_id next_con_id in
  let (ty0, ty1, ty2) =
    let expect_arity n name =
      match Ctx.lookup_ty name initial_ctx with
      | Some (CDatatype (c, arity)) ->
        if arity = n then c
        else invalid_arg ("impossible: expected arity " ^ string_of_int n)
      | Some _ -> invalid_arg ("impossible: type " ^ name ^ " is not a datatype")
      | None -> invalid_arg ("impossible: no such type " ^ name)
    in
    ((fun name -> let c = expect_arity 0 name in            CTCon (c, [])),
     (fun name -> let c = expect_arity 1 name in fun a   -> CTCon (c, a :: [])),
     (fun name -> let c = expect_arity 2 name in fun a b -> CTCon (c, a :: b :: [])))
  in
  let (-->)    = ty2 "->"
  and t_tuple  = match Ctx.lookup_ty "*" initial_ctx with
                 | Some (CDatatype (c, _)) -> fun args -> CTCon (c, args)
                 | _ -> invalid_arg "impossible"
  and t_char   = ty0 "char"
  and t_int    = ty0 "int"
  and t_string = ty0 "string"
  and t_bool   = ty0 "bool"
  in
  let new_uvar lvl name () : typ =
    let id = next_uvar_name () in
    let name = match name with
               | Some n -> n
               (* TODO: do this calculation lazily? *)
               | None   -> string_of_int id
    in CUVar (ref (Unknown (name, id, lvl)))
  in
  let anon_var ty () : var =
    Binding ("<anonymous>", next_var_id (), User, [], ty)
  in
  let translate_ast_typ ctx tvs : Ast.typ -> typ m_result =
    (* substitute N types for N variables (QVars) in typ *)
    let rec subst (rho : (qvar * typ) list) typ =
      match ground typ with
      | CQVar (QVar (name, id)) ->
        (match List.find_opt (fun (QVar (_, id'), _) -> id = id') rho with
         | Some (_, ty) -> Ok ty
         | None -> Error (E ("impossible: unknown qvar " ^ name ^ " while substituting")))
      | CUVar _ -> Error (E "impossible: known types shouldn't have any unknown uvars?")
      | CTCon (c, args) ->
        let* args' = map_m error_monad (subst rho) args in
        Ok (CTCon (c, args'))
    in
    let rec go ctx =
      function
      | Ast.(TVar (s, sp)) ->
        (match tvs_lookup tvs s with
        | None -> Error (E ("(impossible?) binding not found for tvar: " ^ s
                            ^ " " ^ Token.describe_span sp))
        | Some ty -> Ok ty)
      | Ast.(TCon (MModule mod_name :: ms, name, sp, args)) ->
        (match Ctx.extend_open_over ctx mod_name with
         | None     -> Error (E ("module not in scope: " ^ mod_name))
         | Some ctx -> go ctx Ast.(TCon (ms, name, sp, args)))
      | Ast.(TCon ([], name, sp, args)) ->
        match Ctx.lookup_ty name ctx with
        | None -> Error (E ("type constructor not in scope: " ^ name))
        | Some decl ->
          let (CDatatype (con, arity) | CAlias (con, arity, _, _)) = decl in
          if arity <> List.length args && arity >= 0 then
            Error (E ("type constructor " ^ name ^ " " ^ Token.describe_span sp
                      ^ " expects " ^ string_of_int arity ^ " argument(s)"))
          else
            let* args' = map_m error_monad (go ctx) args in
            match decl with
            | CDatatype (_, _) -> Ok (CTCon (con, args'))
            | CAlias (_, _, params, definition) ->
              subst (List.map2 (fun p a -> (p, a)) params args') definition
    in go ctx
  in
  let translate_ast_typ_decl : (string list * string * Ast.typ_decl) list ->
                               Ctx.t -> Ctx.t m_result =
    (* we process a group of type declarations in several stages, to avoid
       creating cyclic type aliases:
       - extend the context with all the *declarations* of ADTs simultaneously;
       - traverse the type aliases serially, processing each's body in the
         current context and then extending the context;
       - extend the context with new term-level things (constructors & fields). *)
    fun decls ctx ->
    let* ((add_adts    : Ctx.t -> Ctx.t m_result),
          (add_aliases : Ctx.t -> Ctx.t m_result),
          (add_terms   : Ctx.t -> Ctx.t m_result))
    = fold_left_m error_monad (fun (prev_add_adts, prev_add_aliases, prev_add_terms)
                                   (ty_params, name, decl) ->
        let arity = List.length ty_params in
        let ty_params_qvs = List.map (fun s -> (s, QVar (s, next_var_id ()))) ty_params in
        let* (ty_params_map : typ StringMap.t) =
          fold_left_m error_monad (fun acc (s, qv) ->
            match StringMap.insert s (CQVar qv) acc with
            | Some map -> Ok map
            | None -> Error (E ("type declaration " ^ name ^
                                " has duplicate type parameter '" ^ s))
          ) StringMap.empty ty_params_qvs
        in
        let tvs = tvs_from_map ty_params_map in
        let ty_params = List.map snd ty_params_qvs in
        let* con = match Ctx.lookup_ty name ctx with
                   | Some _ -> (* this check is not strictly necessary *)
                               Error (E ("duplicate type name: " ^ name))
                   | None   -> Ok (CCon (name, next_con_id ()))
        in
        match decl with
        | Ast.(Datatype constructors) ->
          (* stage 1 *)
          let add_adts ctx =
            let* ctx = prev_add_adts ctx in
            Ok (Ctx.extend_ty ctx (CDatatype (con, arity)))
          in
          (* stage 3 *)
          let return_type = CTCon (con, List.map (fun qv -> CQVar qv) ty_params) in
          let add_terms ctx =
            let* ctx = prev_add_terms ctx in
            fold_left_m error_monad (fun ctx (name, param_tys) ->
              let* () = match Ctx.lookup_con name ctx with
                        | Some _ -> (* we don't yet know how to disambiguate *)
                                    Error (E ("duplicate constructor name: " ^ name))
                        | None   -> Ok () in
              let* param_tys' = map_m error_monad (translate_ast_typ ctx tvs)
                                                  param_tys
              in Ok (Ctx.extend_con ctx (
                CBinding (name,
                          next_var_id (),
                          User,
                          ty_params,
                          param_tys',
                          return_type)))
            ) ctx constructors
          in Ok (add_adts, prev_add_aliases, add_terms)
        | Ast.(Record []) ->
          Error (E "empty records are not allowed")
        | Ast.(Record fields) ->
          invalid_arg "TODO: records"
        | Ast.(Alias ty) ->
          (* step 2 *)
          let add_aliases ctx =
            let* ctx = prev_add_aliases ctx in
            let* ty' = translate_ast_typ ctx tvs ty in
            Ok (Ctx.extend_ty ctx (
              CAlias (con,
                      arity,
                      ty_params,
                      ty')))
          in Ok (prev_add_adts, add_aliases, prev_add_terms)
      ) ((fun c -> Ok c), (fun c -> Ok c), (fun c -> Ok c)) decls
    in
    add_adts ctx >>= add_aliases >>= add_terms
  in
  let generalize (lvl : level) : typ list -> qvar list * typ list =
    (* TODO: we don't need to return a new type list here *)
    let rec go ty qvars =
      match ty with
      | CQVar qv -> (qvars, ty)
      | CTCon (c, tys) ->
        let (qvars, tys) = go_list tys qvars in
        (qvars, (CTCon (c, tys)))
      | CUVar r ->
        match deref r with
        | Known ty -> go ty qvars
        | Unknown (name, id, lvl') ->
          if lvl' > lvl then
            let qv = QVar (name, next_var_id ()) in
            let qvars = qv :: qvars in
            r := Known (CQVar qv);
            (qvars, CQVar qv)
          else
            (qvars, ty)
    and go_list tys qvars =
      map_m state_monad go tys qvars
    in fun tys -> go_list tys []
  in
  let instantiate lvl (qvars : qvar list) () : typ -> typ =
    let qvars = List.map (fun var -> let (QVar (name, _)) = var in
                                     (var, new_uvar lvl (Some name) ())) qvars in
    let rec go ty = match ty with
                    | CQVar (QVar (n, id)) -> (
                      match List.find_opt (fun (QVar (_, id'), _) -> id = id') qvars with
                      | None -> new_uvar lvl (
                                  Some ("<error: unexpected QVar here: " ^ n ^ ">")) ()
                      | Some (_, uv) -> uv)
                    | CUVar r -> (
                      match deref r with
                      | Known ty -> go ty
                      | Unknown (_, _, _) -> ty)
                    | CTCon (c, tys) -> CTCon (c, List.map go tys)
    in go
  in
  (* Elaboration of patterns requires two phases. Originally we just traversed the pattern
     and added every variable we found to the context, with a new uvar for its type.
     The reason this doesn't work is because of 'or'-patterns, which require:
     (1) the set of variables bound in both branches be the same;
     (2) the resulting context contain only one copy of the variables;
     (3) each copy of a variable in the elaborated branches refer to the same var ID.
     So instead, elaboration proceeds in three steps:
     - traverse the pattern to determine the names of all bound variables
       (and checking consistency between branches);
     - create a new Var (with ids and new uvars for types) for each bound variable;
     - traverse the pattern again, translating each identifier to its corresponding Var.
     *)
  let pat_bound_vars : level -> Ast.pat -> var StringMap.t m_result =
    let rec go =
      function
      | POr (p1, p2) -> let* v1 = go p1 in
                        let* v2 = go p2 in
                        if StringMap.eql (fun () () -> true) v1 v2 then Ok v1
                        else Error (E "branches do not bind the same variables")
      | PTuple ps    -> go_list ps
      | PList ps     -> go_list ps
      | PCon (_, ps) -> (match ps with | Some ps -> go_list ps
                                       | None    -> Ok StringMap.empty)
      | PCharLit _ | PIntLit _ | PStrLit _
      | PWild        -> Ok StringMap.empty
      | PVar (v, _)  -> Ok (StringMap.singleton v ())
      | POpenIn (_, p)
      | PAsc (p, _)  -> go p
    and go_list pats =
      List.fold_left merge (Ok StringMap.empty) (List.map go pats)
    and merge ev1 ev2 =
      let* v1 = ev1 in
      let* v2 = ev2 in
      match StringMap.disjoint_union v1 v2 with
      | Ok v' -> Ok v'
      | Error (StringMap.(DupErr v)) -> Error (E "variable bound multiple times in the same pattern: v")
    in
    fun lvl pat ->
      let* bindings = go pat in
      (* NOTE: the order in which StringMap.map visits entries is unspecified --
         this is responsible for the difference in behavior between stage1 and stage2.
         It may be a good idea to change this to be consistent. *)
      Ok (StringMap.map
        (fun s () ->
          Binding (s, next_var_id (), User, [], new_uvar lvl (Some s) ())
        ) bindings)
  (* TODO: exhaustiveness checking? *)
  and infer_pat_with_vars lvl tvs ctx (bindings : var StringMap.t) :
                          Ast.pat -> (pat * typ) m_result =
    let rec go ctx =
      function
      | POr (p1, p2) -> let* (p1', ty1) = go ctx p1 in
                        let* (p2', ty2) = go ctx p2 in
                        let* () = unify ty1 ty2 in
                        Ok (POr (p1', p2'), ty1)
      | PTuple ps ->
        let* ps' = map_m error_monad (go ctx) ps in
        Ok (PTuple (List.map fst ps'),
            t_tuple (List.map snd ps'))
      | PList ps ->
        let ty_elem = new_uvar lvl None () in
        let* ps' = map_m error_monad
                          (fun p ->
                            let* (p', ty_p) = go ctx p in
                            let* () = unify ty_p ty_elem in
                            Ok p'
                          ) ps
        in Ok (PList ps', ground ty_elem)
      | PCon ((name, sp), args) ->
        (* TODO: use sp in errors *)
        let* (cv, param_tys, result_ty, args) =
          preprocess_constructor_args (instantiate lvl) (fun es -> PTuple es)
                                      ctx name args
        in
        let* args' = map_m error_monad (go ctx) args in
        let* () = unify_all param_tys (List.map snd args') in
        let args' = List.map fst args' in
        Ok (PCon (cv, Some args'), ground result_ty)
      | PCharLit c   -> Ok (PCharLit c, t_char)
      | PIntLit c    -> Ok (PIntLit c, t_int)
      | PStrLit c    -> Ok (PStrLit c, t_string)
      | PVar (s, sp) -> (match StringMap.lookup s bindings with
                         | None   -> Error (E ("unexpected variable in pattern: " ^ s
                                               ^ " " ^ Token.describe_span sp))
                         | Some v -> let (Binding (_, _, _, _, ty)) = v in
                                     Ok (PVar v, ty))
      | POpenIn (MModule name, p)
                     -> (match Ctx.extend_open_over ctx name with
                         | Some ctx -> go ctx p
                         | None     -> Error (E ("module not in scope: " ^ name)))
      | PAsc (p, ty) -> let* (p', ty1) = go ctx p in
                        let* ty' = translate_ast_typ ctx tvs ty in
                        let* () = unify ty1 ty' in
                        Ok (p', ty')
      | PWild        -> Ok (PWild, new_uvar lvl None ())
    in go ctx
  in
  (* TODO: enforce statically that this only extends the topmost layer of `ctx` *)
  let infer_pat lvl tvs : Ctx.t -> Ast.pat -> (Ctx.t * (pat * typ)) m_result =
    fun ctx pat ->
    let* bindings = pat_bound_vars lvl pat in
    let* pat' = infer_pat_with_vars lvl tvs ctx bindings pat in
    let ctx' = StringMap.fold (fun ctx _ v -> Ctx.extend ctx v) ctx bindings in
    Ok (ctx', pat')
  in
  (* TODO: enforce statically that this only extends the topmost layer of `ctx` *)
  let infer_pats lvl tvs : Ctx.t -> Ast.pat list -> (Ctx.t * (pat * typ) list) m_result =
    Fun.flip (map_m error_state_monad (Fun.flip (infer_pat lvl tvs)))
  in
  let rec infer lvl ctx : Ast.expr -> (expr * typ) m_result =
    function
    | Tuple es ->
      let* elab = map_m error_monad (infer lvl ctx) es in
      Ok (Tuple (List.map fst elab),
          t_tuple (List.map snd elab))
    | List es ->
      let ty_elem = new_uvar lvl None () in
      let* es' = map_m error_monad
                        (fun e ->
                          let* (e', ty_e) = infer lvl ctx e in
                          let* () = unify ty_e ty_elem in
                          Ok e'
                        ) es
      in Ok (List es', ground ty_elem)
    | Con ((name, sp), args) ->
      (* TODO: use sp in errors *)
      let* (cv, param_tys, result_ty, args) =
        preprocess_constructor_args (instantiate lvl) (fun es -> Tuple es)
                                    ctx name args
      in
      let* args' = map_m error_monad (infer lvl ctx) args in
      let* () = unify_all param_tys (List.map snd args') in
      let args' = List.map fst args' in
      Ok (Con (cv, Some args'), ground result_ty)
    | CharLit c -> Ok (CharLit c, t_char)
    | IntLit i -> Ok (IntLit i, t_int)
    | StrLit s -> Ok (StrLit s, t_string)
    | Var (s, sp) ->
            (match Ctx.lookup s ctx with
            | None -> Error (E ("variable not in scope: " ^ s ^ " " ^ Token.describe_span sp))
            | Some v ->
              let (Binding (_, _, _, qvars, ty)) = v in
              let ty = instantiate lvl qvars () ty in
              Ok (Var v, ty))
    | OpenIn (MModule name, e) -> (
      match Ctx.extend_open_over ctx name with
      | Some ctx -> infer lvl ctx e
      | None     -> Error (E ("module not in scope: " ^ name)))
    | App (e1, e2) ->
      let* (e1', ty_fun) = infer lvl ctx e1 in
      let* (e2', ty_arg) = infer lvl ctx e2 in
      let ty_res = new_uvar lvl None () in
      let* () = unify ty_fun (ty_arg --> ty_res) in
      Ok (App (e1', e2'), ground ty_res)
    | LetIn (bindings, e) ->
      let* (ctx', bindings') = infer_bindings lvl ctx bindings in
      let* (e', ty_e) = infer lvl ctx' e in
      Ok (LetIn (bindings', e'), ground ty_e)
    | Match (e_scrut, cases) ->
      let tvs = tvs_new_dynamic (fun s -> new_uvar lvl (Some s) ()) () in
      let ty_res = new_uvar lvl None () in
      let* (e_scrut', ty_scrut) = infer lvl ctx e_scrut in
      let* cases' =
        map_m error_monad
            (fun (pat, e) ->
              let* (ctx', (pat', ty_pat)) = infer_pat lvl tvs ctx pat in
              let* ()                     = unify ty_pat ty_scrut in
              let* (e', ty_e)             = infer lvl ctx' e      in
              let* ()                     = unify ty_e ty_res     in
              Ok (pat', e'))
            cases
      in
      Ok (
        Match (e_scrut', cases'),
        ground ty_res
      )
    | IfThenElse (e1, e2, e3) ->
      let* (e1', ty_cond) = infer lvl ctx e1      in
      let* ()             = unify ty_cond t_bool  in
      let* (e2', ty_then) = infer lvl ctx e2      in
      let* (e3', ty_else) = infer lvl ctx e3      in
      let* ()             = unify ty_then ty_else in
      Ok (IfThenElse (e1', e2', e3'), ground ty_then)
    | Fun (pats, e) ->
      let tvs = tvs_new_dynamic (fun s -> new_uvar lvl (Some s) ()) () in
      let* (ctx', pats') = infer_pats lvl tvs ctx pats in
      let* (e', ty_res) = infer lvl ctx' e in
      Ok (
        Fun (List.map fst pats', e'),
        List.fold_right (fun (_, ty1) ty2 -> (ty1 --> ty2)) pats' ty_res
      )
    | Function cases ->
      let tvs = tvs_new_dynamic (fun s -> new_uvar lvl (Some s) ()) () in
      let ty_res = new_uvar lvl None () in
      let ty_arg = new_uvar lvl None () in
      let* cases' =
        map_m error_monad
            (fun (pat, e) ->
              let* (ctx', (pat', ty_pat)) = infer_pat lvl tvs ctx pat in
              let* ()                     = unify ty_pat ty_arg       in
              let* (e', ty_e)             = infer lvl ctx' e          in
              let* ()                     = unify ty_e ty_res         in
              Ok (pat', e'))
            cases
      in
      let param = anon_var ty_arg () in
      Ok (
        Fun (PVar param :: [], Match (Var param, cases')),
        ground ty_arg --> ground ty_res
      )
  (* TODO: enforce statically that this only extends the topmost layer of `ctx` *)
  and infer_bindings lvl : Ctx.t -> Ast.bindings -> (Ctx.t * bindings) m_result =
    fun ctx (Bindings (is_rec, bindings)) ->
    let lvl' = lvl + 1 in
    let tvs = tvs_new_dynamic (fun s -> new_uvar lvl' (Some s) ()) () in
    (* for each binding, determine the variables bound by the head *)
    let* bindings =
      map_m error_monad
        (fun binding ->
          let (head, _, _, _) = binding in
          let* vars = pat_bound_vars lvl' head in
          Ok (vars, binding)
        ) bindings
    in
    (* combine all the bindings *)
    let* vars =
      let sets = List.map fst bindings in
      match fold_left_m error_monad StringMap.disjoint_union StringMap.empty sets with
      | Ok combined      -> Ok combined
      | Error (StringMap.(DupErr v)) ->
        Error (E ("variable bound multiple times in a group of definitions: " ^ v))
    in
    (* the context used for the bindings contains these variables iff the binding group
       is recursive *)
    let ctx_inner = if is_rec
                    then StringMap.fold (fun ctx _ v -> Ctx.extend ctx v) ctx vars
                    else ctx
    in
    (* infer each binding *)
    let* bindings =
      map_m error_monad
        (fun (bound_vars, binding) ->
          let (head, args, annot, rhs) = binding in
          let* (head', ty_head)   = infer_pat_with_vars lvl' tvs ctx bound_vars head in
          let* (ctx_inner, args') = infer_pats          lvl' tvs ctx_inner args      in
          let* (rhs', ty_rhs)     = infer               lvl'     ctx_inner rhs       in
          let* () =
            match annot with
            | None    -> Ok ()
            | Some ty -> let* ty' = translate_ast_typ ctx tvs ty in
                         unify ty_rhs ty'
          in
          let* () =
            unify ty_head (List.fold_right
                            (fun (_, ty1) ty2 -> (ty1 --> ty2))
                            args' ty_rhs)
          in
          let args' = List.map fst args' in
          let* can_generalize =
            (* TODO: the value restriction is a little looser than this *)
            if not (could_have_side_effects binding) then
              Ok true
            else if is_rec then
              Error (E "recursive bindings cannot have side effects")
            else
              Ok false
          in
          (* TODO: support type ascriptions in expression position *)
          Ok (bound_vars, can_generalize, ((head', args', None, rhs') (* : binding *)))
        ) bindings
    in
    let bound_vars : var list =
      (* flatten the maps in `bindings`; order is irrelevant, and we
         already know them to be disjoint *)
      List.fold_left (fun acc (bv, _, _) ->
        StringMap.fold (fun acc _ v -> v :: acc) acc bv
      ) [] bindings
    in
    (* conservatively assume that we can only generalize the whole group
       of definitions if every single one meets the criteria *)
    let can_generalize =
      List.fold_left (fun acc (_, cg, _) -> acc && cg) true bindings in
    let bound_vars : var list =
      if not can_generalize then
        (Miniml.debug (fun () ->
          "defined: " ^
            (String.concat "," (
              List.map (fun (Binding (n, _, _, _, ty)) ->
                n^":"^(show_ty ty)) bound_vars)));
         bound_vars)
      else
        let types = List.map (fun (Binding (_, _, _, _, ty)) -> ty) bound_vars in
        let (qvars, types) = generalize lvl types in
        Miniml.debug (fun () ->
          "defined(gen): " ^
            (String.concat "," (
              List.map (fun (Binding (n, _, _, _, ty)) ->
                n^":"^(show_ty ty)) bound_vars)));
        List.map2 (fun var ty ->
          let (Binding (name, id, prov, _, _)) = var in
          (* NOTE: What's going on here? We are allocating a "new" variable,
          but giving it the same ID as the above. This is fine, because (since
          generalization mutates the types it encounters, replacing the uvars
          with qvars) the references to this variable in the rhs's will all be
          of the form:
                        Var/PVar (Binding (name, id, [], ty'))
          where ty' is equivalent to ty modulo following `Known` links.
          Thus we can feel OK about saying that these two objects are "really"
          referring to the "same" variable binding, and we are just allowing it
          to have a more polymorphic type in the subsequent context.
          However, this does feel a little inelegant, and it would be nice to
          avoid it, e.g. by making the qvar list in Binding be a ref. *)
          (* TODO: maybe trim the qvars to those which appear in the ty? *)
          Binding (name, id, prov, qvars, ty)
        ) bound_vars types
    in
    let bindings = List.map (fun (_, _, binding) -> binding) bindings in
    Ok (
      List.fold_left Ctx.extend ctx bound_vars,
      Bindings (is_rec, bindings)
    )
  in
  (* TODO: enforce statically that this does not modify the parent of `ctx` *)
  let rec translate_decls ctx : Ast.decl list -> (Ctx.t * bindings list list) m_result =
    fun decls ->
    map_m error_state_monad
        (fun decl ctx ->
          match decl with
          | Ast.(Let bindings)    -> let* (ctx, bindings') = infer_bindings (* lvl = *) 0 ctx bindings in
                                     Ok (ctx, bindings' :: [])
          | Ast.(Types decls)     -> let* ctx = translate_ast_typ_decl decls ctx in
                                     Ok (ctx, [])
          | Ast.(Module (
              (name, sp), decls)) -> let ctx' = Ctx.extend_new_layer ctx in
                                     let* Ctx.(Ctx (new_layer, _), inner_bindings) = translate_decls ctx' decls in
                                     let ctx = Ctx.(extend_mod ctx (CModule (name, new_layer))) in
                                     (* TODO: use of List.concat here is not ideal for performance *)
                                     Ok (ctx, List.concat inner_bindings)
          | Ast.(Open (name, sp)) -> match Ctx.extend_open_under ctx name with
                                     | Some ctx -> Ok (ctx, [])
                                     | None     -> Error (E ("module not in scope: " ^ name))
        ) decls ctx
  in
  let current_ctx = ref initial_ctx in
  let elab_module module_name ast =
    let ctx = deref current_ctx in
    let ctx' = Ctx.extend_new_layer (deref current_ctx) in
    let* Ctx.(Ctx (new_layer, _), inner_bindings) = translate_decls ctx' ast in
    current_ctx := Ctx.(extend_mod ctx (CModule (module_name, new_layer)));
    Ok (List.concat inner_bindings)
  in
  (next_var_id, next_con_id, elab_module)

let next_var_id : elaborator -> int =
  fun (f, _, _) -> f ()

let elab : elaborator -> string -> Ast.ast -> core m_result =
  fun (_, _, elab_next) -> elab_next

let rec pat_local_vars : pat -> var list =
  function
  | POr (p, _)   -> pat_local_vars p (* will be the same in both branches *)
  | PList ps
  | PTuple ps    -> List.concat_map pat_local_vars ps
  | PCon (_, ps) -> List.concat_map pat_local_vars (Option.unwrap ps)
  | PCharLit _ | PIntLit _ | PStrLit _
  | PWild        -> []
  | PVar v       -> v :: []
  | POpenIn (_, _)
                 -> invalid_arg "POpenIn should no longer be present in Core.pat"
  | PAsc (_, vd) -> Void.absurd vd
