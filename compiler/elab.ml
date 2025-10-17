open Util
open Common_syntax
open Core

type span = Token.span
let err_sp = Token.err_sp

let show_ty : typ -> string =
  let rec go prec ty =
    let wrap_if thresh f =
      if prec <= thresh then f else
      fun acc -> "(" :: f (")" :: acc) in
    match ty with
    | CQVar qv -> fun acc -> "'" :: qv.name :: acc
    | CUVar r -> (match deref r with
                  | Known ty -> go prec ty
                  | Unknown (s, _, lvl) ->
                    fun acc -> ("?" ^ s ^ "(" ^ string_of_int lvl ^ ")") :: acc)
    | CTCon (CCon ("->", _, _, _), a :: b :: []) ->
      let a = go 1 a and b = go 0 b in
      wrap_if 0 (fun acc -> a (" -> " :: b acc))
    | CTCon (CCon ("*", _, _, _), []) -> fun acc -> "unit" :: acc
    | CTCon (CCon ("*", _, _, _), a :: args) ->
      let a = go 2 a and args = List.map (go 2) args in
      wrap_if 1 (fun acc -> a (List.fold_right
                                (fun arg acc -> " * " :: arg acc) args acc))
    | CTCon (CCon (con, _, _, _), []) -> fun acc -> con :: acc
    | CTCon (CCon (con, _, _, _), a :: []) ->
      let a = go 2 a in fun acc -> a (" " :: con :: acc)
    | CTCon (CCon (con, _, _, _), a :: args) ->
      let a = go 0 a and args = List.map (go 0) args in
      fun acc -> "(" :: a (List.fold_right
                            (fun arg acc -> ", " :: arg acc)
                            args
                            (") " :: con :: acc))
  in fun ty -> String.concat "" (go 0 ty [])

(* A type variable scope, or tvs, is responsible for assigning each syntactic type variable
   (just a string) to a type in the core (usually either a `CQVar` or `CUVar`).
   This can work in one of two ways:
   - A "static" type variable scope is used when we refer to type variables in a type declaration
     and only supports a given set of type variables fixed in advance (the parameters).
   - A "dynamic" type variable scope is used for processing type annotations inside terms, and
     it dynamically generates a new type variable every time one with a new name is requested.
 *)
type tvs = { lookup : string -> typ option; }
let tvs_from_map (m : typ StringMap.t) =
  { lookup = fun s -> StringMap.lookup s m }
let tvs_new_dynamic (new_ty : string -> typ) () =
  let cache = ref StringMap.empty in
  { lookup = fun s ->
    match StringMap.lookup s (deref cache) with
    | Some ty -> Some ty
    | None ->
      let ty = new_ty s in
      cache := Option.unwrap (StringMap.insert s ty (deref cache));
      Some ty }

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

let unexpected_qvar (qv : qvar) =
  E ("found CQVar (" ^ qv.name ^ " " ^ string_of_int qv.id ^ ") - should be impossible")

let rec unify : typ -> typ -> unit m_result = fun t1 t2 ->
  (* FIXME: avoid physical equality on types? *)
  if t1 == t2 then Ok () else
  match (ground t1, ground t2) with
  | (CQVar qv, _) | (_, CQVar qv) -> Error (unexpected_qvar qv)
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
    let (CCon (n1, id1, _, _)) = c1 and (CCon (n2, id2, _, _)) = c2 in
    if id1 <> id2 then
      Error (E ("cannot unify different type constructors: " ^ n1 ^ " != " ^ n2))
    else unify_all p1 p2
and unify_all : typ list -> typ list -> unit m_result = fun ts1 ts2 ->
  match (ts1, ts2) with
  | ([], []) -> Ok ()
  | (t1 :: ts1, t2 :: ts2) -> let* () = unify t1 t2 in unify_all ts1 ts2
  | _ -> Error (E "cannot unify different numbers of arguments")

type initial_ctx_types = {
  t_func   : typ -> typ -> typ;
  t_tuple  : typ list -> typ;
  t_unit   : typ;
  t_char   : typ;
  t_int    : typ;
  t_string : typ;
  t_bool   : typ;
  t_list   : typ -> typ;
}

type initial_ctx = {
  top_level : Ctx.t;
  types : initial_ctx_types;
}

let initial_ctx
  (next_var_id : unit -> var_id)
  (new_qvar    : string -> unit -> qvar)
  (next_con_id : unit -> con_id)
: initial_ctx =
  (* it's okay to reuse qvars for multiple variables here -
     they have the same ID, but this is only used to distinguish
     them during instantiation *)
  let a = new_qvar "a" () in
  let qa  = a :: [] and a = CQVar a in
  let b = new_qvar "b" () in
  let qab = b :: qa and b = CQVar b in
  let c = new_qvar "c" () in
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
      let con = CCon (name, next_con_id (), arity, CIDatatype) in
      (ctx := Ctx.layer_extend_ty (deref ctx) (CNominal con); con)
    in
    let add_alias name def =
      let arity = 0 in (* the stdlib only needs nullary aliases *)
      let con = CCon (name, next_con_id (), arity, CIAlias) in
      (ctx := Ctx.layer_extend_ty (deref ctx) (CAlias (con, [], def)); def)
    in
    let add_mod name m =
      ctx := Ctx.layer_extend_mod (deref ctx) { name; layer = m (prefix ^ name ^ ".") }
    in
    (callback add add_con add_ty add_alias add_mod; deref ctx)
  in
  let types : initial_ctx_types option ref = ref None in
  let top_level callback =
    let top = mk_ctx callback (* prefix: *) "" in
    { top_level = { top; parent = None };
      types = Option.unwrap (deref types) }
  in
  top_level (fun add add_con add_ty add_alias add_mod ->
    let ty0 name = CTCon (add_ty name 0, [])
    and ty1 name = let c = add_ty name 1 in fun a -> CTCon (c, a :: [])
    and ty2 name = let c = add_ty name 2 in fun a b -> CTCon (c, a :: b :: [])
    in
    let t_tuple_con = add_ty "*" (0 - 1) (* TODO: this feels janky? *) in
    let t_tuple ts = CTCon (t_tuple_con, ts) in
    let (-->) = ty2 "->"
    and t_unit = add_alias "unit" (t_tuple [])
    and t_char = ty0 "char"
    and t_int = ty0 "int"
    and t_string = ty0 "string"
    and t_bool = ty0 "bool"
    in
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
    add "fst" qab (t_tuple (a :: b :: []) --> a);
    add "snd" qab (t_tuple (a :: b :: []) --> b);
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
      add "init"       qa   (t_int --> ((t_int --> a) --> t_list a));
      add "rev"        qa   (t_list a --> t_list a);
      add "fold_left"  qab  ((a --> (b --> a)) --> (a --> (t_list b --> a)));
      add "fold_right" qab  ((b --> (a --> a)) --> (t_list b --> (a --> a)));
      add "map"        qab  ((a --> b) --> (t_list a --> t_list b));
      add "map2"       qabc ((a --> (b --> c)) --> (t_list a --> (t_list b --> t_list c)));
      add "mapi"       qab  ((t_int --> (a --> b)) --> (t_list a --> t_list b));
      add "filter"     qa   ((a --> t_bool) --> (t_list a --> t_list a));
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
    types := Some {
      t_func = (-->);
      t_tuple;
      t_unit;
      t_char;
      t_int;
      t_string;
      t_bool;
      t_list;
    };
    ()
  )

let preprocess_constructor_args
  (instantiate : qvar list -> unit -> typ -> typ)
  (mk_tuple : 'a list -> 'a)
  (ctx : Ctx.t)
  ((name, sp) : string * span)
  (args : 'a list option)
: (cvar * typ list * typ * 'a list) m_result =
  let* cv =
    match Ctx.lookup_con name ctx with
    | None    -> Error (err_sp ("constructor not in scope: " ^ name) sp)
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

type elaborator = {
  next_var_id : unit -> var_id;
  next_con_id : unit -> con_id;
  (* elaborate a module in the context of those already compiled *)
  elab_module : string -> Ast.ast -> core m_result;
}

let new_elaborator () : elaborator =
  let next_var_id = counter ()
  and next_uvar_name = counter ()
  and next_con_id = counter ()
  in
  let new_qvar name () : qvar = { name; id = next_var_id () } in
  let initial_ctx = initial_ctx next_var_id new_qvar next_con_id in
  let (-->)    = initial_ctx.types.t_func
  and t_tuple  = initial_ctx.types.t_tuple
  and t_char   = initial_ctx.types.t_char
  and t_int    = initial_ctx.types.t_int
  and t_string = initial_ctx.types.t_string
  and t_bool   = initial_ctx.types.t_bool
  and t_list   = initial_ctx.types.t_list
  in
  let new_uvar lvl name () : typ =
    let id = next_uvar_name () in
    let name = match name with
               | Some n -> n
               (* TODO: do this calculation lazily? *)
               | None   -> string_of_int id
    in CUVar (ref (Unknown (name, id, lvl)))
  in
  let new_uvars lvl name xs () =
    List.mapi (fun i x ->
      let name = match name with
                 | Some nm -> Some (nm ^ "[" ^ string_of_int i ^ "]")
                 | None    -> None
      in
      (x, new_uvar lvl name ())
    ) xs
  in
  let anon_var ty () : var =
    Binding ("<anonymous>", next_var_id (), User, [], ty)
  in
  let translate_ast_typ ctx (tvs : tvs) : Ast.typ -> typ m_result =
    (* substitute N types for N variables (qvars) in typ *)
    let rec subst (rho : (qvar * typ) list) typ =
      match ground typ with
      | CQVar qv ->
        (match List.find_opt (fun ((qv' : qvar), _) -> qv.id = qv'.id) rho with
         | Some (_, ty) -> Ok ty
         | None -> Error (E ("impossible: unknown qvar " ^ qv.name ^ " while substituting")))
      | CUVar _ -> Error (E "impossible: known types shouldn't have any unknown uvars?")
      | CTCon (c, args) ->
        let* args' = map_m error_monad (subst rho) args in
        Ok (CTCon (c, args'))
    in
    let rec go ctx =
      function
      | Ast.(TVar (s, sp)) ->
        (match tvs.lookup s with
        | None -> Error (err_sp ("(impossible?) binding not found for tvar: " ^ s) sp)
        | Some ty -> Ok ty)
      | Ast.(TCon (MModule mod_name :: ms, name, sp, args)) ->
        (match Ctx.extend_open_over ctx mod_name with
         | None     -> Error (E ("module not in scope: " ^ mod_name))
         | Some ctx -> go ctx Ast.(TCon (ms, name, sp, args)))
      | Ast.(TCon ([], name, sp, args)) ->
        match Ctx.lookup_ty name ctx with
        | None -> Error (E ("type constructor not in scope: " ^ name))
        | Some decl ->
          let (CNominal con | CAlias (con, _, _)) = decl in
          let (CCon (_, _, arity, _)) = con in
          if arity <> List.length args && arity >= 0 then
            Error (err_sp ("type constructor " ^ name ^ " expects "
                            ^ string_of_int arity ^ " argument(s)") sp)
          else
            let* args' = map_m error_monad (go ctx) args in
            match decl with
            | CNominal _ -> Ok (CTCon (con, args'))
            | CAlias (_, params, definition) ->
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
        let ty_params_qvs = List.map (fun s -> (s, new_qvar s ())) ty_params in
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
        (* check that this type constructor is not already in scope --
           this is not strictly necessary *)
        let* () = match Ctx.lookup_ty name ctx with
                  | Some _ -> Error (E ("duplicate type name: " ^ name))
                  | None   -> Ok ()
        in
        let make_con (info : con_info) : con =
          CCon (name, next_con_id (), arity, info)
        in
        match decl with
        | Ast.(Datatype constructors) ->
          let con = make_con CIDatatype in
          (* stage 1 *)
          let add_adts ctx =
            let* ctx = prev_add_adts ctx in
            Ok (Ctx.extend_ty ctx (CNominal con))
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
          (* we need to have the `con_info` immediately, but we don't actually want
             to calculate the field types until later, so we initially make it empty *)
          let fields_ref : field list ref = ref [] in
          let con = make_con (CIRecord fields_ref) in
          (* stage 1 *)
          let add_adts ctx =
            let* ctx = prev_add_adts ctx in
            Ok (Ctx.extend_ty ctx (CNominal con))
          in
          (* stage 3 *)
          let record_type = CTCon (con, List.map (fun qv -> CQVar qv) ty_params) in
          let add_terms ctx =
            let* ctx = prev_add_terms ctx in
            let* (_, fields') =
              map_m error_state_monad
                    (fun (name, sp, ty) idx ->
                      (* unlike with constructors, we are OK with shadowing of
                         record fields *)
                      let* field_ty = translate_ast_typ ctx tvs ty in
                      Ok (idx + 1, Field (name,
                                          next_var_id (),
                                          idx,
                                          ty_params,
                                          record_type,
                                          field_ty))
                    ) fields 0
            in
            (* update things *)
            fields_ref := fields';
            Ok (List.fold_left Ctx.extend_fld ctx fields')
          in Ok (add_adts, prev_add_aliases, add_terms)
        | Ast.(Alias ty) ->
          let con = make_con CIAlias in
          (* stage 2 *)
          let add_aliases ctx =
            let* ctx = prev_add_aliases ctx in
            let* ty' = translate_ast_typ ctx tvs ty in
            Ok (Ctx.extend_ty ctx (
              CAlias (con,
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
            let qv = new_qvar name () in
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
    let qvars = List.map (fun (qv : qvar) -> (qv, new_uvar lvl (Some qv.name) ())) qvars in
    let rec go ty = match ty with
                    | CQVar (qv : qvar) -> (
                      match List.find_opt (fun ((qv' : qvar), _) -> qv.id = qv'.id) qvars with
                      | None -> new_uvar lvl (
                                  Some ("<error: unexpected qvar here: " ^ qv.name ^ ">")) ()
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
  and infer_pat_with_vars_at lvl tvs ctx (bindings : var StringMap.t) :
                             typ -> Ast.pat -> pat m_result =
    let rec go ctx ty =
      function
      | POr (p1, p2) -> let* p1' = go ctx ty p1 in
                        let* p2' = go ctx ty p2 in
                        Ok (POr (p1', p2'))
      | PTuple ps ->
        let ps_and_types : (Ast.pat * typ) list = new_uvars lvl None ps () in
        let* () = unify ty (t_tuple (List.map snd ps_and_types)) in
        let* ps' = map_m error_monad (fun (p, ty) -> go ctx ty p) ps_and_types in
        Ok (PTuple ps')
      | PList ps ->
        let ty_elem = new_uvar lvl None () in
        let* () = unify ty (t_list ty_elem) in
        let* ps' = map_m error_monad (go ctx ty_elem) ps in
        Ok (PList ps')
      | PCon (name, args) ->
        (* TODO: it is possible to use the result type to aid in name lookup *)
        let* ((cv : cvar),
              (param_tys : typ list),
              (result_ty : typ),
              (args : Ast.pat list))
        = preprocess_constructor_args (instantiate lvl) (fun es -> PTuple es)
                                      ctx name args
        in
        (* TODO: perhaps change the signature of `preprocess_constructor_args`
           so that this is an input instead of an output *)
        let* () = unify result_ty ty in
        let* args' = map2_m error_monad (go ctx) param_tys args in
        Ok (PCon (cv, Some args'))
      | PCharLit c   -> let* () = unify ty t_char   in Ok (PCharLit c)
      | PIntLit c    -> let* () = unify ty t_int    in Ok (PIntLit c)
      | PStrLit c    -> let* () = unify ty t_string in Ok (PStrLit c)
      | PVar (s, sp) -> (match StringMap.lookup s bindings with
                         | None   -> Error (err_sp ("unexpected variable in pattern: " ^ s) sp)
                         | Some v -> let (Binding (_, _, _, qvars, ty_v)) = v in
                                     let () = match qvars with
                                              | [] -> ()
                                              | _  -> invalid_arg "impossible: qvars should be empty here" in
                                     let* () = unify ty_v ty in
                                     Ok (PVar v))
      | POpenIn (MModule name, p)
                     -> (match Ctx.extend_open_over ctx name with
                         | Some ctx -> go ctx ty p
                         | None     -> Error (E ("module not in scope: " ^ name)))
      | PAsc (p, asc_ty)
                     -> let* asc_ty' = translate_ast_typ ctx tvs asc_ty in
                        let* () = unify ty asc_ty' in
                        go ctx ty p
      | PWild        -> Ok PWild
    in go ctx
  in
  let infer_pat_with_vars lvl tvs ctx bindings pat : (pat * typ) m_result =
    let ty = new_uvar lvl None () in
    let* p' = infer_pat_with_vars_at lvl tvs ctx bindings ty pat in
    Ok (p', ty)
  in
  (* TODO: enforce statically that this only extends the topmost layer of `ctx` *)
  let infer_pat_at lvl tvs ctx ty pat : (Ctx.t * pat) m_result =
    let* bindings = pat_bound_vars lvl pat in
    let* pat' = infer_pat_with_vars_at lvl tvs ctx bindings ty pat in
    let ctx' = StringMap.fold (fun ctx _ v -> Ctx.extend ctx v) ctx bindings in
    Ok (ctx', pat')
  in
  let infer_pat lvl tvs ctx pat : (Ctx.t * (pat * typ)) m_result =
    let ty = new_uvar lvl None () in
    let* (ctx', p') = infer_pat_at lvl tvs ctx ty pat in
    Ok (ctx', (p', ty))
  in
  (* TODO: enforce statically that these only extend the topmost layer of `ctx` *)
  let infer_pats_at lvl tvs : Ctx.t -> (Ast.pat * typ) list -> (Ctx.t * pat list) m_result =
    Fun.flip (map_m error_state_monad (fun (pat, ty) ctx -> infer_pat_at lvl tvs ctx ty pat))
  and infer_pats lvl tvs : Ctx.t -> Ast.pat list -> (Ctx.t * (pat * typ) list) m_result =
    Fun.flip (map_m error_state_monad (fun pat ctx -> infer_pat lvl tvs ctx pat))
  in
  let rec infer' lvl ctx e : (expr * typ) m_result =
    let ty_res = new_uvar lvl None () in
    let* e' = infer_at lvl ctx ty_res e in
    Ok (e', ground ty_res)
  and infer_at lvl ctx ty : Ast.expr -> expr m_result =
    function
    | Tuple es ->
      let es_and_types : (Ast.expr * typ) list = new_uvars lvl None es () in
      let* () = unify ty (t_tuple (List.map snd es_and_types)) in
      let* es' = map_m error_monad (fun (e, ty) -> infer_at lvl ctx ty e) es_and_types in
      Ok (Tuple es')
    | List es ->
      let ty_elem = new_uvar lvl None () in
      let* () = unify ty (t_list ty_elem) in
      let* es' = map_m error_monad (infer_at lvl ctx ty_elem) es in
      Ok (List es')
    | Con (name, args) ->
      (* TODO: it is possible to use the result type to aid in name lookup *)
      let* ((cv : cvar),
            (param_tys : typ list),
            (result_ty : typ),
            (args : Ast.expr list))
      = preprocess_constructor_args (instantiate lvl) (fun es -> Tuple es)
                                    ctx name args
      in
      (* TODO: perhaps change the signature of `preprocess_constructor_args`
         so that this is an input instead of an output *)
      let* () = unify result_ty ty in
      let* args' = map2_m error_monad (infer_at lvl ctx) param_tys args in
      Ok (Con (cv, Some args'))
    | CharLit c -> let* () = unify ty t_char   in Ok (CharLit c)
    | IntLit i  -> let* () = unify ty t_int    in Ok (IntLit  i)
    | StrLit s  -> let* () = unify ty t_string in Ok (StrLit  s)
    | Var (s, sp) -> (
      match Ctx.lookup s ctx with
      | None -> Error (err_sp ("variable not in scope " ^ s) sp)
      | Some v ->
        let (Binding (_, _, _, qvars, ty_v)) = v in
        let ty_v = instantiate lvl qvars () ty_v in
        let* () = unify ty_v ty in
        Ok (Var v))
    | OpenIn (MModule name, e) -> (
      match Ctx.extend_open_over ctx name with
      | Some ctx -> infer_at lvl ctx ty e
      | None     -> Error (E ("module not in scope: " ^ name)))
    | Project (e, (field_name, sp)) ->
      let* (e', e_ty) = infer' lvl ctx e in
      let* (con_name, fields, args) =
        match ground e_ty with
        | CQVar qv -> Error (unexpected_qvar qv)
        | CUVar _  -> Error (err_sp "cannot project out of expression of unknown type" sp)
        | CTCon (CCon (con_name, _, _, con_info), args) ->
          match con_info with
          | CIAlias    -> Error (E "should be impossible to find a type alias here?")
          | CIDatatype -> Error (E "cannot project out of a datatype")
          | CIRecord fields -> Ok (con_name, fields, args)
      in
      let* field =
        match
          List.find_opt (fun field_decl ->
            let (Field (name, _, _, _, _, _)) = field_decl in
            name = field_name) (deref fields)
        with
        | None -> Error (E ("record " ^ con_name ^ " has no field " ^ field_name))
        | Some field -> Ok field
      in
      let (Field (_, _, _, qvars, record_ty, result_ty)) = field in
      let instantiate = instantiate lvl qvars () in
      let* () = unify e_ty (instantiate record_ty) in
      let* () = unify ty (instantiate result_ty) in
      Ok (Project (e', field))
    | MkRecord [] -> Error (E "empty records are not allowed")
    | MkRecord fields ->
      (* Mutable variable keeping track of what we know so far about this record.
         If the result type is already known to be a record, we can populate this
         immediately. Otherwise, we have to wait until we see the first field. *)
      let record_info_ref : (string * field list) option ref =
        ref (match ground ty with
             | CTCon (CCon (record_name, _, _, CIRecord (fs_ref : field list ref)), _)
                 -> Some (record_name, deref fs_ref)
             | _ -> None)
      in
      let* fields' = map_m error_monad (fun ((field_name, sp), rhs) ->
        (* Check whether `record_info_ref` is populated. *)
        let* (record_name, remaining_fields) =
          match deref record_info_ref with
          | Some info -> Ok info
          | None ->
            (* look up this field in the context *)
            let* field = match Ctx.lookup_fld field_name ctx with
                         | Some field -> Ok field
                         | None -> Error (err_sp ("unknown record field: " ^ field_name) sp)
            in
            let (Field (_, _, _, _, record_ty, _)) = field in
            match ground record_ty with
            | CTCon (CCon (record_name, _, _, CIRecord (fs_ref : field list ref)), _) ->
              (match deref fs_ref with
               | [] -> invalid_arg "impossible: record cannot have empty list of fields"
               | fields -> Ok (record_name, fields))
            | _ -> invalid_arg "impossible: field's record_ty has invalid structure"
        in
        (* Get the current field out of the list of remaining fields. *)
        let* field =
          match list_remove (fun (Field (n, _, _, _, _, _)) -> n = field_name) remaining_fields with
          | None -> Error (E ("record " ^ record_name ^ " has no field " ^ field_name))
          | Some (field, remaining_fields) ->
            record_info_ref := Some (record_name, remaining_fields);
            Ok field
        in
        let (Field (_, _, _, qvars, record_ty, field_ty)) = field in
        let instantiate = instantiate lvl qvars () in
        let* () = unify ty (instantiate record_ty) in
        let* rhs' = infer_at lvl ctx (instantiate field_ty) rhs in
        Ok (field, rhs')
      ) fields
      in
      let* () =
        match deref record_info_ref with
        | None -> invalid_arg "impossible: we never found out what record we're dealing with"
        | Some (_, []) -> Ok ()
        | Some (record_name, remaining_fields) ->
          Error (E ("initializer for record " ^ record_name ^ " is missing fields: " ^
                      String.concat ", "
                        (List.map (fun (Field (n, _, _, _, _, _)) -> n) remaining_fields)))
      in
      Ok (MkRecord fields')
    | App (e1, e2) ->
      let ty_arg = new_uvar lvl None () in
      let* e1' = infer_at lvl ctx (ty_arg --> ty) e1 in
      let* e2' = infer_at lvl ctx ty_arg          e2 in
      Ok (App (e1', e2'))
    | LetIn (bindings, e) ->
      let* (ctx', bindings') = infer_bindings lvl ctx bindings in
      let* e' = infer_at lvl ctx' ty e in
      Ok (LetIn (bindings', e'))
    | Match (e_scrut, cases) ->
      let tvs = tvs_new_dynamic (fun s -> new_uvar lvl (Some s) ()) () in
      let* (e_scrut', ty_scrut) = infer' lvl ctx e_scrut in
      let* cases' =
        map_m error_monad
            (fun (pat, e) ->
              let* (ctx', pat') = infer_pat_at lvl tvs ctx  ty_scrut pat in
              let* e'           = infer_at     lvl     ctx' ty       e   in
              Ok (pat', e'))
            cases
      in
      Ok (Match (e_scrut', cases'))
    | IfThenElse (e1, e2, e3) ->
      let* e1' = infer_at lvl ctx t_bool e1 in
      let* e2' = infer_at lvl ctx ty     e2 in
      let* e3' = infer_at lvl ctx ty     e3 in
      Ok (IfThenElse (e1', e2', e3'))
    | Fun (pats, e) ->
      let tvs = tvs_new_dynamic (fun s -> new_uvar lvl (Some s) ()) () in
      let return_ty = new_uvar lvl None () in
      let pats : (Ast.pat * typ) list = new_uvars lvl None pats () in
      let* () =
        unify ty (List.fold_right
                    (fun (_, ty1) ty2 -> (ty1 --> ty2))
                    pats return_ty)
      in
      let* (ctx', pats') = infer_pats_at lvl tvs ctx pats in
      let* e' = infer_at lvl ctx' return_ty e in
      Ok (Fun (pats', e'))
    | Function cases ->
      let tvs = tvs_new_dynamic (fun s -> new_uvar lvl (Some s) ()) () in
      let ty_res = new_uvar lvl None () in
      let ty_arg = new_uvar lvl None () in
      let* () = unify ty (ty_arg --> ty_res) in
      let* cases' =
        map_m error_monad
            (fun (pat, e) ->
              let* (ctx', pat') = infer_pat_at lvl tvs ctx  ty_arg pat in
              let* e'           = infer_at     lvl     ctx' ty_res e   in
              Ok (pat', e'))
            cases
      in
      (* desugar to (fun x -> match x with ...) *)
      let param = anon_var ty_arg () in
      Ok (Fun (PVar param :: [], Match (Var param, cases')))
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
          let* ty_rhs =
            match annot with
            | None    -> Ok (new_uvar lvl' None ())
            | Some ty -> translate_ast_typ ctx tvs ty
          in
          let* (head', ty_head)   = infer_pat_with_vars lvl' tvs ctx bound_vars head  in
          let* (ctx_inner, args') = infer_pats          lvl' tvs ctx_inner args       in
          let* rhs'               = infer_at            lvl'     ctx_inner ty_rhs rhs in
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
          let binding' : binding = (head', args', None, rhs') in
          Ok (bound_vars, can_generalize, binding')
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
  let ignore_all_but_the_top (ctx : Ctx.t) = ctx.top in
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
                                     let* (ctx'', inner_bindings) = translate_decls ctx' decls in
                                     let ctx = Ctx.extend_mod ctx {
                                       name;
                                       layer = ignore_all_but_the_top ctx''
                                     } in
                                     (* TODO: use of List.concat here is not ideal for performance *)
                                     Ok (ctx, List.concat inner_bindings)
          | Ast.(Open (name, sp)) -> match Ctx.extend_open_under ctx name with
                                     | Some ctx -> Ok (ctx, [])
                                     | None     -> Error (E ("module not in scope: " ^ name))
        ) decls ctx
  in
  let current_ctx = ref initial_ctx.top_level in
  let elab_module module_name ast =
    let ctx = deref current_ctx in
    let ctx' = Ctx.extend_new_layer (deref current_ctx) in
    let* (ctx'', inner_bindings) = translate_decls ctx' ast in
    current_ctx := Ctx.extend_mod ctx {
      name = module_name;
      layer = ignore_all_but_the_top ctx''
    };
    Ok (List.concat inner_bindings)
  in
  { next_var_id; next_con_id; elab_module }

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
