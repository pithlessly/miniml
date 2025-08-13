type module_ = | CModule of string * layer
and  layer =    Core.var list
           *   Core.cvar list
           * Core.tydecl list
           *     module_ list
type t = | Ctx of layer * t option
let empty_layer : layer = ([], [], [], [])
let find : (layer -> 'a list) -> ('a -> string) -> string -> t -> 'a option =
  fun get_list get_name name ->
    let rec go (Ctx (top, parent)) =
      match List.find_opt (fun item -> get_name item = name) (get_list top) with
      | Some x -> Some x
      | None   -> match parent with | None -> None
                                    | Some p -> go p
    in go
let lookup     : string -> t ->    Core.var option = find (fun (vars, _, _, _) -> vars)
                                                          (fun Core.(Binding (name, _, _, _, _)) -> name)
let lookup_con : string -> t ->   Core.cvar option = find (fun (_, cvars, _, _) -> cvars)
                                                          (fun Core.(CBinding (name, _, _, _, _, _)) -> name)
let lookup_ty  : string -> t -> Core.tydecl option = find (fun (_, _, cons, _) -> cons)
                                                          (fun Core.(CDatatype (CCon (name, _), _) |
                                                                     CAlias    (CCon (name, _), _, _, _)) -> name)
let lookup_mod : string -> t ->     module_ option = find (fun (_, _, _, modules) -> modules)
                                                          (fun (CModule (name, _)) -> name)

let layer_extend     (vars, cvars, cons, modules) v   = (v :: vars, cvars, cons, modules)
let layer_extend_con (vars, cvars, cons, modules) cv  = (vars, cv :: cvars, cons, modules)
let layer_extend_ty  (vars, cvars, cons, modules) con = (vars, cvars, con :: cons, modules)
let layer_extend_mod (vars, cvars, cons, modules) m   = (vars, cvars, cons, m :: modules)
let update : (layer -> 'a -> layer) -> t -> 'a -> t =
  fun f (Ctx (top, parent)) x -> Ctx (f top x, parent)
let extend     = update layer_extend
let extend_con = update layer_extend_con
let extend_ty  = update layer_extend_ty
let extend_mod = update layer_extend_mod
let extend_open_over : t -> string -> t option =
  fun ctx mod_name ->
    Option.map (fun (CModule (_, layer)) -> Ctx (layer, Some ctx))
      (lookup_mod mod_name ctx)
let extend_open_under : t -> string -> t option =
  fun ctx mod_name ->
    let (Ctx (top_layer, parent)) = ctx in
    Option.map (fun (CModule (_, layer)) -> Ctx (top_layer, Some (Ctx (layer, parent))))
      (lookup_mod mod_name ctx)
let extend_new_layer : t -> t =
  fun ctx -> Ctx (empty_layer, Some ctx)
