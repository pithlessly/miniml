type module_ = { name : string;
                 layer : layer }
and  layer =    Core.var list
           *   Core.cvar list
           *  Core.field list
           * Core.tydecl list
           *     module_ list
type t = { top : layer;
           parent : t option }
let empty_layer : layer = ([], [], [], [], [])
let find : (layer -> 'a list) -> ('a -> string) -> string -> t -> 'a option =
  fun get_list get_name name ->
    let rec go { top; parent } =
      match List.find_opt (fun item -> get_name item = name) (get_list top) with
      | Some x -> Some x
      | None   -> match parent with | None -> None
                                    | Some p -> go p
    in go
let lookup     : string -> t ->    Core.var option = find (fun (vars, _, _, _, _) -> vars)
                                                          (fun Core.(Binding (name, _, _, _, _)) -> name)
let lookup_con : string -> t ->   Core.cvar option = find (fun (_, cvars, _, _, _) -> cvars)
                                                          (fun Core.(CBinding (name, _, _, _, _, _)) -> name)
let lookup_fld : string -> t ->  Core.field option = find (fun (_, _, fields, _, _) -> fields)
                                                          (fun Core.(Field (name, _, _, _, _, _)) -> name)
let lookup_ty  : string -> t -> Core.tydecl option = find (fun (_, _, _, cons, _) -> cons)
                                                          (fun Core.(CNominal (CCon (name, _, _, _)) |
                                                                     CAlias   (CCon (name, _, _, _), _, _)) -> name)
let lookup_mod : string -> t ->     module_ option = find (fun (_, _, _, _, modules) -> modules)
                                                          (fun m -> m.name)

let layer_extend     (vars, cvars, fields, cons, modules) v   = (v :: vars, cvars, fields, cons, modules)
let layer_extend_con (vars, cvars, fields, cons, modules) cv  = (vars, cv :: cvars, fields, cons, modules)
let layer_extend_fld (vars, cvars, fields, cons, modules) f   = (vars, cvars, f :: fields, cons, modules)
let layer_extend_ty  (vars, cvars, fields, cons, modules) con = (vars, cvars, fields, con :: cons, modules)
let layer_extend_mod (vars, cvars, fields, cons, modules) m   = (vars, cvars, fields, cons, m :: modules)
let update : (layer -> 'a -> layer) -> t -> 'a -> t =
  fun f ctx x -> { top = f ctx.top x; parent = ctx.parent }
let extend     = update layer_extend
let extend_con = update layer_extend_con
let extend_fld = update layer_extend_fld
let extend_ty  = update layer_extend_ty
let extend_mod = update layer_extend_mod
let extend_open_over : t -> string -> t option =
  fun ctx mod_name ->
    Option.map (fun (m : module_) -> { top = m.layer; parent = Some ctx })
      (lookup_mod mod_name ctx)
let extend_open_under : t -> string -> t option =
  fun ctx mod_name ->
    Option.map (fun (m : module_) -> { top = ctx.top; parent = Some { top = m.layer; parent = ctx.parent } })
      (lookup_mod mod_name ctx)
let extend_new_layer : t -> t =
  fun ctx -> { top = empty_layer; parent = Some ctx }
