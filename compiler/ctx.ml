type module_ = { name : string;
                 layer : layer }
and  layer = {
  vars    :     Core.var list;
  cvars   :    Core.cvar list;
  fields  :   Core.field list;
  tydecls :  Core.tydecl list;
  modules :      module_ list;
}
type t = { top : layer;
           parent : t option }
let empty_layer : layer = { vars = []; cvars = []; fields = []; tydecls = []; modules = [] }
let find : (layer -> 'a list) -> ('a -> string) -> string -> t -> 'a option =
  fun get_list get_name name ->
    let rec go { top; parent } =
      match List.find_opt (fun item -> get_name item = name) (get_list top) with
      | Some x -> Some x
      | None   -> match parent with | None -> None
                                    | Some p -> go p
    in go
let lookup     : string -> t ->    Core.var option = find (fun l -> l.vars)
                                                          (fun v -> v.name)
let lookup_con : string -> t ->   Core.cvar option = find (fun l -> l.cvars)
                                                          (fun cv -> cv.name)
let lookup_fld : string -> t ->  Core.field option = find (fun l -> l.fields)
                                                          (fun field -> field.name)
let lookup_ty  : string -> t -> Core.tydecl option = find (fun l -> l.tydecls)
                                                          (fun Core.(CNominal con | CAlias (con, _, _)) -> con.name)
let lookup_mod : string -> t ->     module_ option = find (fun l -> l.modules)
                                                          (fun m -> m.name)

let layer_extend     { vars; cvars; fields; tydecls; modules } v   = { vars = v :: vars; cvars; fields; tydecls; modules }
let layer_extend_con { vars; cvars; fields; tydecls; modules } cv  = { vars; cvars = cv :: cvars; fields; tydecls; modules }
let layer_extend_fld { vars; cvars; fields; tydecls; modules } f   = { vars; cvars; fields = f :: fields; tydecls; modules }
let layer_extend_ty  { vars; cvars; fields; tydecls; modules } con = { vars; cvars; fields; tydecls = con :: tydecls; modules }
let layer_extend_mod { vars; cvars; fields; tydecls; modules } m   = { vars; cvars; fields; tydecls; modules = m :: modules }
let update : (layer -> 'a -> layer) -> t -> 'a -> t =
  fun f ctx x -> { top = f ctx.top x; parent = ctx.parent }
let extend     = update layer_extend
let extend_con = update layer_extend_con
let extend_fld = update layer_extend_fld
let extend_ty  = update layer_extend_ty
let extend_mod = update layer_extend_mod
let extend_open_over : t -> string -> t option =
  fun ctx mod_name ->
    lookup_mod mod_name ctx
    |> Option.map (fun m -> { top = m.layer; parent = Some ctx })
let extend_open_under : t -> string -> t option =
  fun ctx mod_name ->
    lookup_mod mod_name ctx
    |> Option.map (fun m -> { top = ctx.top; parent = Some { top = m.layer; parent = ctx.parent } })
let extend_new_layer : t -> t =
  fun ctx -> { top = empty_layer; parent = Some ctx }
