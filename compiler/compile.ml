type backend = Elab.elaborator -> Core.core -> string

let backends : backend StringMap.t ref =
  ref StringMap.empty

let add_backend (backend_name : string) (b : backend) : unit =
  match StringMap.insert backend_name b (deref backends) with
  | Some backends' -> backends := backends'
  | None -> invalid_arg ("backend already exists: " ^ backend_name)

let compile (backend_name : string) : backend option =
  StringMap.lookup backend_name (deref backends)
