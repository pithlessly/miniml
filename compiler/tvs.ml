(* A type variable scope, or tvs, is responsible for assigning each syntactic type variable
   (just a string) to a type in the core (usually either a `CQVar` or `CUVar`).
   This can work in one of two ways:
   - A "static" type variable scope is used when we refer to type variables in a type declaration
     and only supports a given set of type variables fixed in advance (the parameters).
   - A "dynamic" type variable scope is used for processing type annotations inside terms, and
     it dynamically generates a new type variable every time one with a new name is requested.
 *)
type 't tvs = {
  lookup : string -> 't option;
  hole   : unit -> 't option;
}

let from_map : 'a StringMap.t -> 'a tvs =
  fun m -> {
    lookup = (fun s -> StringMap.lookup s m);
    hole = (fun () -> None);
  }

let new_dynamic : (string option -> unit -> 'a) -> unit -> 'a StringMap.t ref * 'a tvs =
  fun new_ty () ->
    let cache = ref StringMap.empty in
    let lookup s = 
      match StringMap.lookup s (deref cache) with
      | Some ty -> Some ty
      | None ->
        let ty = new_ty (Some s) () in
        cache := Option.unwrap (StringMap.insert s ty (deref cache));
        Some ty
    and hole () = Some (new_ty None ())
    in (cache, { lookup; hole })
