(* Provides MiniML library functions not present in OCaml
   (to assist with bootstrapping). *)

module Option = struct
  let map = Option.map
  let unwrap = Option.get
end

let deref = (!)
