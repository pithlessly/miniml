(* Provides MiniML library functions not present in OCaml
   (to assist with bootstrapping). *)

module Option = struct
  let map = Option.map
  let unwrap = Option.get
end

let deref = (!)

module Miniml = struct
  let log_level =
    match Sys.getenv_opt "MINIML_BOOTSTRAP_DEBUG" with
    | Some "2" -> 2
    | Some "1" -> 1
    | _ -> 0

  let debug msg =
    if log_level < 1 then () else
      prerr_endline ("\x1b[33m(b debug)\x1b[m " ^ msg ())

  let trace msg =
    if log_level < 2 then () else
      prerr_endline ("\x1b[33m(b trace)\x1b[m " ^ msg ())
end
