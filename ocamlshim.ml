(* Provides MiniML library functions not present in OCaml
   (to assist with bootstrapping). *)

let deref = (!)

module Char : sig
  val (<=) : char -> char -> bool
  val (>=) : char -> char -> bool
  val (<)  : char -> char -> bool
  val (>)  : char -> char -> bool
end = struct
  type cf = char -> char -> bool
  let (<=) : cf = fun a b -> a <= b
  let (>=) : cf = fun a b -> a >= b
  let (<)  : cf = fun a b -> a < b
  let (>)  : cf = fun a b -> a > b
end

let (<=) : int -> int -> bool = fun a b -> a <= b
let (>=) : int -> int -> bool = fun a b -> a >= b
let (<)  : int -> int -> bool = fun a b -> a < b
let (>)  : int -> int -> bool = fun a b -> a > b

module Option = struct
  let map = Option.map
  let unwrap = Option.get
end

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

module Void : sig
  type void (* left abstract so that it is opaque to the totality checker *)
  val absurd : void -> 'a
end = struct
  type void = |
  let absurd (v : void) = match v with _ -> .
end
type void = Void.void
