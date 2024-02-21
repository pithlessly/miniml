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

module StringMap : sig
  type 'a t
  val empty     : 'a t
  val singleton : string -> 'a -> 'a t
  val lookup    : string -> 'a t -> 'a option
  val eql       : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val insert    : string -> 'a -> 'a t -> 'a t option
  val map       : (string -> 'a -> 'b) -> 'a t -> 'b t
  val fold      : ('a -> string -> 'b -> 'a) -> ('a -> 'b t -> 'a)

  type dup_err = DupErr of string
  val disjoint_union : 'a t -> 'a t -> ('a t, dup_err) result
end = struct
  module Map = Map.Make(String)
  type 'a t = int * 'a Map.t
  let empty = (0, Map.empty)
  let singleton k v = (1, Map.singleton k v)
  let lookup k (_, entries) = Map.find_opt k entries
  let eql elem_eql (n1, entries1) (n2, entries2) = (n1 = n2) && Map.equal elem_eql entries1 entries2
  let insert k v (n, entries) =
    match Map.find_opt k entries with
    | None   -> Some (n + 1, Map.add k v entries)
    | Some v -> None
  let map f (n, entries) = (n, Map.mapi f entries)
  let fold f x (_, entries) = Map.fold (fun k v acc -> f acc k v) entries x
  type dup_err = DupErr of string
  exception DupExn of dup_err
  let disjoint_union (n1, entries1) (n2, entries2) =
    try Ok (n1 + n2, Map.union (fun k _ _ -> raise (DupExn (DupErr k))) entries1 entries2)
    with DupExn e -> Error e
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
