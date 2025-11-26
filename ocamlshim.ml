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

module String = struct
  include String
  let filter p s =
    String.to_seq s
    |> Seq.filter p
    |> String.of_seq
  let (<) (s1 : string) (s2 : string) = s1 < s2
  let (>) (s1 : string) (s2 : string) = s1 > s2
end

let (<=) : int -> int -> bool = fun a b -> a <= b
let (>=) : int -> int -> bool = fun a b -> a >= b
let (<)  : int -> int -> bool = fun a b -> a < b
let (>)  : int -> int -> bool = fun a b -> a > b

module Option = struct
  let map    = Option.map
  let unwrap = Option.get
  let bind   = Option.bind
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

module IntMap : sig
  type 'a t
  val empty  : 'a t
  val lookup : int -> 'a t -> 'a option
  val insert : int -> 'a -> 'a t -> 'a t
  val fold   : ('a -> int -> 'b -> 'a) -> ('a -> 'b t -> 'a)
  val union  : 'a t -> 'a t -> 'a t
  val iter   : (int -> 'a -> unit) -> 'a t -> unit
end = struct
  module Map = Map.Make(Int)
  type 'a t = 'a Map.t
  let empty = Map.empty
  let lookup = Map.find_opt
  let insert = Map.add
  let fold f x entries = Map.fold (fun k v acc -> f acc k v) entries x
  let union m1 m2 = Map.union (fun _ v1 _ -> Some v1) m1 m2
  let iter = Map.iter
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

  let argv () =
    Array.to_list Sys.argv
end

module Void : sig
  type void (* left abstract so that it is opaque to the totality checker *)
  val absurd : void -> 'a
end = struct
  type void = |
  let absurd (v : void) = match v with _ -> .
end
type void = Void.void
