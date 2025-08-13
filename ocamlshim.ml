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

module String = struct
  include String
  let filter p s =
    String.to_seq s
    |> Seq.filter p
    |> String.of_seq
end

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

module Cont : sig
  type 'a prompt
  type ('a, 'b) cont
  val new_prompt : unit -> 'a prompt
  val prompt     : 'a prompt -> (unit -> 'a) -> 'a
  val control    : 'a prompt -> (('b, 'a) cont -> 'a) -> 'b
  val resume     : ('a, 'b) cont -> 'a -> 'b
end = struct
  module Sh = Effect.Shallow
  type ('a, 'b) cont = ('a, 'b) Sh.continuation
  type 'a prompt = {
    prompt  : (unit -> 'a) -> 'a;
    control : 'b. (('b, 'a) cont -> 'a) -> 'b;
  }
  let new_prompt (type a) () =
    let
      module M = struct
        type _ Effect.t +=
          | Control : (('b, a) cont -> a) -> 'b Effect.t
        let prompt f =
          Sh.continue_with (Sh.fiber f) () {
            retc = (fun x -> x);
            exnc = raise;
            effc = (function
              | Control c -> Some c
              | _ -> None);
          }
        let control h = Effect.perform (Control h)
      end
    in
    { prompt = M.prompt; control = M.control }
  let prompt p f = p.prompt f
  let control p h = p.control h
  let resume k a  = Sh.continue_with k a {
    retc = (fun x -> x);
    exnc = raise;
    effc = (fun _ -> None);
  }
end
