type error = | E of string
type 'a m_result = ('a, error) result

let (||>) (x, y) f = f x y

type 'a snoc = | Nil | Snoc of 'a snoc * 'a

module Snoc = struct
  let map f =
    let rec go = function
      | Nil -> Nil
      | Snoc (xs, x) -> Snoc (go xs, f x)
    in go

  (* tail-recursive *)
  let fold_right : ('a -> 'acc -> 'acc) -> 'a snoc -> 'acc -> 'acc =
    fun f ->
      let rec go xs acc =
        match xs with
        | Nil -> acc
        | Snoc (xs, x) -> go xs (f x acc)
      in go

  (* matches the structure of the list more closely *)
  let fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a snoc -> 'acc =
    fun f init ->
      let rec go = function
        | Nil -> init
        | Snoc (xs, x) -> f (go xs) x
      in go

  let sum : int snoc -> int =
    fold_left (fun x y -> x + y) 0

  let to_rev_list (xs : 'a snoc) : 'a list =
    fold_left (fun acc x -> x :: acc) [] xs

  let to_list_append (xs : 'a snoc) (ys : 'a list) : 'a list =
    fold_right (fun x ys -> x :: ys) xs ys

  let to_list (xs : 'a snoc) : 'a list =
    to_list_append xs []

  let from_list (xs : 'a list) : 'a snoc =
    List.fold_left (fun acc x -> Snoc (acc, x)) Nil xs

  let length : 'a snoc -> int =
    fun xs -> fold_right (fun _ n -> n + 1) xs 0
end

(* monadic operations *)

let map_m
  ((pure  : 'b list -> 'b_list_m),
   ((>>=) : 'b_m -> ('b -> 'b_list_m) -> 'b_list_m))
  (f : 'a -> 'b_m)
  : 'a list -> 'b_list_m =
  let rec go ys xs =
    match xs with
    | [] -> pure (Snoc.to_list ys)
    | x :: xs -> f x >>= fun y -> go (Snoc (ys, y)) xs
  in go Nil
let fold_left_m
  ((pure  : 'b -> 'b_m),
   ((>>=) : 'b_m -> ('b -> 'b_m) -> 'b_m))
  (f : 'b -> 'a -> 'b_m)
  : 'b -> 'a list -> 'b_m =
  let rec go acc xs =
    match xs with
    | [] -> pure acc
    | x :: xs -> f acc x >>= fun y -> go y xs
  in go
let for_m
  ((pure  : unit -> 'unit_m),
   ((>>=) : 'unit_m -> (unit -> 'unit_m) -> 'unit_m))
  (f : 'a -> 'unit_m)
  : 'a list -> 'unit_m =
  let rec go = function | [] -> pure ()
                        | x :: xs -> f x >>= fun () -> go xs
  in go

(* FIXME: this is not the best implementation in the world *)
let map2_m
  (monad : ('c list -> 'c_list_m) *
           ('c_m -> ('c -> 'c_list_m) -> 'c_list_m))
  (f : 'a -> 'b -> 'c_m)
  (xs : 'a list)
  (ys : 'b list)
  : 'c_list_m
= let thunks : (unit -> 'c_m) list = List.map2 (fun x y () -> f x y) xs ys in
  map_m monad (fun k -> k ()) thunks

let state_monad =
  let pure a    = (fun s -> (s, a))
  and (>>=) g f = (fun s -> let (s, a) = g s in f a s)
  in (pure, (>>=))
let error_monad =
  let pure a    = Ok a
  and (>>=) x f = match x with | Error e -> Error e | Ok a -> f a
  in (pure, (>>=))
let error_state_monad =
  let pure a    = (fun s -> Ok (s, a))
  and (>>=) g f = (fun s -> match g s with | Error e -> Error e | Ok (s, a) -> f a s)
  in (pure, (>>=))

let writer_bind (monoid_op : 'w -> 'w -> 'w)
  : 'w * 'a -> ('a -> 'w * 'b) -> 'w * 'b
  = fun (w1, x) f ->
      let (w2, y) = f x in
      (monoid_op w1 w2, y)
let writer_monad monoid_neu monoid_op =
  let pure x = (monoid_neu, x)
  and (>>=) = writer_bind monoid_op
  in (pure, (>>=))

let (>>=) x f = snd error_monad x f
let (=<<) f x = (>>=) x f
let (let*) x f = (>>=) x f
let counter () =
  let i = ref 0 in
  (fun () ->
    let v = deref i in
    i := 1 + v;
    v)

let list_remove (p : 'a -> bool) : 'a list -> ('a * 'a list) option =
  let rec go acc =
    function
    | [] -> None
    | h :: xs ->
      if p h then
        Some (h, Snoc.to_list_append acc xs)
      else
        go (Snoc (acc, h)) xs
  in go Nil

let list_split_at : int -> 'a list -> 'a list * 'a list =
  let rec go n acc xs =
    if n > 0 then
      match xs with
      | [] -> invalid_arg "list is too long to split"
      | x :: xs -> go (n - 1) (Snoc (acc, x)) xs
    else
      (Snoc.to_list acc, xs)
  in fun n xs -> go n Nil xs

let list_merge (cmp : 'a -> 'a -> int) : 'a list -> 'a list -> 'a list =
  let rec go xs ys =
    match (xs, ys) with
    | ([], _) -> ys
    | (_, []) -> xs
    | (x :: xs', y :: ys') ->
        if cmp x y > 0 then
          y :: go xs ys'
        else
          x :: go xs' ys
  in go

let list_sort (cmp : 'a -> 'a -> int) : 'a list -> 'a list =
  let merge = list_merge cmp in
  let rec sort len xs =
    if len <= 1 then xs else
      let prefix_len = (len + 1) / 2 in
      let suffix_len = len - prefix_len in
      let (prefix, suffix) = list_split_at prefix_len xs in
      merge (sort prefix_len prefix) (sort suffix_len suffix)
  in fun xs -> sort (List.length xs) xs

let list_equal (eql : 'a -> 'a -> bool) : 'a list -> 'a list -> bool =
  let rec go l1 l2 =
    match (l1, l2) with
    | ([],       [])       -> true
    | (a1 :: l1, a2 :: l2) -> if eql a1 a2 then go l1 l2 else false
    | _                    -> false
  in go

let try_zip : 'a list -> 'b list -> (('a * 'b) snoc, int * int) result =
  let rec go n acc l1 l2 =
    match (l1, l2) with
    | ([],       [])       -> Ok acc
    | (a1 :: l1, a2 :: l2) -> go (n + 1) (Snoc (acc, (a1, a2))) l1 l2
    | ([],       _)        -> Error (n, n + List.length l2)
    | (_,        [])       -> Error (n + List.length l1, n)
  in fun l1 l2 -> go 0 Nil l1 l2
