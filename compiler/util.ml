type error = | E of string
type 'a m_result = ('a, error) result

(* monadic operations *)

let map_m
  ((pure  : 'b list -> 'b_list_m),
   ((>>=) : 'b_m -> ('b -> 'b_list_m) -> 'b_list_m))
  (f : 'a -> 'b_m)
  : 'a list -> 'b_list_m =
  let rec go ys xs =
    match xs with
    | [] -> pure (List.rev ys)
    | x :: xs -> f x >>= fun y -> go (y :: ys) xs
  in go []
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

let (>>=) x f = snd error_monad x f
let (=<<) f x = (>>=) x f
let (let*) x f = (>>=) x f
let counter () =
  let i = ref 0 in
  (fun () ->
    let v = deref i in
    i := 1 + v;
    v)

let list_remove : ('a -> bool) -> 'a list -> ('a * 'a list) option =
  fun p ->
    let rec go acc =
      function
      | [] -> None
      | h :: xs ->
        if p h then
          Some (h, List.rev acc @ xs)
        else
          go (h :: acc) xs
    in go []

let list_split_at : int -> 'a list -> 'a list * 'a list =
  fun n xs ->
    let rec go n acc xs =
      if n > 0 then
        match xs with
        | [] -> invalid_arg "list is too long to split"
        | x :: xs -> go (n - 1) (x :: acc) xs
      else
        (List.rev acc, xs)
    in go n [] xs

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
  fun xs ->
    let rec sort len xs =
      if len <= 1 then xs else
        let prefix_len = (len + 1) / 2 in
        let suffix_len = len - prefix_len in
        let (prefix, suffix) = list_split_at prefix_len xs in
        merge (sort prefix_len prefix) (sort suffix_len suffix)
    in sort (List.length xs) xs
