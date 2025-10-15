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

let string_flat_map : (char -> string) -> string -> string =
  fun f s ->
    let n = String.length s in
    let rec go acc i =
      if i < 0 then acc
      else go (f (String.get s i) :: acc) (i - 1)
    in String.concat "" (go [] (n - 1))

let list_unwrap : 'a list -> 'a = function
  | x :: [] -> x
  | ls ->
      let len = List.length ls in
      invalid_arg ("expected singleton, but list has length" ^ string_of_int len)
