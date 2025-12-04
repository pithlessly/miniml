(* Type constructors that need to be passed in from the outside because the elaborator
 * needs to be aware of them (they have dedicated syntax). *)
type 'typ pervasive_types = {
  t_func   : 'typ -> 'typ -> 'typ;
  t_tuple  : 'typ list -> 'typ;
  t_unit   : 'typ;
  t_char   : 'typ;
  t_int    : 'typ;
  t_string : 'typ;
  t_bool   : 'typ;
  t_list   : 'typ -> 'typ;
}

(* Functions passed to a module *)
type ('qvar, 'typ) module_builder = {
  add       : string -> 'typ -> unit;
  add_con   : string -> 'typ list -> 'typ -> unit;
  ty0       : string -> 'typ;
  ty1       : string -> ('typ -> 'typ);
  ty2       : string -> ('typ -> 'typ -> 'typ);
  tyN       : string -> ('typ list -> 'typ);
  add_alias : string -> 'typ -> 'typ;
  add_mod   : string -> (('qvar, 'typ) module_builder -> unit) -> unit;
}

type 'typ prelude_setup = {
  types : 'typ pervasive_types;
  new_qvar : string -> unit -> 'typ;
  top_level : ('typ, 'typ) module_builder;
}

let initial_ctx {
  types = {
    t_func = (@->);
    t_tuple = tuple;
    t_unit = unit;
    t_char = char;
    t_int = int;
    t_string = string;
    t_bool = bool;
    t_list = list;
  };
  new_qvar;
  top_level = { add; add_con; ty0; ty1; ty2; add_mod; _ };
} : unit =
  (* it's okay to reuse qvars for multiple variables here -
     they have the same ID, but this is only used to distinguish
     them during instantiation *)
  let a = new_qvar "a" () in
  let b = new_qvar "b" () in
  let c = new_qvar "c" () in
  add "|>"  (a @-> (a @-> b) @-> b);
  add "&&"  (bool @-> bool @-> bool);
  add "||"  (bool @-> bool @-> bool);
  add "not" (bool @-> bool);
  add "+"   (int @-> int @-> int);
  add "-"   (int @-> int @-> int);
  add "*"   (int @-> int @-> int);
  add "/"   (int @-> int @-> int);
  add ">="  (int @-> int @-> bool);
  add "<="  (int @-> int @-> bool);
  add ">"   (int @-> int @-> bool);
  add "<"   (int @-> int @-> bool);
  (* TODO: figure out a better alternative to polymorphic physical equality *)
  add "="   (a @-> a @-> bool);
  add "<>"  (a @-> a @-> bool);
  add "=="  (a @-> a @-> bool);
  add "^"   (string @-> string @-> string);
  add ";"   (unit @-> a @-> a);
  add "min" (int @-> int @-> int);
  add "fst" (tuple [a; b] @-> a);
  add "snd" (tuple [a; b] @-> b);
  add "int_of_string" (string @-> int);
  add "string_of_int" (int @-> string);
  add "int_of_char"   (char @-> int);
  add "char_of_int"   (int @-> char);
  add "print_endline" (string @-> unit);
  add "prerr_endline" (string @-> unit);
  add "invalid_arg"   (string @-> a);
  add "exit"          (int @-> a);
  add_con "true"  [] bool;
  add_con "false" [] bool;
  (
    let ref = ty1 "ref" in
    add "ref"   (a @-> ref a);
    add "deref" (ref a @-> a);
    add ":="    (ref a @-> a @-> unit)
  );
  add_con "::" [a; list a] (list a);
  add     "@"  (list a @-> list a @-> list a);
  let option = ty1 "option" in
  add_con "None" []  (option a);
  add_con "Some" [a] (option a);
  add_mod "Option" (fun { add; _ } ->
    add "map"    ((a @-> b) @-> (option a @-> option b));
    add "unwrap" (option a @-> a);
    add "bind"   (option a @-> (a @-> option b) @-> option b);
    ()
  );
  add_mod "List" (fun { add; _ } ->
    add "init"       (int @-> (int @-> a) @-> list a);
    add "rev"        (list a @-> list a);
    add "fold_left"  ((a @-> b @-> a) @-> (a @-> list b @-> a));
    add "fold_right" ((b @-> a @-> a) @-> (list b @-> a @-> a));
    add "map"        ((a @-> b) @-> (list a @-> list b));
    add "map2"       ((a @-> b @-> c) @-> (list a @-> list b @-> list c));
    add "mapi"       ((int @-> a @-> b) @-> (list a @-> list b));
    add "for_all"    ((a @-> bool) @-> list a @-> bool);
    add "filter"     ((a @-> bool) @-> (list a @-> list a));
    add "find_opt"   ((a @-> bool) @-> (list a @-> option a));
    add "iter"       ((a @-> unit) @-> (list a @-> unit));
    add "length"     (list a @-> int);
    add "concat"     (list (list a) @-> list a);
    add "concat_map" ((a @-> list b) @-> (list a @-> list b));
    ()
  );
  let result = ty2 "result" in
  add_con "Ok"    [a] (result a b);
  add_con "Error" [b] (result a b);
  add_mod "Char" (fun { add; _ } ->
    add ">=" (char @-> char @-> bool);
    add "<=" (char @-> char @-> bool);
    add ">"  (char @-> char @-> bool);
    add "<"  (char @-> char @-> bool);
    ()
  );
  add_mod "String" (fun { add; _ } ->
    add "length"  (string @-> int);
    add "get"     (string @-> int @-> char);
    add "sub"     (string @-> int @-> int @-> string);
    add "concat"  (string @-> list string @-> string);
    add "make"    (int @-> char @-> string);
    add "for_all" ((char @-> bool) @-> (string @-> bool));
    add "filter"  ((char @-> bool) @-> (string @-> string));
    add "<"       (string @-> string @-> bool);
    add ">"       (string @-> string @-> bool);
    ()
  );
  let void = ty0 "void" in
  add_mod "Void" (fun { add; _ } ->
    add "absurd" (void @-> a);
    ()
  );
  add_mod "Fun" (fun { add; _ } ->
    add "id"   (a @-> a);
    add "flip" ((a @-> b @-> c) @-> (b @-> a @-> c));
    ()
  );
  (
    let in_channel = ty0 "in_channel" in
    add_mod "In_channel" (fun { add; _ } ->
      add "open_text" (string @-> in_channel);
      add "input_all" (in_channel @-> string);
      add "close"     (in_channel @-> unit);
      ()
    )
  );
  add_mod "StringMap" (fun { add; add_con; ty0; ty1; _ } ->
    let t = ty1 "t" in
    add "empty"     (t a);
    add "singleton" (string @-> a @-> t a);
    add "lookup"    (string @-> t a @-> option a);
    add "eql"       ((a @-> a @-> bool) @-> (t a @-> t a @-> bool));
    add "insert"    (string @-> a @-> t a @-> option (t a));
    add "map"       ((string @-> a @-> b) @-> (t a @-> t b));
    add "fold"      ((a @-> string @-> b @-> a) @-> (a @-> t b @-> a));
    let dup_err = ty0 "dup_err" in
    add_con "DupErr" [string] dup_err;
    add "disjoint_union" (t a @-> t a @-> result (t a) dup_err);
    ()
  );
  add_mod "IntMap" (fun { add; ty1; _ } ->
    let t = ty1 "t" in
    add "empty"    (t a);
    add "is_empty" (t a @-> bool);
    add "lookup"   (int @-> t a @-> option a);
    add "insert"   (int @-> a @-> t a @-> t a);
    add "map"      ((int @-> a @-> b) @-> (t a @-> t b));
    add "fold"     ((a @-> int @-> b @-> a) @-> (a @-> t b @-> a));
    add "union"    (t a @-> (t a @-> t a));
    add "iter"     ((int @-> a @-> unit) @-> t a @-> unit);
    add "filter"   ((int @-> a @-> bool) @-> t a @-> t a);
    ()
  );
  add_mod "Miniml" (fun { add; _ } ->
    add "log_level" int;
    add "debug" ((unit @-> string) @-> unit);
    add "trace" ((unit @-> string) @-> unit);
    add "argv"  (unit @-> list string);
    ()
  );
  ()
