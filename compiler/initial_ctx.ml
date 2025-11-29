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
  add       : string -> 'qvar list -> 'typ -> unit;
  add_con   : string -> 'qvar list -> 'typ list -> 'typ -> unit;
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
  types = { t_func = (@->); t_tuple; t_unit; t_char; t_int; t_string; t_bool; t_list };
  new_qvar;
  top_level = { add; add_con; ty0; ty1; ty2; add_mod; _ };
} : unit =
  (* it's okay to reuse qvars for multiple variables here -
     they have the same ID, but this is only used to distinguish
     them during instantiation *)
  let a = new_qvar "a" () in
  let b = new_qvar "b" () in
  let c = new_qvar "c" () in
  add "|>"  [a; b] (a @-> (a @-> b) @-> b);
  add "&&"  []     (t_bool @-> t_bool @-> t_bool);
  add "||"  []     (t_bool @-> t_bool @-> t_bool);
  add "not" []     (t_bool @-> t_bool);
  add "+"   []     (t_int @-> t_int @-> t_int);
  add "-"   []     (t_int @-> t_int @-> t_int);
  add "*"   []     (t_int @-> t_int @-> t_int);
  add "/"   []     (t_int @-> t_int @-> t_int);
  add ">="  []     (t_int @-> t_int @-> t_bool);
  add "<="  []     (t_int @-> t_int @-> t_bool);
  add ">"   []     (t_int @-> t_int @-> t_bool);
  add "<"   []     (t_int @-> t_int @-> t_bool);
  (* TODO: figure out a better alternative to polymorphic physical equality *)
  add "="   [a]    (a @-> a @-> t_bool);
  add "<>"  [a]    (a @-> a @-> t_bool);
  add "=="  [a]    (a @-> a @-> t_bool);
  add "^"   []     (t_string @-> t_string @-> t_string);
  add ";"   [a]    (t_unit @-> a @-> a);
  add "min" []     (t_int @-> t_int @-> t_int);
  add "fst" [a; b] (t_tuple [a; b] @-> a);
  add "snd" [a; b] (t_tuple [a; b] @-> b);
  add "int_of_string" []  (t_string @-> t_int);
  add "string_of_int" []  (t_int @-> t_string);
  add "int_of_char"   []  (t_char @-> t_int);
  add "char_of_int"   []  (t_int @-> t_char);
  add "print_endline" []  (t_string @-> t_unit);
  add "prerr_endline" []  (t_string @-> t_unit);
  add "invalid_arg"   [a] (t_string @-> a);
  add "exit"          [a] (t_int @-> a);
  add_con "true"  [] [] t_bool;
  add_con "false" [] [] t_bool;
  (
    let t_ref = ty1 "ref" in
    add "ref"   [a] (a @-> t_ref a);
    add "deref" [a] (t_ref a @-> a);
    add ":="    [a] (t_ref a @-> a @-> t_unit)
    );
  add_con "::" [a] [a; t_list a] (t_list a);
  (* TODO: remove this; have AST treat (::) in expr as a constructor *)
  add     "::" [a] (a @-> t_list a @-> t_list a);
  add     "@"  [a] (t_list a @-> t_list a @-> t_list a);
  let t_option = ty1 "option" in
  add_con "None" [a] []  (t_option a);
  add_con "Some" [a] [a] (t_option a);
  add_mod "Option" (fun { add; _ } ->
    add "map"    [a; b] ((a @-> b) @-> (t_option a @-> t_option b));
    add "unwrap" [a]    (t_option a @-> a);
    add "bind"   [a; b] (t_option a @-> (a @-> t_option b) @-> t_option b);
    ()
  );
  add_mod "List" (fun { add; _ } ->
    add "init"       [a]       (t_int @-> (t_int @-> a) @-> t_list a);
    add "rev"        [a]       (t_list a @-> t_list a);
    add "fold_left"  [a; b]    ((a @-> b @-> a) @-> (a @-> t_list b @-> a));
    add "fold_right" [a; b]    ((b @-> a @-> a) @-> (t_list b @-> a @-> a));
    add "map"        [a; b]    ((a @-> b) @-> (t_list a @-> t_list b));
    add "map2"       [a; b; c] ((a @-> b @-> c) @-> (t_list a @-> t_list b @-> t_list c));
    add "mapi"       [a; b]    ((t_int @-> a @-> b) @-> (t_list a @-> t_list b));
    add "for_all"    [a]       ((a @-> t_bool) @-> t_list a @-> t_bool);
    add "filter"     [a]       ((a @-> t_bool) @-> (t_list a @-> t_list a));
    add "find_opt"   [a]       ((a @-> t_bool) @-> (t_list a @-> t_option a));
    add "iter"       [a]       ((a @-> t_unit) @-> (t_list a @-> t_unit));
    add "length"     [a]       (t_list a @-> t_int);
    add "concat"     [a]       (t_list (t_list a) @-> t_list a);
    add "concat_map" [a; b]    ((a @-> t_list b) @-> (t_list a @-> t_list b));
    ()
  );
  let t_result = ty2 "result" in
  add_con "Ok"    [a; b] [a] (t_result a b);
  add_con "Error" [a; b] [b] (t_result a b);
  add_mod "Char" (fun { add; _ } ->
    add ">=" [] (t_char @-> t_char @-> t_bool);
    add "<=" [] (t_char @-> t_char @-> t_bool);
    add ">"  [] (t_char @-> t_char @-> t_bool);
    add "<"  [] (t_char @-> t_char @-> t_bool);
    ()
  );
  add_mod "String" (fun { add; _ } ->
    add "length"  [] (t_string @-> t_int);
    add "get"     [] (t_string @-> t_int @-> t_char);
    add "sub"     [] (t_string @-> t_int @-> t_int @-> t_string);
    add "concat"  [] (t_string @-> t_list t_string @-> t_string);
    add "make"    [] (t_int @-> t_char @-> t_string);
    add "for_all" [] ((t_char @-> t_bool) @-> (t_string @-> t_bool));
    add "filter"  [] ((t_char @-> t_bool) @-> (t_string @-> t_string));
    add "<"       [] (t_string @-> t_string @-> t_bool);
    add ">"       [] (t_string @-> t_string @-> t_bool);
    ()
  );
  let t_void = ty0 "void" in
  add_mod "Void" (fun { add; _ } ->
    add "absurd" [a] (t_void @-> a);
    ()
  );
  add_mod "Fun" (fun { add; _ } ->
    add "id"   [a]       (a @-> a);
    add "flip" [a; b; c] ((a @-> b @-> c) @-> (b @-> a @-> c));
    ()
  );
  (
    let t_in_channel = ty0 "in_channel" in
    add_mod "In_channel" (fun { add; _ } ->
      add "open_text" [] (t_string @-> t_in_channel);
      add "input_all" [] (t_in_channel @-> t_string);
      add "close"     [] (t_in_channel @-> t_unit);
      ()
    )
  );
  add_mod "StringMap" (fun { add; add_con; ty0; ty1; _ } ->
    let t = ty1 "t" in
    add "empty"     [a]    (t a);
    add "singleton" [a]    (t_string @-> a @-> t a);
    add "lookup"    [a]    (t_string @-> t a @-> t_option a);
    add "eql"       [a]    ((a @-> a @-> t_bool) @-> (t a @-> t a @-> t_bool));
    add "insert"    [a]    (t_string @-> a @-> t a @-> t_option (t a));
    add "map"       [a; b] ((t_string @-> a @-> b) @-> (t a @-> t b));
    add "fold"      [a; b] ((a @-> t_string @-> b @-> a) @-> (a @-> t b @-> a));
    let t_dup_err = ty0 "dup_err" in
    add_con "DupErr" [] [t_string] t_dup_err;
    add "disjoint_union" [a] (t a @-> t a @-> t_result (t a) t_dup_err);
    ()
  );
  add_mod "IntMap" (fun { add; ty1; _ } ->
    let t = ty1 "t" in
    add "empty"    [a]    (t a);
    add "is_empty" [a]    (t a @-> t_bool);
    add "lookup"   [a]    (t_int @-> t a @-> t_option a);
    add "insert"   [a]    (t_int @-> a @-> t a @-> t a);
    add "fold"     [a; b] ((a @-> t_int @-> b @-> a) @-> (a @-> t b @-> a));
    add "union"    [a]    (t a @-> (t a @-> t a));
    add "iter"     [a]    ((t_int @-> a @-> t_unit) @-> t a @-> t_unit);
    add "filter"   [a]    ((t_int @-> a @-> t_bool) @-> t a @-> t a);
    ()
  );
  add_mod "Miniml" (fun { add; _ } ->
    add "log_level" [] t_int;
    add "debug" [] ((t_unit @-> t_string) @-> t_unit);
    add "trace" [] ((t_unit @-> t_string) @-> t_unit);
    add "argv"  [] (t_unit @-> t_list t_string);
    ()
  );
  ()
