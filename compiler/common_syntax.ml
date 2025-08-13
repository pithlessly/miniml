type mod_expr = | MModule of string

type ('var, 'con, 'ty) pat =
                               | POr      of ('var, 'con, 'ty) pat
                                           * ('var, 'con, 'ty) pat
                               | PTuple   of ('var, 'con, 'ty) pat list
                               | PList    of ('var, 'con, 'ty) pat list
                               | PCon     of 'con
                                           * ('var, 'con, 'ty) pat list option
                               | PCharLit of char
                               | PIntLit  of int
                               | PStrLit  of string
                               | PVar     of 'var
                               | POpenIn  of mod_expr
                                           * ('var, 'con, 'ty) pat
                               | PAsc     of ('var, 'con, 'ty) pat * 'ty
                               | PWild
type ('var, 'con, 'ty) binding = ('var, 'con, 'ty) pat      (* head pattern *)
                               * ('var, 'con, 'ty) pat list (* argument patterns *)
                               * 'ty option                 (* return type annotation *)
                               * ('var, 'con, 'ty) expr     (* RHS *)
and  ('var, 'con, 'ty) bindings =
                               | Bindings of bool (* recursive? *)
                                           * ('var, 'con, 'ty) binding list
and  ('var, 'con, 'ty) expr =
                               | Tuple      of ('var, 'con, 'ty) expr list
                               | List       of ('var, 'con, 'ty) expr list
                               | Con        of 'con
                                             * ('var, 'con, 'ty) expr list option
                               | CharLit    of char
                               | IntLit     of int
                               | StrLit     of string
                               | Var        of 'var
                               | OpenIn     of mod_expr
                                             * ('var, 'con, 'ty) expr
                               | App        of ('var, 'con, 'ty) expr
                                             * ('var, 'con, 'ty) expr
                               | LetIn      of ('var, 'con, 'ty) bindings
                                             * ('var, 'con, 'ty) expr
                               | Match      of ('var, 'con, 'ty) expr
                                             * ( ('var, 'con, 'ty) pat
                                               * ('var, 'con, 'ty) expr
                                               ) list
                               | IfThenElse of ('var, 'con, 'ty) expr
                                             * ('var, 'con, 'ty) expr
                                             * ('var, 'con, 'ty) expr
                               | Fun        of ('var, 'con, 'ty) pat list
                                             * ('var, 'con, 'ty) expr
                               | Function   of ( ('var, 'con, 'ty) pat
                                               * ('var, 'con, 'ty) expr
                                               ) list

let could_have_side_effects : ('var, 'con, 'ty) binding -> bool =
  (* TODO: the real value restriction is smarter *)
  let rec go_expr =
    function
    | Tuple es
    | List es
    | Con (_, Some es) -> List.fold_left (fun acc e -> acc || go_expr e) false es
    | Con (_, None)
    | CharLit _
    | IntLit _
    | StrLit _
    | Var _
    | Fun (_, _) -> false
    | Function _ -> false
    | LetIn (Bindings (_, bs), e) ->
      List.fold_left (fun acc b -> acc || go b) false bs
      || go_expr e
    | _ -> true
  and go (_, args, _, e) = match args with
                           | _ :: _ -> false
                           | []     -> go_expr e
  in go
