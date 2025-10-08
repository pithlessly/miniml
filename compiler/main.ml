open Util

let split_end (delim : char) (str : string) : (string * string) option =
  let n = String.length str in
  let rec go i =
    if i < 0 then None else
    if String.get str i = delim then
      Some (String.sub str 0 i, String.sub str (i + 1) (n - 1 - i))
    else
      go (i - 1)
  in go (n - 1)

let basename_and_extension (path : string) : string * string =
  let filename = match split_end '/' path with | None -> path
                                               | Some (_, f) -> f
  in
  match split_end '.' filename with
  | None -> (filename, "")
  (* a leading `.` is not considered to be part of a file extension *)
  | Some ("", ext) -> (filename, "")
  | Some (base, ext) -> (base, "." ^ ext)

let drop_1 = function
  | [] -> []
  | _ :: xs -> xs

let module_name_from_filename : string -> string option =
  fun str ->
    match basename_and_extension str with
    | (name, (".ml" | ".mini-ml")) ->
        let first_letter = String.get name 0 in
        if Lex.lower_letter first_letter && String.for_all Lex.lower name
        then Some (
          String.make 1 (char_of_int (int_of_char first_letter - 32))
          ^ String.sub name 1 (String.length name - 1)
        ) else None
    | _ -> None

let () =
  match
    let* (backend_name, (files : string list)) =
      match Miniml.argv () with
      | _ :: backend :: files -> Ok (backend, files)
      | _                     -> Error "Usage: miniml BACKEND [FILES ...]"
    in
    let* backend =
      match Compile.compile backend_name with
      | Some backend -> Ok backend
      | None -> Error ("No such backend: " ^ backend_name)
    in
    let* (files : (string * string) list) =
      map_m error_monad (fun file_path ->
        match module_name_from_filename file_path with
        | None -> Error ("Invalid name for a program file: " ^ file_path)
        | Some mod_name -> Ok (file_path, mod_name)
      ) files
    in
    let files : (string * string * string) list =
      List.map (fun (file_path, mod_name) ->
        let f = In_channel.open_text file_path in
        let text = In_channel.input_all f in
        In_channel.close f;
        (file_path, mod_name, text)
      ) files
    in
    let* (files : (string * string * Ast.ast) list) =
      map_m error_monad (fun (file_path, mod_name, text) ->
        match Lex.lex text with
        | Error (E e) -> Error ("Lex error: " ^ file_path ^ ": " ^ e)
        | Ok tokens ->
            match Parser.parse tokens with
            | Error (E e) -> Error ("Parse error: " ^ file_path ^ ": " ^ e)
            | Ok ast -> Ok (file_path, mod_name, ast)
      ) files
    in
    let elaborator = Elab.new_elaborator () in
    let* (all_core : Core.core list) =
      map_m error_monad (fun (file_path, mod_name, ast) ->
        match Elab.elab elaborator mod_name ast with
        | Error (E e) -> Error ("Type error: " ^ file_path ^ ": " ^ e)
        | Ok core -> Ok core
      ) files
    in
    Ok (backend elaborator (List.concat all_core))
  with
  | Error e -> (prerr_endline e; exit 1)
  | Ok result -> print_endline result
