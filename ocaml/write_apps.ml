module type EXTRACTED = sig
  type bool =
    | True
    | False

  type ascii =
    | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

  type string =
    | EmptyString
    | String of ascii * string

  type 'a option =
    | Some of 'a
    | None

  type 'a list =
    | Nil
    | Cons of 'a * 'a list

  module AppFile : sig
    type t = { party : string; source : string }
  end
end

module Make (T : EXTRACTED) = struct
  let rec coq_string_to_string = function
    | T.EmptyString -> ""
    | T.String (c, rest) -> String.make 1 (char_of_ascii c) ^ coq_string_to_string rest

  and char_of_ascii = function
    | T.Ascii (b0, b1, b2, b3, b4, b5, b6, b7) ->
        let bit b shift acc =
          match b with
          | T.True -> acc lor (1 lsl shift)
          | T.False -> acc
        in
        let code =
          0
          |> bit b0 0
          |> bit b1 1
          |> bit b2 2
          |> bit b3 3
          |> bit b4 4
          |> bit b5 5
          |> bit b6 6
          |> bit b7 7
        in
        Char.chr code

  let sanitize_filename s =
    let buf = Buffer.create (String.length s) in
    String.iter
      (fun ch ->
        match ch with
        | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> Buffer.add_char buf ch
        | _ -> Buffer.add_char buf '_')
      s;
    Buffer.contents buf

  let write_file path contents =
    let oc = open_out path in
    output_string oc contents;
    close_out oc

  let copy_file src dst =
    let ic = open_in_bin src in
    let oc = open_out_bin dst in
    Fun.protect
      ~finally:(fun () ->
        close_in ic;
        close_out oc)
      (fun () ->
        really_input_string ic (in_channel_length ic) |> output_string oc)

  let ensure_dir path =
    if not (Sys.file_exists path) then Unix.mkdir path 0o755

  let rec write_apps out_dir = function
    | T.Nil -> ()
    | T.Cons (app, rest) ->
        let { T.AppFile.party = party; T.AppFile.source = source } = app in
        let party = coq_string_to_string party in
        let source = coq_string_to_string source in
        let file_name = "app_" ^ sanitize_filename party ^ ".py" in
        write_file (Filename.concat out_dir file_name) source;
        write_apps out_dir rest

  let run ~apps ~default_out_dir =
    let apps =
      match apps with
      | T.Some xs -> xs
      | T.None ->
          prerr_endline "failed to generate NetQASM apps";
          exit 1
    in
    let out_dir =
      if Array.length Sys.argv > 1 then Sys.argv.(1) else default_out_dir
    in
    let parent = Filename.dirname out_dir in
    ensure_dir parent;
    ensure_dir out_dir;
    copy_file "python/qoreo_netqasm_runtime.py"
      (Filename.concat out_dir "qoreo_netqasm_runtime.py");
    write_apps out_dir apps
end
