module type EXTRACTED = sig
  module AppFile : sig
    type t = { party : string; source : string }
  end
end

module Make (T : EXTRACTED) = struct
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
    | [] -> ()
    | app :: rest ->
        let { T.AppFile.party = party; T.AppFile.source = source } = app in
        let file_name = "app_" ^ sanitize_filename party ^ ".py" in
        write_file (Filename.concat out_dir file_name) source;
        write_apps out_dir rest

  let run ~apps ~default_out_dir =
    let apps =
      match apps with
      | Some xs -> xs
      | None ->
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
