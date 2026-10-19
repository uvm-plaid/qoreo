module W = Write_apps.Make (struct
  module AppFile = AppFile
end)

let () =
  let executable = Filename.basename Sys.argv.(0) in
  let prefix = "generate_" in
  let example =
    String.sub executable (String.length prefix)
      (String.length executable - String.length prefix)
  in
  W.run ~apps:example_apps ~default_out_dir:(Filename.concat "generated" example)
