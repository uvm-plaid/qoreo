module T = B92_netqasm
module W = Write_apps.Make (T)

let () =
  W.run
    ~apps:T.B92.apps
    ~default_out_dir:"generated/b92"
