module T = Dqft_netqasm
module W = Write_apps.Make (T)

let () =
  W.run
    ~apps:T.DQFT.apps
    ~default_out_dir:"generated/dqft"
