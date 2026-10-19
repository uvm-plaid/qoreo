module T = Distributed_grover_netqasm
module W = Write_apps.Make (T)

let () =
  W.run
    ~apps:T.DistributedGrover.apps
    ~default_out_dir:"generated/grover"