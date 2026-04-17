module T = Teleportation_netqasm
module W = Write_apps.Make (T)

let () =
  W.run
    ~apps:T.TeleportationNetQasm.apps
    ~default_out_dir:"generated/teleportation"
