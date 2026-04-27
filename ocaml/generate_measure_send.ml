module T = Measure_send_netqasm
module W = Write_apps.Make (T)

let () =
  W.run
    ~apps:T.MeasureSend.apps
    ~default_out_dir:"generated/measure_send"
