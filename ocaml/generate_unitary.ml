module T = Unitary_test_netqasm
module W = Write_apps.Make (T)

let () =
  W.run
    ~apps:T.UnitaryTest.apps
    ~default_out_dir:"generated/unitary_test"
