module T = Conditional_test_netqasm
module W = Write_apps.Make (T)

let () =
  W.run
    ~apps:T.ConditionalTest.apps
    ~default_out_dir:"generated/conditional_test"