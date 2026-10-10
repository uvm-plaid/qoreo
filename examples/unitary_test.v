From Stdlib Require Import String.
From Qoreo Require Import Base Expr Choreography.
From QoreoExamples Require Import Notation.
Import ExampleExtraction.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Open Scope string_scope.
Open Scope example_scope.

(*Simple test case file I wrote to check functionality of a new added gate. When adding a new gate,
* Refer to: https://gate.directory/ to find the inverse cancelling operation if not intuitive
*)
Module UnitaryTest.


  Definition tdag_test (Alice : Actor.t) : Qoreo Var.t :=
    do q ← Alice [- Unitary H (New (Bit false)) -] ;;
    do q ← Alice [- Unitary TGATE q -] ;;
    do q ← Alice [- Unitary Tdag q -] ;;
    do q ← Alice [- Unitary H q -] ;;
    do r ← Alice [- Meas q -] ;;
    ret r.


 
  Definition sdag_test (Alice : Actor.t) : Qoreo Var.t :=
    do q ← Alice [- Unitary H (New (Bit false)) -] ;;
    do q ← Alice [- Unitary SGATE q -] ;;
    do q ← Alice [- Unitary Sdag q -] ;;
    do q ← Alice [- Unitary H q -] ;;
    do r ← Alice [- Meas q -] ;;
    ret r.


 
  Definition cs_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target  ← Alice [- Unitary H (New (Bit false)) -] ;;

    do (control, target) ←
      Alice [-- Unitary CS (Pair control target) -] ;;

    do (control, target) ←
      Alice [-- Unitary CS (Pair control target) -] ;;

    do target ← Alice [- Unitary H target -] ;;
    do r      ← Alice [- Meas target -] ;;

    ret r.

      Definition ct_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target  ← Alice [- Unitary H (New (Bit false)) -] ;;

    do (control, target) ←
      Alice [-- Unitary CT (Pair control target) -] ;;

    do (control, target) ←
      Alice [-- Unitary CTdag (Pair control target) -] ;;

    do target ← Alice [- Unitary H target -] ;;
    do r      ← Alice [- Meas target -] ;;

    ret r.


  Definition csdag_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target  ← Alice [- Unitary H (New (Bit false)) -] ;;

    do (control, target) ←
      Alice [-- Unitary CS (Pair control target) -] ;;

    do (control, target) ←
      Alice [-- Unitary CSdag (Pair control target) -] ;;

    do target ← Alice [- Unitary H target -] ;;
    do r      ← Alice [- Meas target -] ;;

    ret r.


  Definition ctdag_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target  ← Alice [- Unitary H (New (Bit false)) -] ;;

    do (control, target) ←
      Alice [-- Unitary CTdag (Pair control target) -] ;;

    do (control, target) ←
      Alice [-- Unitary CT (Pair control target) -] ;;

    do target ← Alice [- Unitary H target -] ;;
    do r      ← Alice [- Meas target -] ;;

    ret r.

   Definition choreo : Choreography.t :=
    mk (
      do t_result     ← tdag_test "alice" ;;
      do s_result     ← sdag_test "alice" ;;
      do cs_result    ← cs_test "alice" ;;
      do ct_result    ← ct_test "alice" ;;
      do csdag_result ← csdag_test "alice" ;;
      do ctdag_result ← ctdag_test "alice" ;;

      "alice" [- Pair
                    (Pair
                      (Pair (Var t_result) (Var s_result))
                      (Pair (Var cs_result) (Var ct_result)))
                    (Pair (Var csdag_result) (Var ctdag_result))
              -]
    ).

  Definition parties : list Actor.t :=
    ["alice"].


  Definition apps : option (list AppFile.t) :=
    ExampleExtraction.render_parties choreo parties.

End UnitaryTest.


Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "unitary_test_netqasm.ml" UnitaryTest.apps.