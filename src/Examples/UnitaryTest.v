From Stdlib Require Import String.
From Qoreo.Base Require Import Config. Import Unitary.
From Qoreo Require Import Expr.Expr Choreography.Choreography.
From Qoreo.Choreography Require Import Notation.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.
From Stdlib Require Import QArith.

Import List.ListNotations.
Import Unitary.
Open Scope string_scope.
Open Scope example_scope.

Module UnitaryTest.

  Definition tdag_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET q @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET q @ Alice ← Alice [- Unitary TGATE q -] ;;
    LET q @ Alice ← Alice [- Unitary Tdag q -] ;;
    LET q @ Alice ← Alice [- Unitary H q -] ;;
    Alice [- Meas q -].

  Definition sdag_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET q @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET q @ Alice ← Alice [- Unitary SGATE q -] ;;
    LET q @ Alice ← Alice [- Unitary Sdag q -] ;;
    LET q @ Alice ← Alice [- Unitary H q -] ;;
    Alice [- Meas q -].
  (*Definition cs_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target ← Alice [- Unitary H (New (Bit false)) -] ;;
    do (control, target) ← Alice [-- Unitary CS (Pair control target) -] ;;
    do (control, target) ← Alice [-- Unitary CS (Pair control target) -] ;;
    do target ← Alice [- Unitary H target -] ;;
    do r ← Alice [- Meas target -] ;;
    ret r.*)
  Definition cs_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET control @ Alice ← Alice [- New (Bit true) -] ;;
    LET target @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary CS (Pair control target) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary CS (Pair control target) -] ;;
    LET q @ Alice ← Alice [- Unitary H target -] ;;
    Alice [- Meas target -].

  Definition ct_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET control @ Alice ← Alice [- New (Bit true) -] ;;
    LET target @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary CT (Pair control target) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary CTdag (Pair control target) -] ;;
    LET target @ Alice ← Alice [- Unitary H target -] ;;
    Alice [- Meas target -].

  Definition csdag_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET control @ Alice ← Alice [- New (Bit true) -] ;;
    LET target @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary CS (Pair control target) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary CSdag (Pair control target) -] ;;
    LET target @ Alice ← Alice [- Unitary H target -] ;;
    Alice [- Meas target -].

  Definition ctdag_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET control @ Alice ← Alice [- New (Bit true) -] ;;
    LET target @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary CTdag (Pair control target) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary CT (Pair control target) -] ;;
    LET target @ Alice ← Alice [- Unitary H target -] ;;
    Alice [- Meas target -].


  (* RZ(pi/4) is equivalent to T up to global phase. *)
  Definition rz_t_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET q @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET q @ Alice ← Alice [- Unitary (RZ (pi/4)%Q) q -] ;; (*Pi/4%Q*)
    LET q @ Alice ← Alice [- Unitary Tdag q -] ;;
    LET q @ Alice ← Alice [- Unitary H q -] ;;
    Alice [- Meas q -].

  (* RZ(3*pi/7) followed by its inverse is identity. *)
  Definition rz_arbitrary_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET q @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET q @ Alice ← Alice [- Unitary (RZ (3#7)) q -] ;;
    LET q @ Alice ← Alice [- Unitary (RZ (-3#7)) q -] ;;
    LET q @ Alice ← Alice [- Unitary H q -] ;;
    Alice [- Meas q -].

  (* Expected P(1) = sin^2(3*pi/14). *)
  Definition rz_probability_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET q @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET q @ Alice ← Alice [- Unitary (RZ (3#7)) q -] ;;
    LET q @ Alice ← Alice [- Unitary H q -] ;;
    Alice [- Meas q -].

  (* CRZ(pi/4) followed by CRZ(-pi/4) is identity. *)
  Definition crz_inverse_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET control @ Alice ← Alice [- New (Bit true) -] ;;
    LET target @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary (CRZ (1#4)) (Pair control target) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary (CRZ (-1#4)) (Pair control target) -] ;;
    LET target @ Alice ← Alice [- Unitary H target -] ;;
    Alice [- Meas target -].

  (* Control = 1 activates CRZ(3*pi/7). *)
  (* Expected P(1) = sin^2(3*pi/14). *)
  Definition crz_probability_test (Alice : Actor.t) : Qoreo Choreography.t :=
    LET control @ Alice ← Alice [- New (Bit true) -] ;;
    LET target @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
    LET@ (control, target) @ Alice ← Alice [- Unitary (CRZ (3#7)) (Pair control target) -] ;;
    LET target @ Alice ← Alice [- Unitary H target -] ;;
    Alice [- Meas target -].

   Definition choreo : Qoreo Choreography.t :=
      LET! t_result @ "alice" ← tdag_test "alice" ;;
      LET! s_result @ "alice" ← sdag_test "alice" ;;
      LET! cs_result @ "alice" ← cs_test "alice" ;;
      LET! ct_result @ "alice" ← ct_test "alice" ;;
      LET! csdag_result @ "alice" ← csdag_test "alice" ;;
      LET! ctdag_result @ "alice" ← ctdag_test "alice" ;;

      LET! rz_t_result @ "alice" ← rz_t_test "alice" ;;
      LET! rz_arb_result @ "alice" ← rz_arbitrary_test "alice" ;;
      LET! rz_prob_result @ "alice" ← rz_probability_test "alice" ;;
      LET! crz_inv_result @ "alice" ← crz_inverse_test "alice" ;;
      LET! crz_prob_result @ "alice" ← crz_probability_test "alice" ;;
      "alice" [-
        Pair
      (Pair
        (Pair (Bang t_result) (Bang s_result))
        (Pair (Bang cs_result) (Bang ct_result)))
      (Pair
        (Pair (Bang csdag_result) (Bang ctdag_result))
        (Pair
          (Pair (Bang rz_t_result) (Bang rz_arb_result))
          (Pair
            (Bang rz_prob_result)
            (Pair (Bang crz_inv_result) (Bang crz_prob_result)))))-].
      (*"alice" [- Pair
                    (Pair
                      (Pair (Var t_result) (Var s_result))
                      (Pair (Var cs_result) (Var ct_result)))
                    (Pair (Var csdag_result) (Var ctdag_result))
              -]*)

  (*Definition parties : list Actor.t := ["alice"].*)

  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo NetSquid choreo.

End UnitaryTest.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Definition example_apps := UnitaryTest.apps.
Extraction "UnitaryTest.ml" example_apps.
