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
    do target ← Alice [- Unitary H (New (Bit false)) -] ;;
    do (control, target) ← Alice [-- Unitary CS (Pair control target) -] ;;
    do (control, target) ← Alice [-- Unitary CS (Pair control target) -] ;;
    do target ← Alice [- Unitary H target -] ;;
    do r ← Alice [- Meas target -] ;;
    ret r.

  Definition ct_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target ← Alice [- Unitary H (New (Bit false)) -] ;;
    do (control, target) ← Alice [-- Unitary CT (Pair control target) -] ;;
    do (control, target) ← Alice [-- Unitary CTdag (Pair control target) -] ;;
    do target ← Alice [- Unitary H target -] ;;
    do r ← Alice [- Meas target -] ;;
    ret r.

  Definition csdag_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target ← Alice [- Unitary H (New (Bit false)) -] ;;
    do (control, target) ← Alice [-- Unitary CS (Pair control target) -] ;;
    do (control, target) ← Alice [-- Unitary CSdag (Pair control target) -] ;;
    do target ← Alice [- Unitary H target -] ;;
    do r ← Alice [- Meas target -] ;;
    ret r.

  Definition ctdag_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target ← Alice [- Unitary H (New (Bit false)) -] ;;
    do (control, target) ← Alice [-- Unitary CTdag (Pair control target) -] ;;
    do (control, target) ← Alice [-- Unitary CT (Pair control target) -] ;;
    do target ← Alice [- Unitary H target -] ;;
    do r ← Alice [- Meas target -] ;;
    ret r.


  (* RZ(pi/4) is equivalent to T up to global phase. *)
  Definition rz_t_test (Alice : Actor.t) : Qoreo Var.t :=
    do q ← Alice [- Unitary H (New (Bit false)) -] ;;
    do q ← Alice [- Unitary (RZ (1#4)) q -] ;;
    do q ← Alice [- Unitary Tdag q -] ;;
    do q ← Alice [- Unitary H q -] ;;
    do r ← Alice [- Meas q -] ;;
    ret r.

  (* RZ(3*pi/7) followed by its inverse is identity. *)
  Definition rz_arbitrary_test (Alice : Actor.t) : Qoreo Var.t :=
    do q ← Alice [- Unitary H (New (Bit false)) -] ;;
    do q ← Alice [- Unitary (RZ (3#7)) q -] ;;
    do q ← Alice [- Unitary (RZ (-3#7)) q -] ;;
    do q ← Alice [- Unitary H q -] ;;
    do r ← Alice [- Meas q -] ;;
    ret r.

  (* Expected P(1) = sin^2(3*pi/14). *)
  Definition rz_probability_test (Alice : Actor.t) : Qoreo Var.t :=
    do q ← Alice [- Unitary H (New (Bit false)) -] ;;
    do q ← Alice [- Unitary (RZ (3#7)) q -] ;;
    do q ← Alice [- Unitary H q -] ;;
    do r ← Alice [- Meas q -] ;;
    ret r.

  (* CRZ(pi/4) followed by CRZ(-pi/4) is identity. *)
  Definition crz_inverse_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target ← Alice [- Unitary H (New (Bit false)) -] ;;
    do (control, target) ← Alice [-- Unitary (CRZ (1#4)) (Pair control target) -] ;;
    do (control, target) ← Alice [-- Unitary (CRZ (-1#4)) (Pair control target) -] ;;
    do target ← Alice [- Unitary H target -] ;;
    do r ← Alice [- Meas target -] ;;
    ret r.

  (* Control = 1 activates CRZ(3*pi/7). *)
  (* Expected P(1) = sin^2(3*pi/14). *)
  Definition crz_probability_test (Alice : Actor.t) : Qoreo Var.t :=
    do control ← Alice [- New (Bit true) -] ;;
    do target ← Alice [- Unitary H (New (Bit false)) -] ;;
    do (control, target) ← Alice [-- Unitary (CRZ (3#7)) (Pair control target) -] ;;
    do target ← Alice [- Unitary H target -] ;;
    do r ← Alice [- Meas target -] ;;
    ret r.

   Definition choreo : Qoreo (list Var.t) :=
      do t_result     ← tdag_test "alice" ;;
      do s_result     ← sdag_test "alice" ;;
      do cs_result    ← cs_test "alice" ;;
      do ct_result    ← ct_test "alice" ;;
      do csdag_result ← csdag_test "alice" ;;
      do ctdag_result ← ctdag_test "alice" ;;

      do rz_t_result     ← rz_t_test "alice" ;;
      do rz_arb_result   ← rz_arbitrary_test "alice" ;;
      do rz_prob_result  ← rz_probability_test "alice" ;;
      do crz_inv_result  ← crz_inverse_test "alice" ;;
      do crz_prob_result ← crz_probability_test "alice" ;;

      ret [ t_result; s_result;
            cs_result; ct_result; 
            csdag_result; ctdag_result;
            rz_t_result; rz_arb_result;
            rz_prob_result;
            crz_inv_result; crz_prob_result
            ].
      (*"alice" [- Pair
                    (Pair
                      (Pair (Var t_result) (Var s_result))
                      (Pair (Var cs_result) (Var ct_result)))
                    (Pair (Var csdag_result) (Var ctdag_result))
              -]*)

  Definition parties : list Actor.t := ["alice"].

  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo NetSquid parties choreo.

End UnitaryTest.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "unitary_test_netqasm.ml" UnitaryTest.apps.
