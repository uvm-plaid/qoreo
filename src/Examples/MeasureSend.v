From Stdlib Require Import String.
From Stdlib Require Lists.List.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
Import List.ListNotations.

From Qoreo Require Import Expr.Expr Choreography.Choreography.
From Qoreo Require Import Network NetQasm.
From Qoreo.Choreography Require Import Notation.
Require Extraction.

Import Choreography.

Open Scope string_scope.

Module MeasureSend.

  Definition A : Actor.t := "alice"%string.
  Definition B : Actor.t := "bob"%string.

  Definition choreo : Qoreo (list Var.t) :=
    do q ← A[- New (Bit false) -];;
    do q ← A[- Unitary H q -];;
    do x ← A[- Meas q -];;
    do y ← send A x B;;
    ret [y].

  Definition parties : list Actor.t :=
    [A; B].

  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo NetQASM parties choreo.
End MeasureSend.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "measure_send_netqasm.ml" MeasureSend.apps.
