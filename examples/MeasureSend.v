From Stdlib Require Import String.
From Stdlib Require Lists.List.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
Import List.ListNotations.

From Qoreo Require Import Base Expr Choreography.
From Qoreo Require Import Network NetQasm.
From QoreoExamples Require Import Notation.
Require Extraction.

Import Choreography.
Import ExampleNotation.

Open Scope string_scope.

Module MeasureSend.
  Definition A : Actor.t := actor "alice"%string.
  Definition B : Actor.t := actor "bob"%string.

  Definition q : Var.t := var 0.
  Definition x : Var.t := var 1.
  Definition y : Var.t := var 2.

  Definition choreo : Choreography.t :=
    [
      let{A, q := New[false]};
      let{A, q := H[q]};
      let!{A, x := Measure[q]};
      send{A, x -> B, y}
    ].

  Definition parties : list Actor.t :=
    [A; B].

  Definition apps : option (list AppFile.t) :=
    ExampleExtraction.render_parties choreo parties.
End MeasureSend.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "measure_send_netqasm.ml" MeasureSend.apps.
