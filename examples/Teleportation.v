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

Module Teleportation.
  Definition A : Actor.t := actor "alice"%string.
  Definition B : Actor.t := actor "bob"%string.

  Definition q : Var.t := var 0.
  Definition a : Var.t := var 1.
  Definition x : Var.t := var 2.
  Definition z : Var.t := var 3.
  Definition b : Var.t := var 4.

  Definition choreo : Choreography.t :=
    [
      (* Alice and Bob establish an entangled (EPR) pair. *)
      epr{A, a; B, b};

      (* Alice performs some local operations and obtains classical bits x and z. *)
      let{A, q := New[false]};
      let{A, q := H[q]};
      letp{A, (q, a) := CNOT[q, a]};
      let!{A, x := Measure[q]};
      let!{A, z := Measure[a]};

      (* Alice sends x and z to Bob. *)
      send{A, x -> B, x};
      send{A, z -> B, z};

      (* Bob uses x and z to update his qubit. *)
      let{B, b := if_ (ref z) (Z[b]) (ref b)};
      let{B, b := if_ (ref x) (X[b]) (ref b)}
    ].

  Definition parties : list Actor.t :=
    [A; B].

  Definition apps : option (list AppFile.t) :=
    ExampleExtraction.render_parties choreo parties.
End Teleportation.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "teleportation_netqasm.ml" Teleportation.apps.
