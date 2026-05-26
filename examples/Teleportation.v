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
Open Scope choreo_scope.

Module Teleportation.
  Definition A : Actor.t := actor "alice"%string.
  Definition B : Actor.t := actor "bob"%string.

  Definition q : Var.t := var 0.
  Definition a : Var.t := var 1.
  Definition x : Var.t := var 2.
  Definition z : Var.t := var 3.
  Definition b : Var.t := var 4.

  Definition choreo : Choreography.t :=
    <{
      (* Alice and Bob establish an entangled (EPR) pair. *)
      epr A,a; B,b;

      (* Alice performs some local operations and obtains classical bits x and z. *)
      let A,q := new false;
      let A,q := H q;
      letp A,(q,a) := CNOT q a;
      let! A,x := measure q;
      let! A,z := measure a;

      (* Alice sends x and z to Bob. *)
      A,x -> B,x;
      A,z -> B,z;

      (* Bob uses x and z to update his qubit. *)
      let B,b := if z then Z b else b end;
      let B,b := if x then X b else b end;
      let B,b := H b
    }>.

  Definition parties : list Actor.t :=
    [A; B].

  Definition apps : option (list AppFile.t) :=
    ExampleExtraction.render_parties choreo parties.
End Teleportation.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "teleportation_netqasm.ml" Teleportation.apps.
