From Stdlib Require Import String.
From Stdlib Require Lists.List.
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
End Teleportation.

Module TeleportationNetQasm.
  Definition parties : list Actor.t :=
    [Teleportation.A; Teleportation.B].

  Definition render_party (p : Actor.t) : option AppFile.t :=
    match Network.epp p Teleportation.choreo with
    | Some proc =>
        Some {| AppFile.party := p; AppFile.source := render_app p proc |}
    | None => None
    end.

  Fixpoint render_parties (ps : list Actor.t) : option (list AppFile.t) :=
    match ps with
    | [] => Some []
    | p :: ps' =>
        match render_party p, render_parties ps' with
        | Some app, Some apps => Some (app :: apps)
        | _, _ => None
        end
    end.

  Definition apps : option (list AppFile.t) := render_parties parties.
End TeleportationNetQasm.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "teleportation_netqasm.ml" TeleportationNetQasm.apps.
