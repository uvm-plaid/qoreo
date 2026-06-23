From Stdlib Require Import String.
From Qoreo Require Import Base Expr Choreography.
From QoreoExamples Require Import HOASNotation.

Open Scope string_scope.
Open Scope example_scope.


(* One round of B92 quantum key distribution.
   Alice randomly prepares either |0⟩ (key bit 0) or |+⟩ (key bit 1) and
   sends the qubit to Bob.  Bob randomly selects the Z-basis (bit 0) or the
   X-basis (bit 1) by applying H before measuring.  The round is conclusive
   when Bob measures 1: measuring 1 in the Z-basis means Alice must have sent
   |+⟩, and measuring 1 in the X-basis means Alice must have sent |0⟩.  Bob
   announces his result to Alice so both parties know which rounds to keep. *)
Definition b92_round (Alice Bob : Actor.t) : Qoreo Var.t :=
  (* Alice randomly picks her key bit by preparing |+⟩ and measuring. *)
  coin_a ← Alice [- Unitary H (New (Bit false)) -] ;;
  a      ← Alice [- Meas coin_a -] ;;

  (* Alice prepares her transmission qubit: |0⟩ if a=0, |+⟩ if a=1. *)
  q      ← Alice [- New (Bit false) -] ;;
  q      ← Alice [- If a (Unitary H q) q -] ;;

  (* Alice sends the qubit to Bob over the quantum channel. *)
  q_b    ← send Alice q Bob ;;

  (* Bob randomly picks his measurement basis. *)
  coin_b ← Bob [- Unitary H (New (Bit false)) -] ;;
  b      ← Bob [- Meas coin_b -] ;;

  (* Bob rotates into his chosen basis by applying H when b=1. *)
  q_b    ← Bob [- If b (Unitary H q_b) q_b -] ;;

  (* Bob measures in his chosen basis.  A result of 1 means the round is
     conclusive: both Alice and Bob know they share the same key bit. *)
  r      ← Bob [- Meas q_b -] ;;

  (* Bob announces the round result to Alice over the classical channel. *)
  send Bob r Alice.


(* Three rounds of B92.  In each conclusive round (Bob measures 1) Alice and
   Bob share the same key bit: Alice's prepared bit equals Bob's inferred bit. *)
Definition choreo : Choreography.t :=
  mk (
    _ ← b92_round "alice" "bob" ;;
    _ ← b92_round "alice" "bob" ;;
    b92_round "alice" "bob"
  ).

Eval compute in choreo.

Eval compute in (Network.epp "alice" choreo).
(*
  do 0  ← Unitary H (New (Bit false)) ;;
  do 1  ← Meas 0 ;;
  do 2  ← New (Bit false) ;;
  do 3  ← If 1 (Unitary H 2) 2 ;;
  do _  ← Send 3 "bob" ;;
  do 9  ← Receive "bob" ;;
  do 10 ← Unitary H (New (Bit false)) ;;
  do 11 ← Meas 10 ;;
  do 12 ← New (Bit false) ;;
  do 13 ← If 11 (Unitary H 12) 12 ;;
  do _  ← Send 13 "bob" ;;
  do 19 ← Receive "bob" ;;
  do 20 ← Unitary H (New (Bit false)) ;;
  do 21 ← Meas 20 ;;
  do 22 ← New (Bit false) ;;
  do 23 ← If 21 (Unitary H 22) 22 ;;
  do _  ← Send 23 "bob" ;;
  Receive "bob"
*)

Eval compute in (Network.epp "bob" choreo).
(*
  do 4  ← Receive "alice" ;;
  do 5  ← Unitary H (New (Bit false)) ;;
  do 6  ← Meas 5 ;;
  do 7  ← If 6 (Unitary H 4) 4 ;;
  do 8  ← Meas 7 ;;
  do _  ← Send 8 "alice" ;;
  do 14 ← Receive "alice" ;;
  do 15 ← Unitary H (New (Bit false)) ;;
  do 16 ← Meas 15 ;;
  do 17 ← If 16 (Unitary H 14) 14 ;;
  do 18 ← Meas 17 ;;
  do _  ← Send 18 "alice" ;;
  do 24 ← Receive "alice" ;;
  do 25 ← Unitary H (New (Bit false)) ;;
  do 26 ← Meas 25 ;;
  do 27 ← If 26 (Unitary H 24) 24 ;;
  do 28 ← Meas 27 ;;
  Send 28 "alice"
*)


Definition parties : list Actor.t :=
  ["alice"; "bob"].


Import ExampleExtraction.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Definition apps : option (list AppFile.t) :=
  ExampleExtraction.render_parties choreo parties.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "b92_netqasm.ml" apps.
