From Stdlib Require Import String.
From Qoreo Require Import Base Expr Choreography.
From QoreoExamples Require Import HOASNotation.
Import ExampleExtraction.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Open Scope string_scope.
Open Scope example_scope.

Module B92.
  (* One round of B92 quantum key distribution.
  Alice randomly prepares either |0⟩ (key bit 0) or |+⟩ (key bit 1) and
  sends the qubit to Bob.  Bob randomly selects the Z-basis (bit 0) or the
  X-basis (bit 1) by applying H before measuring.  The round is conclusive
  when Bob measures 1: measuring 1 in the Z-basis means Alice must have sent
  |+⟩, and measuring 1 in the X-basis means Alice must have sent |0⟩.  Bob
  announces his result to Alice so both parties know which rounds to keep. *)
  (* Returns ((alice_bit, alice_recv), (bob_basis, bob_result)).
     When bob_result = 1 the round is conclusive: alice_bit = NOT bob_basis. *)
  Definition b92_round (Alice Bob : Actor.t) : Qoreo ((Var.t * Var.t) * (Var.t * Var.t)) :=
  (* Alice randomly picks her key bit by preparing |+⟩ and measuring. *)
  do coin_a ← Alice [- Unitary H (New (Bit false)) -] ;;
  do a      ← Alice [- Meas coin_a -] ;;

  (* Alice prepares her transmission qubit: |0⟩ if a=0, |+⟩ if a=1. *)
  do q      ← Alice [- New (Bit false) -] ;;
  do q      ← Alice [- If a (Unitary H q) q -] ;;

  (* Alice sends the qubit to Bob over the quantum channel. *)
  do q_b    ← teleport Alice Bob q ;;

  (* Bob randomly picks his measurement basis. *)
  do coin_b ← Bob [- Unitary H (New (Bit false)) -] ;;
  do b      ← Bob [- Meas coin_b -] ;;

  (* Bob rotates into his chosen basis by applying H when b=1. *)
  do q_b    ← Bob [- If b (Unitary H q_b) q_b -] ;;

  (* Bob measures in his chosen basis.  A result of 1 means the round is
      conclusive: both Alice and Bob know they share the same key bit. *)
  do r      ← Bob [- Meas q_b -] ;;

  (* Bob announces the round result to Alice over the classical channel. *)
  do r_recv ← send Bob r Alice ;;

  ret ((a, r_recv), (b, r)).


  (* Three rounds of B92 followed by local key packaging.
     Alice packages ((r1,a1),(r2,a2),(r3,a3)) where ri is Bob's announcement
     and ai is her prepared bit.  Bob packages ((m1,~b1),(m2,~b2),(m3,~b3))
     where mi is his measurement result and ~bi is his inferred key bit.
     In each conclusive round (ri=1) the key bits agree: ai = ~bi. *)
  Definition choreo : Choreography.t :=
  mk (
    do (ad1, bd1) ← b92_round "alice" "bob" ;;
    do (a1, r1)   ← ret ad1 ;;
    do (b1, m1)   ← ret bd1 ;;
    do (ad2, bd2) ← b92_round "alice" "bob" ;;
    do (a2, r2)   ← ret ad2 ;;
    do (b2, m2)   ← ret bd2 ;;
    do (ad3, bd3) ← b92_round "alice" "bob" ;;
    do (a3, r3)   ← ret ad3 ;;
    do (b3, m3)   ← ret bd3 ;;
    do _ ← "alice" [- Pair (Pair (Pair (Var r1) (Var a1))
                                 (Pair (Var r2) (Var a2)))
                           (Pair (Var r3) (Var a3)) -] ;;
    "bob"          [- Pair (Pair (Pair (Var m1) (If (Var b1) (Bit false) (Bit true)))
                                 (Pair (Var m2) (If (Var b2) (Bit false) (Bit true))))
                           (Pair (Var m3) (If (Var b3) (Bit false) (Bit true))) -]
  ).


  Definition parties : list Actor.t :=
    ["alice"; "bob"].


  Definition apps : option (list AppFile.t) :=
    ExampleExtraction.render_parties choreo parties.
End B92.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "b92_netqasm.ml" B92.apps.
