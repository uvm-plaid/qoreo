From Stdlib Require Import String.
From Qoreo Require Import Base.Config Expr.Expr Choreography.Choreography.
Import Config.Unitary.
Import Expr.
From Qoreo.Choreography Require Import Notation.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Import List.ListNotations.
Open Scope list_scope.

Open Scope string_scope.
Open Scope example_scope.


Module B92.


  Definition bneg (e : Expr.t) : Expr.t :=
    If e (Bit false) (Bit true).

  (* One round of B92 quantum key distribution.
  Alice randomly prepares either |0⟩ (key bit 0) or |+⟩ (key bit 1) and
  sends the qubit to Bob.  Bob randomly selects the Z-basis (bit 0) or the
  X-basis (bit 1) by applying H before measuring.  The round is conclusive
  when Bob measures 1: measuring 1 in the Z-basis means Alice must have sent
  |+⟩, and measuring 1 in the X-basis means Alice must have sent |0⟩.  Bob
  announces his result to Alice so both parties know which rounds to keep. *)
  (* Returns ((alice_recv, alice_bit), (bob_result, ~bob_basis)).
     When bob_result = 1 the round is conclusive: alice_bit = NOT bob_basis. *)
  Definition b92_round (Alice Bob : Actor.t) :=

  (* Alice randomly picks her key bit by preparing |+⟩ and measuring. *)
  LET  coin @ Alice ← Alice [- Unitary H (New (Bit false)) -] ;;
  LET! a    @ Alice ← Alice [- Meas coin -] ;;

  (* Alice prepares her transmission qubit: |0⟩ if a=0, |+⟩ if a=1. *)
  LET q @ Alice ← Alice [- New (Bit false) -] ;;
  LET q @ Alice ← Alice [- If a (Unitary H q) q -] ;;

  (* Alice sends the qubit to Bob over the quantum channel. *)
  LET q @ Bob   ← teleport Alice Bob q ;;

  (* Bob randomly picks his measurement basis. *)
  LET  coin @ Bob ← Bob [- Unitary H (New (Bit false)) -] ;;
  LET! b @ Bob    ← Bob [- Meas coin -] ;;

  (* Bob rotates into his chosen basis by applying H when b=1. *)
  LET q @ Bob    ← Bob [- If b (Unitary H q) q -] ;;

  (* Bob measures in his chosen basis.  A result of 1 means the round is
      conclusive: both Alice and Bob know they share the same key bit. *)
  LET! rb @ Bob   ← Bob [- Meas q -] ;;

  (* Bob announces the round result to Alice over the classical channel. *)
  LET! ra @ Alice ← send Bob (Expr.Bang rb) Alice ;;

  pair Alice Bob
       (Alice [- Pair (Bang ra) (Bang a) -])
       (Bob   [- Pair (Bang rb) (Bang (bneg b)) -]).


  (* Three rounds of B92 followed by local key packaging.
     Alice packages ((r1,a1),(r2,a2),(r3,a3)) where ri is Bob's announcement
     and ai is her prepared bit.  Bob packages ((m1,~b1),(m2,~b2),(m3,~b3))
     where mi is his measurement result and ~bi is his inferred key bit.
     In each conclusive round (ri=1) the key bits agree: ai = ~bi. *)
  Definition choreo  :=
    LET (ad1 @ "alice", bd1@ "bob") ← b92_round "alice" "bob" ;;
    LET (ad2 @ "alice", bd2@ "bob") ← b92_round "alice" "bob" ;;
    LET (ad3 @ "alice", bd3@ "bob") ← b92_round "alice" "bob" ;;
    pair "alice" "bob"
        ("alice" [- Pair (Pair ad1 ad2) ad3 -])
        ("bob" [- Pair (Pair bd1 bd2) bd3 -]).


  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo
              NetQASM
              choreo.

    Eval compute in apps.

End B92.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Definition example_apps := B92.apps.
Extraction "B92.ml" example_apps.
