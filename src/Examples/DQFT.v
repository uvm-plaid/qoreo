
From Stdlib Require Import String List Arith ZArith QArith.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import Base.Config Expr.Expr Choreography.Choreography.
From Qoreo.Choreography Require Import Notation.
From Qoreo Require Import NetQasm.

Import ListNotations.
Import Config.Unitary.

Open Scope string_scope.
Open Scope example_scope.

Module DQFT.

  (* General DQFT algorithm as seen in: https://arxiv.org/pdf/2606.18494 *)

  (* Allocate all qubits belonging to a single actor. *)
  Fixpoint allocate_n (A : Actor.t) (bits : list bool)
      : Qoreo (list Var.t) :=
    match bits with
    | [] => ret []
    | b :: bits' =>
      do q ← A [- New (Bit b) -] ;;
      do qs ← allocate_n A bits' ;;
      ret (q :: qs)
    end.

  (* Generalized version of assigning qubits to each actor based on the inputs to the function.
     Every actor except the last receives num_qubits_per_actor qubits.
     The last actor receives all remaining qubits.

     Returns a list (Actor.t * list Var.t), mapping each actor
     with the qubits it owns.
  *)
  Fixpoint allocate (num_qubits_per_actor : nat)
      (actors : list Actor.t) (bits : list bool)
      : Qoreo (list (Actor.t * list Var.t)) :=
    match actors with
    | [] => ret []
    | [A] =>
      do qs ← allocate_n A bits ;;
      ret [(A, qs)] (*For the remaining r qubits, we assign them to the last actor*)
    | A :: actors' =>
      let abits := List.firstn num_qubits_per_actor bits in
      let bits' := List.skipn num_qubits_per_actor bits in
      do qs ← allocate_n A abits ;;
      do rest ← allocate num_qubits_per_actor actors' bits' ;;
      ret ((A, qs) :: rest)
    end.

  (* Extra gates needed for general QFT *)
  Definition angle (d : nat) : QArith_base.Q :=
    QArith_base.Qmake 1%Z
      (Pos.of_nat (Nat.pow 2 d)).

  (* Requires control and target to be owned by A.
     Returns (control', target') where both remain owned by A.
  *)
  Definition controlled_phase
      (A : Actor.t) (d : nat)
      (control target : Var.t)
      : Qoreo (Var.t * Var.t) :=
    match d with
    | S O =>
      A [-- Unitary CS (Pair control target) -]
    | S (S O) =>
      A [-- Unitary CT (Pair control target) -]
    | _ =>
      do control ←
        A [- Unitary (RZ (angle (S d))) control -] ;;
      do (control, target) ←
        A [-- Unitary (CRZ (angle d))
          (Pair control target) -] ;;
      ret (control, target)
    end.

  (* Apply several controlled phases with one control.
     The control and all targets must be owned by the same actor.
     Returns updated variables with their ownership preserved.
  *)
  Fixpoint controlled_targets
      (A : Actor.t) (d : nat)
      (control : Var.t) (targets : list Var.t)
      : Qoreo (Var.t * list Var.t) :=
    match targets with
    | [] => ret (control, [])
    | target :: rest =>
      do (control, target) ←
        controlled_phase A d control target ;;
      do (control, rest) ←
        controlled_targets A (S d) control rest ;;
      ret (control, target :: rest)
    end.

  (* Generalized correction algorithm as seen in the paper.
     Requires q to be owned by Alice and all targets to be owned by Bob.

     Returns (q', targets') where q' remains owned by Alice
     and every target in targets' remains owned by Bob.

     Uses one EPR pair for all remote controlled-phase gates in the packet.
  *)
  Definition remote_packet
      (Alice Bob : Actor.t) (d : nat)
      (q : Var.t) (targets : list Var.t)
      : Qoreo (Var.t * list Var.t) :=

    do (a0, a1) ← get_entangled_pair Alice Bob ;;

    (* Starting process *)
    do (q, a0) ←
      Alice [-- Unitary CNOT (Pair q a0) -] ;;
    do m0 ← Alice [- Meas a0 -] ;;
    do m0_bob ← send Alice m0 Bob ;;
    do a1 ← Bob [-
      Expr.If m0_bob (Unitary X a1) a1 -] ;;

    (* All targets share the same remote ancilla. 
    E.g: The ancilla a1 that Bob owns is responsible for all the operations 
    q0 would have done in the regular QFT case.
    It then calls controlled_targets to apply CP for all the qubits in Bob's list. *)
    do (a1, targets) ←
      controlled_targets Bob d a1 targets ;;

    (* Ending process *)
    do a1 ← Bob [- Unitary H a1 -] ;;
    do m1 ← Bob [- Meas a1 -] ;;
    do m1_alice ← send Bob m1 Alice ;;
    do q ← Alice [-
      Expr.If m1_alice (Unitary Z q) q -] ;;

    ret (q, targets).


  (* Recursively construct the QFT.
     Each actor owns a list of qubits in logical QFT order.

     For each control qubit q:
     - Apply a Hadamard gate on the actor A that owns q.
     - Apply all controlled-phase gates with the remaining target qubits.
     - Recursively repeat the process for the next control qubit.

     The local helper apply_targets processes the remaining actor groups:
     - If the targets are owned by A, execute their CP gates locally.
     - If the targets belong to another actor B, call remote_packet
       once to execute all their CP gates using one EPR pair.
     - d is just the general denominator power for the angle used in CP(Pi/2^d). 
       For e.g: For q0 on q2, d=2, We apply CP(Pi/4) .

     Returns updated qubits paired with their original owners.
     remaining_qubits provides one recursive step per control qubit.
  *)
  Fixpoint qft
      (remaining_qubits : list bool)
      (groups : list (Actor.t * list Var.t))
      {struct remaining_qubits}
      : Qoreo (list (Actor.t * Var.t)) :=

    match remaining_qubits with
    | [] => ret []
    | _ :: remaining_qubits' =>

      (*Actor has no qubits left to process. *)
      match List.filter
          (fun '(_, qs) =>
            match qs with
            | [] => false
            | _ => true
            end)
          groups with

      | (A, q :: qs) :: rest =>

        (* Apply the remaining CP gates for the current control qubit. *)
        let fix apply_targets
            (d : nat)
            (q : Var.t)
            (targets : list (Actor.t * list Var.t))
            {struct targets}
            : Qoreo (Var.t * list (Actor.t * list Var.t)) :=

          match targets with
          | [] => ret (q, [])

          | (B, ts) :: later =>
            match ts with
            | [] =>
              do (q, later) ←
                apply_targets d q later ;;
              ret (q, (B, []) :: later)

            | _ =>
              if String.eqb A B then

                (* Local controlled-phase gates *)
                do (q, ts) ←
                  controlled_targets A d q ts ;;

                do (q, later) ←
                  apply_targets (Nat.add d (List.length ts)) q later;;

                ret (q, (B, ts) :: later)

              else

                (* Remote_packet takes a list of ALL qubits owned by an actor and only creates 1 EPR. *)
                do (q, ts) ←
                  remote_packet A B d q ts ;;

                do (q, later) ←
                  apply_targets (Nat.add d (List.length ts)) q later;;
                ret (q, (B, ts) :: later)
            end
          end in

        do q ← A [- Unitary H q -] ;;

        do (q, targets) ←
          apply_targets 1%nat q ((A, qs) :: rest);;

        do later ←
          qft remaining_qubits' targets ;;

        ret ((A, q) :: later)

      | _ => ret []
      end
    end.

  (* Measure output qubits.
     Each pair (A, q) specifies the actor that owns and measures q.
     Returns the measurement variables in logical qubit order.
  *)
  Fixpoint measure_all (qs : list (Actor.t * Var.t))
      : Qoreo (list Var.t) :=
    match qs with
    | [] => ret []
    | (A, q) :: rest =>
      do bit ← A [- Meas q -] ;;
      do bits ← measure_all rest ;;
      ret (bit :: bits)
    end.


  Definition dqft
      (actors : list Actor.t)
      (st : list bool)
      : Qoreo (list Var.t) :=
    let num_qubits_per_actor :=
      Nat.div (List.length st) (List.length actors) in

    do groups ←
      allocate num_qubits_per_actor actors st ;;

    do qs ← qft st groups ;;

    measure_all qs.

  Definition parties : list Actor.t :=
    ["alice"; "bob"; "charlie"].

  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo NetSquid parties
      (dqft parties
        [true; false; true; false; true; false]).

End DQFT.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Definition example_apps := DQFT.apps.
Extraction "DQFT.ml" example_apps.
