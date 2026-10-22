
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

  (* This function calculates how many qubits need to be assigned to each actor. We assume that all actors have equal network capabilities here.
  Note: This is not optimal and can be changed to reflect real-time network constraints. *)
  Definition owners (n : nat) (actors : list Actor.t)
      : list Actor.t :=
    let m := List.length actors in
    match m with
    | O => []
    | S _ =>
        let k := Nat.div n m in
        let r := Nat.modulo n m in
        let small := Nat.sub m r in

        List.app
          (List.flat_map
            (fun A => List.repeat A k)
            (List.firstn small actors))
          (List.flat_map
            (fun A => List.repeat A (S k))
            (List.skipn small actors))
    end.

  (* Generalized version of assigning qubits to each actor based on the inputs to the function *)
  Fixpoint allocate (actors : list Actor.t) (bits : list bool)
      : Qoreo (list Var.t) :=
    match actors, bits with
    | A :: actors', b :: bits' =>
      do q ← A [- New (Bit b) -] ;;
      do qs ← allocate actors' bits' ;;
      ret (q :: qs)
    | _, _ => ret []
    end.

  (* owner_of replaces A [- New(Bit b) -] with the name of the Actor defined in owners *)
  Definition owner_of (q : Var.t) : Qoreo Actor.t :=
    fun s =>
      (s, match Var.Map.find q (Notation.vars s) with
          | Some A => A
          | None => ""
          end).

  (* Extra gates needed for general QFT *)
  Definition angle (d : nat) : QArith_base.Q :=
    QArith_base.Qmake 1%Z
      (Pos.of_nat (Nat.pow 2 d)).

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

  (* Apply several controlled phases with one control. *)
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

  (* Generalized correction algorithm as seen in the paper *)
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

    (* All targets share the same remote ancilla. *)
    do (a1, targets) ←
      controlled_targets Bob d a1 targets ;;

    (* Ending process *)
    do a1 ← Bob [- Unitary H a1 -] ;;
    do m1 ← Bob [- Meas a1 -] ;;
    do m1_alice ← send Bob m1 Alice ;;
    do q ← Alice [-
      Expr.If m1_alice (Unitary Z q) q -] ;;

    ret (q, targets).

  (* Generalized QFT distribution. If Alice is executing a CP with a qubit that she owns,
  No additional EPR requirement. If Alice executes a CP with Bob, we generate 1 EPR. The paper outlines that we only
  to generate 1 ancilla. 
  Recursively run this for Bob-Charlie operations and subsequently every other pair of actors. *)
  Fixpoint run_targets
      (fuel : nat)
      (Alice : Actor.t)
      (d : nat)
      (q : Var.t)
      (targets : list Var.t)
      : Qoreo (Var.t * list Var.t) :=

    match fuel, targets with
    | O, _ => ret (q, targets)
    | S _, [] => ret (q, [])
    | S fuel', target :: rest =>

      do Bob ← owner_of target ;;

      if String.eqb Alice Bob then

        (* Local controlled-phase gate *)
        do (q, target) ←
          controlled_phase Alice d q target ;;

        do (q, rest) ←
          run_targets fuel' Alice (S d) q rest ;;

        ret (q, target :: rest)

      else

        (* Find the remaining targets on Bob. *)
        do (same, later) ←
          (fun s =>
            (s, List.partition
              (fun x =>
                match Var.Map.find x (Notation.vars s) with
                | Some A => String.eqb A Bob
                | None => false
                end)
              rest)) ;;

        (* One EPR pair for all Bob's targets. *)
        do (q, packed) ←
          remote_packet Alice Bob d q (target :: same) ;;

        (* Continue with subsequent actors. *)
        do (q, later) ←
          run_targets fuel' Alice
            (d + List.length packed) q later ;;

        ret (q, List.app packed later)
    end.

  (* Recursively construct the QFT. *)
  Fixpoint qft (fuel : nat) (qs : list Var.t)
      : Qoreo (list Var.t) :=
    match fuel, qs with
    | O, _ => ret qs
    | S _, [] => ret []
    | S fuel', q :: rest =>

      do A ← owner_of q ;;
      do q ← A [- Unitary H q -] ;;

      do (q, rest) ←
        run_targets (List.length rest) A 1 q rest ;;

      do rest ← qft fuel' rest ;;
      ret (q :: rest)
    end.

  (* Measure output qubits. *)
  Fixpoint measure_all (qs : list Var.t)
      : Qoreo (list Var.t) :=
    match qs with
    | [] => ret []
    | q :: rest =>
      do A ← owner_of q ;;
      do bit ← A [- Meas q -] ;;
      do bits ← measure_all rest ;;
      ret (bit :: bits)
    end.

  Definition dqft
      (n : nat)
      (actors : list Actor.t)
      (st : list bool)
      : Qoreo (list Var.t) :=
    do qs ← allocate (owners n actors) st ;;
    do qs ← qft n qs ;;
    measure_all qs.

  Definition parties : list Actor.t :=
    ["alice"; "bob"].

  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo NetSquid parties
      (dqft 6 parties
        [true; false; true; false; true; false]).

End DQFT.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Definition example_apps := DQFT.apps.
Extraction "DQFT.ml" example_apps.
