From Stdlib Require Import  FSets.FMapList FSets.FSetList FSets.FMapFacts
                            OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Stdlib Require Import String.

From Stdlib Require Lists.List.
Export List.ListNotations.
Open Scope list_scope.

Declare Scope qoreo.

Module Var.

  Module Export V := OrderedTypeEx.UOT_to_OT (OrderedTypeEx.Nat_as_OT).
  Definition t := V.t.
  Definition eq_dec : forall (x y : t), {x=y} + {x <> y} := eq_nat_dec.
  
  Module Map := FSets.FMapList.Make(V).
  Module MapFacts := FMapFacts.Properties(Map).
  Module FSet := FSets.FSetList.Make(V).

  #[export] Existing Instance MapFacts.F.EqualSetoid.

  Definition domain {A} (m : Map.t A) : FSet.t :=
    let f := fun x _ s => FSet.add x s in
    Map.fold f m FSet.empty.

  Definition Singleton {A} x a (m : Map.t A) : Prop :=
    Map.Equal m (Map.add x a (Map.empty _)).

End Var.

Definition qref := nat.

Inductive unitary :=
| H | X | Y | Z | CNOT | SGATE | Sdag | TGATE | Tdag.


Module Config.
  Record t := {
    dim : nat;
    qstate : Matrix dim dim
  }.
  (* Definition add x (v : expr) (cfg : t) : t :=
  {|
    state := Var.Map.add x v (state cfg);
    dim := dim cfg;
    qstate := qstate cfg
  |}. *)
  (* Definition find x (cfg : t) : option expr :=
    Var.Map.find x (state cfg). *)


  (* Project onto the state where qubit q is in the classical state |b> *)
  (*Definition proj q dim (b : bool) := pad_u dim q (bool_to_matrix b).*)
  Definition measure (b : bool) (q : qref) (cfg : t) : t :=
    let rho' := super (pad_u q (dim cfg) (bool_to_matrix b)) (qstate cfg) in
    {|
      dim := dim cfg;
      qstate := rho'
    |}.
    
  Definition new (b : bool) (cfg : t) : qref * t :=
    let q := dim cfg in
    let rho' := kron (qstate cfg) (bool_to_ket b) in
    (q, {|
      dim := 1 + dim cfg;
      qstate := rho'
    |}).

  Definition apply_matrix (cfg : t) (U : Matrix (2 ^ dim cfg) (2 ^ dim cfg)) : t :=
  {|
    dim := dim cfg;
    qstate := super U (qstate cfg)
  |}.
  

  Definition epr (cfg : t) : qref * qref * t :=
    let q1 := dim cfg in
    let q2 := (1 + q1)%nat in
    let bell00 := Quantum.EPRpair † × Quantum.EPRpair in
    let rho' := kron (qstate cfg) bell00 in
    (q1, q2, {|
      dim := 2 + dim cfg;
      qstate := rho'
    |}).


  Definition gate_to_matrix (n : nat) (U : unitary) (qs : list qref) : Matrix (2^n) (2^n) :=
  match U, qs with
  | H, [q] => @pad 1 q n Quantum.hadamard
  | X, [q] => @pad 1 q n Quantum.σx
  | Y, [q] => @pad 1 q n Quantum.σy
  | Z, [q] => @pad 1 q n Quantum.σz
  | CNOT, [q1; q2] => pad_ctrl n q1 q2 Quantum.σx
  | SGATE, [q] => @pad 1 q n Quantum.Sgate
  | Sdag, [q]  => @pad 1 q n Quantum.Sgate†
  | TGATE, [q] => @pad 1 q n Quantum.Tgate
  | Tdag, [q]  => @pad 1 q n Quantum.Tgate†
  | _, _ => Zero
  end.
  Definition apply_gate (U : unitary) (qs : list qref) (cfg : t) : t :=
    apply_matrix cfg (gate_to_matrix _ U qs).

    
  Lemma test1 : gate_to_matrix 2 CNOT [0;1]%nat = cnot.
  Proof.
    assert (H : WF_Matrix (gate_to_matrix 2 CNOT [0%nat; 1%nat])).
    { simpl.
      set (H0 := QuantumLib.Pad.WF_pad_ctrl 2 0 1 σx).
      apply H0.
      auto with wf_db.
    }
    prep_matrix_equality.
    destruct x as [ | [ | [ | [ | x ]]]];
    destruct y as [ | [ | [ | [ | y ]]]];
      try (rewrite H; [ auto | right; simpl; lia]; fail);
      try (rewrite H; [ auto | left; simpl; lia]; fail);
      try lca.
  Qed.

  Lemma test2 :gate_to_matrix 1 H [0]%nat = hadamard.
  Proof.
    simpl. unfold pad. simpl. Msimpl; auto.
  Qed.

End Config.

(* This could be instantiated in different ways. *)

Module Actor.

  Module Export V := OrderedTypeEx.UOT_to_OT (OrderedTypeEx.String_as_OT).
  Definition t := V.t.
  Definition eq_dec : forall (x y : t), {x=y} + {x <> y} := string_dec.
  
  Module Map := FSets.FMapList.Make(V).
  Module MapFacts := FMapFacts.Properties(Map).
  Module FSet := FSets.FSetList.Make(V).

  #[export] Existing Instance MapFacts.F.EqualSetoid.

  Definition domain {A} (m : Map.t A) : FSet.t :=
    let f := fun x _ s => FSet.add x s in
    Map.fold f m FSet.empty.

  Definition Singleton {A} x a (m : Map.t A) : Prop :=
    Map.Equal m (Map.add x a (Map.empty _)).

End Actor.
