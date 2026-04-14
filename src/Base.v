From Stdlib Require Import  FSets.FMapList FSets.FSetList FSets.FMapFacts
                            OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Stdlib Require Import String.

From Stdlib Require Lists.List.
Export List.ListNotations.
Open Scope list_scope.

Declare Scope qoreo.
Create HintDb var_db.

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

  Lemma eq_dec_refl : forall x,
    eq_dec x x = left (eq_refl x).
  Proof.
    intros.
    induction x; simpl; auto.
    rewrite IHx; auto.
  Qed.
  #[export] Hint Rewrite eq_dec_refl : var_db.

  Lemma remove_add_eq : forall A x (v : A) Gamma,
    Var.Map.Equal
      (Var.Map.remove x (Var.Map.add x v Gamma))
      (Var.Map.remove x Gamma).
  Proof.
    intros A x v Gamma y.
    destruct (eq_dec x y) as [Heq | Hneq].
    - subst. rewrite MapFacts.F.remove_eq_o; auto.
      rewrite MapFacts.F.remove_eq_o; auto.
    - rewrite MapFacts.F.remove_neq_o; auto.
      rewrite MapFacts.F.add_neq_o; auto.
      rewrite MapFacts.F.remove_neq_o; auto.
  Qed.
  #[export] Hint Rewrite remove_add_eq : var_db. 

  Lemma remove_add_neq : forall A x y (v : A) Gamma,
    x <> y ->
    Var.Map.Equal
      (Var.Map.remove x (Var.Map.add y v Gamma))
      (Var.Map.add y v (Var.Map.remove x Gamma)).
  Proof.
    intros A x y v Gamma Hneq z.
    destruct (eq_dec x z) as [Heq_xz | Hneq_xz].
    - subst. rewrite MapFacts.F.remove_eq_o; auto.
      rewrite MapFacts.F.add_neq_o; auto.
      rewrite MapFacts.F.remove_eq_o; auto.
    - rewrite MapFacts.F.remove_neq_o; auto.
      destruct (eq_dec y z) as [Heq_yz | Hneq_yz].
      + subst. rewrite MapFacts.F.add_eq_o; auto.
        rewrite MapFacts.F.add_eq_o; auto.
      + rewrite MapFacts.F.add_neq_o; auto.
        rewrite MapFacts.F.add_neq_o; auto.
        rewrite MapFacts.F.remove_neq_o; auto.
  Qed.
  #[export] Hint Rewrite remove_add_neq : var_db.

  Lemma remove_empty : forall A x,
    Map.Equal (Map.remove x (@Map.empty A))
      (@Map.empty A).
  Proof.
    intros A x y.
    destruct (eq_dec x y) as [Heq | Hneq].
    - subst. rewrite MapFacts.F.remove_eq_o; auto.
    - rewrite MapFacts.F.remove_neq_o; auto.
  Qed.
  #[export] Hint Rewrite remove_empty : var_db.
  
  Definition concat {A} (m1 m2 : Map.t A) : Map.t A :=
  Map.fold (fun k v acc => Map.add k v acc) m1 m2.

  Lemma concat_find : forall A (m1 m2 : Map.t A) k,
    Map.find k (concat m1 m2) =
    match Map.find k m1 with
    | Some v => Some v
    | None => Map.find k m2
    end.
  Proof.
    intros.
    unfold concat.
    apply MapFacts.fold_rec; intros.
    - replace (Map.find k m) with (@None A); auto.
      {
        symmetry. apply MapFacts.F.not_find_in_iff.
        intros [v Hin]. apply (H k v); auto.
      }
    - rewrite MapFacts.F.add_o.
      unfold MapFacts.Add in H1.
      rewrite H1.
      rewrite MapFacts.F.add_o.
      rewrite H2.
      destruct (Map.E.eq_dec k0 k); auto.
  Qed.

  Lemma partition_concat : forall A (m m1 m2 : Var.Map.t A),
    MapFacts.Partition m m1 m2 ->
    Map.Equal m (concat m1 m2).
  Proof.
    intros A m m1 m2 [Hdisj Hpart] x.
    rewrite concat_find.
    destruct (Map.find x m) eqn:Hfind.
    * (* x in dom m *)
      apply MapFacts.F.find_mapsto_iff in Hfind.
      apply Hpart in Hfind.
      destruct Hfind as [Hfind | Hfind].
      + (* x in dom m1 *)
        apply MapFacts.F.find_mapsto_iff in Hfind.
        rewrite Hfind; auto.
      + (* x in dom m2 *)
        replace (Map.find x m1) with (@None A).
        2:{
          symmetry.
          apply MapFacts.F.not_find_in_iff.
          intros Hcontra. apply (Hdisj x). split; auto.
          eexists; eauto.
        }
        symmetry.
        apply MapFacts.F.find_mapsto_iff; auto.
    * (* x ∉ m *) 
      assert (H : Map.find x m1 = None /\ Map.find x m2 = None).
      {
        apply MapFacts.F.not_find_in_iff in Hfind.
          repeat rewrite <- MapFacts.F.not_find_in_iff.
          split; intros [v Hcontra]; apply Hfind;
            exists v; apply Hpart; auto.
      }
      destruct H as [H1 H2].
      rewrite H1; rewrite H2.
      auto.
  Qed.
  

End Var.

Module QRef := Var.

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
  Definition measure (b : bool) (q : nat) (cfg : t) : t :=
    let rho' := super (pad_u q (dim cfg) (bool_to_matrix b)) (qstate cfg) in
    {|
      dim := dim cfg;
      qstate := rho'
    |}.
    
  Definition new (b : bool) (cfg : t) : nat * t :=
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
  

  Definition epr (cfg : t) : nat * nat * t :=
    let q1 := dim cfg in
    let q2 := (1 + q1)%nat in
    let bell00 := Quantum.EPRpair † × Quantum.EPRpair in
    let rho' := kron (qstate cfg) bell00 in
    (q1, q2, {|
      dim := 2 + dim cfg;
      qstate := rho'
    |}).


  Definition gate_to_matrix (n : nat) (U : unitary) (qs : list nat) : Matrix (2^n) (2^n) :=
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
  Definition apply_gate (U : unitary) (qs : list nat) (cfg : t) : t :=
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
