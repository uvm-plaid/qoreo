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

  Definition fresh {A} (m : Map.t A) :=
    let f := fun x _ z_fresh => if Nat.leb z_fresh x then (x+1)%nat else z_fresh in
    Map.fold f m 0%nat.

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


Inductive unitary :=
| H | X | Y | Z | CNOT | SGATE | Sdag | TGATE | Tdag.


Module Config.
  
  Record t := {
    dim : nat;
    qrefs : Var.Map.t nat;
    qstate : Matrix dim dim
  }.

  Module Refs.
    Definition Partition cfg cfg1 cfg2 :=
      Var.MapFacts.Partition (qrefs cfg) (qrefs cfg1) (qrefs cfg2).
    Definition Singleton x cfg :=
      Var.Map.In x (qrefs cfg) /\ Var.Map.cardinal (qrefs cfg) = 1%nat.
    Definition Empty cfg :=
      Var.Map.Empty (qrefs cfg).

  End Refs.

  Record WellScoped (cfg : t) := {
    wf_qstate : Matrix.WF_Matrix (qstate cfg);
    wf_qrefs : List.Forall
              (fun x => snd x < dim cfg)%nat
              (Var.Map.elements (qrefs cfg))
  }.

    Definition find (x : Var.t) (cfg : t) : nat :=
      match Var.Map.find x (qrefs cfg) with
      | Some q => q
      | None   => 0%nat
      end.


  (* Project onto the state where qubit q is in the classical state |b> *)
  (*Definition proj q dim (b : bool) := pad_u dim q (bool_to_matrix b).*)
  Definition measure (b : bool) (x : Var.t) (cfg : t) : t :=
    let q := find x cfg in
    let rho' := super (pad_u q (dim cfg) (bool_to_matrix b)) (qstate cfg) in
    {|
      dim := dim cfg;
      qrefs := Var.Map.remove x (qrefs cfg);
      qstate := rho'
    |}.

  Definition new (b : bool) (cfg : t) : Var.t * t :=
    let x := Var.fresh (qrefs cfg) in
    let q := dim cfg in
    let rho' := kron (qstate cfg) (bool_to_ket b) in
    (x, {|
      dim := 1 + dim cfg;
      qrefs := Var.Map.add x q (qrefs cfg);
      qstate := rho'
    |}).

  Definition apply_matrix (cfg : t) (U : Matrix (2 ^ dim cfg) (2 ^ dim cfg)) : t :=
  {|
    dim := dim cfg;
    qrefs := qrefs cfg;
    qstate := super U (qstate cfg)
  |}.
  

  Definition epr (cfg : t) : Var.t * Var.t * t :=
    let d := dim cfg in
    let refs := qrefs cfg in
    let x1 := Var.fresh refs in
    let refs' := Var.Map.add x1 d refs in
    let x2 := Var.fresh refs' in
    let refs'' := Var.Map.add x2 (d+1)%nat refs in

    let bell00 := Quantum.EPRpair † × Quantum.EPRpair in
    let rho' := kron (qstate cfg) bell00 in
    (x1, x2, {|
      dim := 2 + dim cfg;
      qrefs := refs'';
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

  Definition apply_gate (U : unitary) (xs : list Var.t) (cfg : t) : t :=
    let qs := List.map (fun x => find x cfg) xs in
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

  Lemma bool_dec_refl : forall (b : bool), bool_dec b b = left (eq_refl b).
  Proof. destruct b; auto. Qed.
  Lemma ascii_dec_refl : forall (a : Ascii.ascii), Ascii.ascii_dec a a = left (eq_refl a).
  Proof.
    destruct a. simpl.
    repeat rewrite bool_dec_refl.
    simpl.
    reflexivity.
  Qed.

  Module Export V := OrderedTypeEx.UOT_to_OT (OrderedTypeEx.String_as_OT).
  Definition t := V.t.
  Definition eq_dec : forall (x y : t), {x=y} + {x <> y} := string_dec.


  Lemma eq_dec_refl : forall A, eq_dec A A = left (eq_refl A).
  Proof.
    induction A; auto.
    simpl. rewrite IHA. simpl.
    rewrite ascii_dec_refl.
    reflexivity.
  Qed.
  
  Module Map := FSets.FMapList.Make(V).
  Module MapFacts := FMapFacts.Properties(Map).
  Module FSet := FSets.FSetList.Make(V).
  Module FSetFacts := FSetFacts.WFacts(FSet).

  #[export] Existing Instance MapFacts.F.EqualSetoid.

  Definition domain {A} (m : Map.t A) : FSet.t :=
    let f := fun x _ s => FSet.add x s in
    Map.fold f m FSet.empty.

  Definition Singleton {A} x a (m : Map.t A) : Prop :=
    Map.Equal m (Map.add x a (Map.empty _)).

End Actor.
Module Tactics.
  Create HintDb actor_db.

  #[export] Hint Rewrite Var.MapFacts.F.add_mapsto_iff : var_db.
  #[export] Hint Rewrite Var.MapFacts.F.empty_mapsto_iff Var.MapFacts.F.remove_in_iff Var.MapFacts.F.remove_mapsto_iff : var_db.

  #[export] Hint Rewrite Var.eq_dec_refl Var.remove_add_eq Var.remove_empty : var_db.


  #[export] Hint Rewrite Actor.FSetFacts.inter_iff : actor_db.
  #[export] Hint Rewrite Actor.FSetFacts.add_iff : actor_db.
  #[export] Hint Rewrite Actor.FSetFacts.singleton_iff : actor_db.

End Tactics.
