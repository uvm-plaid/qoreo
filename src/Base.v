From Stdlib Require FSets.FMapList FSets.FSetList 
                            FSets.FMapFacts
                            FSets.FMapInterface
                            OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Stdlib Require Import String Morphisms (* for Proper *).

From Stdlib Require Lists.List.
Export List.ListNotations.
Open Scope list_scope.

Declare Scope qoreo.
Create HintDb var_db.

(** Generic map theory: extends FMapFacts.Properties with definitions and
    theorems about [Singleton], [concat], and associated tactics. The module
    is parameterized over an arbitrary [FMapInterface.S] so it can be
    instantiated for any key type. *)
Module FMap_fun (E : OrderedType.OrderedType) (M : FMapInterface.Sfun E) (FSet : FSetInterface.Sfun E).
  Import M.
  (* type t = M.t, type key = M.key = V0.t *)
  Module Export Properties := FMapFacts.WProperties_fun E M. (* Includes module F *)
  Module FSetProperties := FSetFacts.WFacts_fun E FSet.

  Definition Singleton {A} (x : key) (a : A) (m : M.t A) : Prop :=
    M.Equal m (M.add x a (M.empty _)).

  Definition concat {A} (m1 m2 : t A) : t A :=
    M.fold (fun k v acc => M.add k v acc) m1 m2.

  Definition domain {A} (m : M.t A) : FSet.t :=
      let f := fun x _ s => FSet.add x s in
      M.fold f m FSet.empty.
  Definition Partition {A} := @Properties.Partition A.

  (* Rewrite/auto databases *)
  #[global] Existing Instance F.EqualSetoid.
  #[global] Hint Rewrite F.add_mapsto_iff : var_db.
  #[global] Hint Rewrite F.empty_mapsto_iff : var_db.
  #[global] Hint Rewrite F.add_in_iff : var_db.
  #[global] Hint Rewrite F.map_o : var_db.
  #[global] Hint Rewrite F.remove_o : var_db.
  #[global] Hint Rewrite F.add_o : var_db.
  #[global] Hint Rewrite F.empty_o : var_db.
  #[global] Hint Rewrite F.map_in_iff : var_db.
  #[global] Hint Resolve M.empty_1 : var_db.
  #[global] Hint Resolve Properties.Partition_sym : var_db.

  Module Proofs.

  #[global] Instance singletonProper : forall A,
    Proper (E.eq ==> @eq A ==> @M.Equal A ==> iff) (@Singleton A).
  Proof.
    intros A x1 x2 Heq a1 a2 Ha m1 m2 Hm. subst.
    unfold Singleton.
    rewrite Heq. rewrite Hm. reflexivity.
  Qed.

  (** Concatenation *)

  Lemma concat_find : forall A (m1 m2 : M.t A) k,
    M.find k (concat m1 m2) =
    match M.find k m1 with
    | Some v => Some v
    | None => M.find k m2
    end.
  Proof.
    intros.
    unfold concat.
    apply fold_rec; intros.
    - replace (M.find k m) with (@None A); auto.
      {
        symmetry. apply F.not_find_in_iff.
        intros [v Hin]. apply (H k v); auto.
      }
    - rewrite F.add_o.
      unfold Add in H1.
      rewrite H1.
      rewrite F.add_o.
      rewrite H2.
      destruct (E.eq_dec k0 k); auto.
  Qed.
  #[global] Hint Rewrite concat_find : var_db.

  #[global] Instance concatProper : forall A,
    Proper (@M.Equal A ==> @M.Equal A ==> @M.Equal A) (@concat A).
  Proof.
    intros A m1 m2 Hm n1 n2 Hn.
    intros z.
    repeat rewrite concat_find.
    rewrite Hm.
    destruct (M.find z m2); auto.
  Qed.

  Lemma concat_in : forall A x (m1 m2 : M.t A),
    M.In x (concat m1 m2) <-> M.In x m1 \/ M.In x m2.
  Proof.
    intros A x m1 m2.
    repeat rewrite F.in_find_iff.
    rewrite concat_find.
    destruct (M.find x m1); auto.
    * split; [intros | intros [? | ?]]; auto.
      inversion 1.
    * split; [intros | intros [? | ?]]; auto.
  Qed.
  #[global] Hint Rewrite concat_in : var_db.

  Lemma map_concat : forall {A B} (f : A -> B) m1 m2,
    M.Equal (M.map f (concat m1 m2))
            (concat (M.map f m1) (M.map f m2)).
  Proof.
      intros.
      intros z.
      autorewrite with var_db.
      destruct (M.find z m1); auto.
  Qed.
  #[global] Hint Rewrite @map_concat : var_db.

  Lemma concat_assoc : forall {A} (m1 m2 m3 : M.t A),
    M.Equal (concat m1 (concat m2 m3)) (concat (concat m1 m2) m3).
  Proof.
      intros.
      intros z.
      autorewrite with var_db.
      destruct (M.find z m1); auto.
  Qed.

  Lemma domain_add_iff : forall A x z (a : A) m0 m,
    Add x a m0 m ->
    FSet.In z (domain m) <-> (x = z) \/ FSet.In z (domain m0).
  Admitted.

  Lemma domain_remove : forall A x m,
    FSet.Equal (domain (remove x m)) (FSet.remove x (@domain A m)).
  Admitted.

  (** Domain *)
  #[global] Existing Instance FSetProperties.Equal_ST.
  #[global] Instance domainProper : forall A,
    Proper (@M.Equal A ==> @FSet.Equal) (@domain A).
  Proof.
    intros A m1 m2 Heq.
    unfold domain.
    apply fold_Equal; auto.
    * apply FSetProperties.Equal_ST.
    * intros x1 x2 Hx a1 a2 Ha X1 X2 HX; subst.
      rewrite Hx. rewrite HX. reflexivity.
    * intros x1 x2 ? ? ? Hneq z.
      repeat rewrite FSetProperties.add_iff.
      tauto.
  Qed.
      


  (** Lemma about FSets *)

  Lemma fset_in_union : forall x X1 X2,
    FSet.In x (FSet.union X1 X2)
    <->
    FSet.In x X1 \/ FSet.In x X2.
  Proof.
    intros x X1 X2. split.
    - apply FSet.union_1.
    - intros [H | H].
      + apply FSet.union_2; exact H.
      + apply FSet.union_3; exact H.
  Qed.
  #[global] Hint Rewrite fset_in_union : var_db.

  (** General properties of maps *)

  Lemma remove_not_in : forall A x (m : M.t A),
    ~ M.In x m ->
    M.Equal
      (M.remove x m)
      m.
  Proof.
    intros ? ? ? Hin.
    intros z.
    autorewrite with var_db.
    destruct (F.eq_dec x z) as [Heq | ?]; auto.
    {
      subst.
      rewrite <- Heq.
      apply F.not_find_in_iff in Hin.
      auto.
    }
  Qed.

  Lemma remove_map : forall A B x (f : A -> B) m,
    M.Equal
      (M.remove x (M.map f m))
      (M.map f (M.remove x m)).
  Proof.
    intros A B x f m z;
      autorewrite with var_db.
    destruct (E.eq_dec x z) as [Heq | Hneq];
      subst; simpl; auto.
  Qed.
  #[global] Hint Rewrite remove_map : var_db.

  Ltac compare x y :=
    let Heq := fresh "Heq" in
    destruct (E.eq_dec x y) as [Heq | Heq];
      try (rewrite <- Heq in *; clear Heq);
      try contradiction;
      try match goal with
      | [ H : ~ E.eq ?x ?x |- _ ] => contradict H; reflexivity
      end.

  Ltac reduce_eq_dec :=
    match goal with
    | [ |- context[E.eq_dec ?x ?y] ] => compare x y
    | [ H : context[E.eq_dec ?x ?y] |- _ ] => compare x y
    end.

  Lemma remove_add : forall A x y (v : A) Gamma,
    M.Equal
      (M.remove x (M.add y v Gamma))
      (if E.eq_dec x y then M.remove x Gamma else M.add y v (M.remove x Gamma)).
  Proof.
    intros.
    intros z.
    autorewrite with var_db.
    repeat (reduce_eq_dec; autorewrite with var_db; auto).
  Qed.
  #[global] Hint Rewrite remove_add : var_db.

  Lemma remove_empty : forall A x,
    M.Equal (M.remove x (@M.empty A))
      (@M.empty A).
  Proof.
    intros A x y.
    autorewrite with var_db.
    reduce_eq_dec; auto.
  Qed.
  #[global] Hint Rewrite remove_empty : var_db.

  Lemma map_add : forall {A B} (f : A -> B) x a m,
    M.Equal (M.map f (M.add x a m))
            (M.add x (f a) (M.map f m)).
  Proof.
    intros.
    intros z. autorewrite with var_db.
    compare x z; auto.
  Qed.
  #[global] Hint Rewrite @map_add : var_db.

  (** Empty maps *)

  Lemma empty_map_equal : forall {A} (m : M.t A),
    M.Empty m -> M.Equal m (M.empty A).
  Proof.
    intros A m Hempty k.
    autorewrite with var_db.
    destruct (M.find k m) eqn:Hfind; auto.
    apply M.find_2 in Hfind. exfalso. eapply Hempty; eauto.
  Qed.
  #[global] Hint Resolve @empty_map_equal : var_db.

  Lemma empty_map_Empty : forall {A B} (f : A -> B) m,
    M.Empty (M.map f m) <->
    M.Empty m.
  Proof.
    intros A B f m. 
    split.
    - intros Hempty k v Hmaps.
      apply (Hempty k (f v)).
      apply M.map_1; exact Hmaps.
    - intros Hempty k v Hmaps.
      apply F.map_mapsto_iff in Hmaps.
      destruct Hmaps as [a [_ Ha]].
      exact (Hempty k a Ha).
  Qed.

  Lemma empty_map_empty : forall {A B} (f : A -> B),
    M.Equal (M.map f (M.empty A)) (M.empty B).
  Proof.
    intros A B f k.
    autorewrite with var_db.
    reflexivity.
  Qed.
  #[global] Hint Rewrite @empty_map_empty : var_db.

  Lemma singleton_singleton : forall A x (a : A),
    Singleton x a (M.add x a (M.empty _)).
  Proof.
    intros A x a.
    intros z.
    reflexivity.
  Qed.

  Lemma singleton_remove : forall {A} (a : A) x m,
    Singleton x a m ->
    M.Empty (M.remove x m).
  Proof.
    intros A a x m H.
    unfold Singleton in H.
    rewrite H.
    autorewrite with var_db.
    compare x x.
    autorewrite with var_db.
    apply M.empty_1.
  Qed.
  #[global] Hint Resolve @singleton_remove : var_db.

  Ltac subst_eq_hypothesis_fwd m :=
    repeat match goal with
    | [ Heq : M.Equal m _, H : context[m] |- _ ] =>
      setoid_rewrite Heq in H
    | [ Heq : M.Equal m _ |- context[m] ] =>
      setoid_rewrite Heq
    end;
    (* if there are no more occurrences of m, clear Heq *)
    try match goal with
    | [ Heq : M.Equal m _ |- _ ] => clear m Heq
    end.

  Ltac subst_eq_hypothesis_bwd m :=
    repeat match goal with
    | [ Heq : M.Equal _ m, H : context[m] |- _ ] =>
      setoid_rewrite <- Heq in H
    | [ Heq : M.Equal _ m |- context[m] ] =>
      setoid_rewrite <- Heq
    end.
    (* if there are no more occurrences of m, clear Heq *)
    (*
    try match goal with
    | [ Heq : M.Equal _ m |- _ ] => clear m Heq
    end.
    *)

  Ltac subst_map :=
    repeat match goal with
    | [ Heq : M.Equal ?m ?m |- _ ] => clear Heq; try clear m
    | [ m : M.t _ |- _ ] =>
      match goal with
      | [ Heq : M.Equal m _ |- _ ] =>
        subst_eq_hypothesis_fwd m;
        try clear m Heq
      | [ Heq : M.Equal _ m |- _ ] =>
        subst_eq_hypothesis_bwd m;
        try clear m Heq
      end
    end.

  Ltac simpl_Empty :=
      match goal with
      | [ H : M.Empty (M.map _ _) |- _ ] =>
        apply empty_map_Empty in H
      | [ |- M.Empty (M.map _ _) ] =>
        apply empty_map_Empty

      (* Replace any instances of Empty m with m == empty
      and substitute *)
      | [ H : M.Empty ?m |- _ ] =>
        apply empty_map_equal in H;
        subst_map
      end.

  (** Lemmas about disjointness *)

  Lemma concat_disjoint : forall {A} (m1 m2 m3 : M.t A),
    Disjoint m1 (concat m2 m3) <->
    Disjoint m1 m2 /\ Disjoint m1 m3.
  Proof.
    intros A m1 m2 m3.
    unfold Disjoint.
    repeat split; intros.
    * specialize (H k); autorewrite with var_db in H.
      firstorder.
    * specialize (H k); autorewrite with var_db in H.
      firstorder.
    * autorewrite with var_db.
      firstorder.
  Qed.
  #[global] Hint Rewrite @concat_disjoint : var_db.

  Lemma disjoint_sym : forall {A} (m1 m2 : M.t A),
    Disjoint m1 m2 ->
    Disjoint m2 m1.
  Proof.
    intros ? ? ? H.
    unfold Disjoint.
    intros k; specialize (H k). firstorder.
  Qed.

  Lemma disjoint_map : forall {A B} (f : A -> B) m1 m2,
    Disjoint (M.map f m1) (M.map f m2)
    <-> Disjoint m1 m2.
  Proof.
    intros A B f m1 m2.
    unfold Disjoint.
    split; intros H k [Hin1 Hin2].
    - apply (H k). split.
      + apply F.map_in_iff; exact Hin1.
      + apply F.map_in_iff; exact Hin2.
    - apply F.map_in_iff in Hin1.
      apply F.map_in_iff in Hin2.
      exact (H k (conj Hin1 Hin2)).
  Qed.

  Lemma disjoint_empty_1 : forall A m,
    Disjoint (M.empty A) m.
  Proof.
    intros. intros z.
    rewrite F.empty_in_iff.
    intros [? ?]; contradiction.
  Qed.

  Lemma disjoint_empty_2 : forall A m,
    Disjoint m (M.empty A).
  Proof.
    intros. intros z.
    rewrite F.empty_in_iff.
    intros [? ?]; contradiction.
  Qed.
  #[global] Hint Resolve disjoint_empty_1 disjoint_empty_2 : var_db.

  Lemma disjoint_remove_1 : forall {A} (m1 m2 : M.t A) x,
    Disjoint m1 m2 ->
    Disjoint (M.remove x m1) m2.
  Admitted.

  Lemma disjoint_remove_2 : forall {A} (m1 m2 : M.t A) x,
    Disjoint m1 m2 ->
    Disjoint m1 (M.remove x m2).
  Proof.
    intros.
    apply disjoint_sym. apply disjoint_remove_1.
    apply disjoint_sym. auto.
  Qed.

  Ltac reduce_disjoint :=
  repeat match goal with
        | [ H : Disjoint ?m1 ?m2 |- Disjoint ?m2 ?m1 ] =>
          apply disjoint_sym; exact H

        | [ |- Disjoint (M.map _ _) (M.map _ _)] =>
          apply disjoint_map
        | [ H : Disjoint (M.map _ _) (M.map _ _) |- _] =>
          apply disjoint_map in H

        | [ |- Disjoint _ (concat _ _)] =>
          apply concat_disjoint; split
        | [ |- Disjoint _ (concat _ _)] =>
          apply disjoint_sym; apply concat_disjoint; split; apply disjoint_sym
        | [ H : Disjoint _ (concat _ _) |- _ ] =>
          apply concat_disjoint in H;
          destruct H
        | [ H : Disjoint (concat _ _) _ |- _ ] =>
          apply disjoint_sym in H;
          apply concat_disjoint in H;
          let H1 := fresh "Hdisj" in
          let H2 := fresh "Hdisj" in
          destruct H as [H1 H2];
          apply disjoint_sym in H1;
          apply disjoint_sym in H2

        | [ |- Disjoint (M.empty _) _ ] =>
          apply disjoint_empty_1
        | [ |- Disjoint _ (M.empty _) ] =>
          apply disjoint_empty_2
  end.

  (** Reflection between partition and concat *)

  Lemma partition_concat : forall {A} (m m1 m2 : M.t A),
    Partition m m1 m2 <->
    Disjoint m1 m2 /\ M.Equal m (concat m1 m2).
  Proof.
    intros A m m1 m2.
    split; [intros [Hdisj Hpart] | intros [Hdisjoint Heq]].
    * split; auto.
      intros k.
      rewrite concat_find.
      destruct (M.find k m1) as [ a |] eqn:Hfind1.
      { specialize (Hpart k a);
        repeat rewrite F.find_mapsto_iff in Hpart.
        apply Hpart; auto.
      }
      destruct (M.find k m2) as [a | ] eqn:Hfind2.
      {
        specialize (Hpart k a);
        repeat rewrite F.find_mapsto_iff in Hpart.
        apply Hpart; auto.
      }
      destruct (M.find k m) as [a | ] eqn:Hfind; auto.
      { (* contradiction *)
        contradict Hfind.
        specialize (Hpart k a);
        repeat rewrite F.find_mapsto_iff in Hpart.
        rewrite Hpart, Hfind1, Hfind2.
        inversion 1; discriminate.
      }
    * split; auto.
      intros k a.
      rewrite Heq.
      repeat rewrite F.find_mapsto_iff.
      rewrite concat_find.
      destruct (M.find k m1) eqn:Hfind1.
      {
        destruct (M.find k m2) eqn:Hfind2; auto;
          try (firstorder; fail).
        { unfold Disjoint in Hdisjoint.
          exfalso; apply (Hdisjoint k).
          repeat rewrite F.in_find_iff.
          rewrite Hfind1, Hfind2.
          split; inversion 1.
        }
        firstorder. discriminate.
      }
      destruct (M.find k m2) eqn:Hfind2; auto.
      {
        firstorder; try discriminate.
      }
      firstorder.
  Qed.

  Lemma concat_sym : forall {A} (m1 m2 : M.t A),
    Disjoint m1 m2 ->
    M.Equal (concat m1 m2) (concat m2 m1).
  Proof.
    intros A m1 m2 Hdisj z.
    autorewrite with var_db.
    destruct (M.find z m1) eqn:Hfind1; destruct (M.find z m2) eqn:Hfind2; auto.
    exfalso. apply (Hdisj z). split.
    - apply F.in_find_iff. rewrite Hfind1; discriminate.
    - apply F.in_find_iff. rewrite Hfind2; discriminate.
  Qed.

  Ltac reflect_partition :=
    repeat match goal with
          | [ H : Partition ?m ?m1 ?m2 |- _ ] =>
            apply partition_concat in H;
            let Hdisj := fresh "Hdisj" in
            let Heq := fresh "Heq" in
            destruct H as [Hdisj Heq];
            subst_map
          | [ |- Partition ?m ?m1 ?m2 ] =>
            apply partition_concat; split
          | [ H : context[M.map _ (concat _ _)] |- _] =>
            rewrite map_concat in H
          | [ |- context[M.map _ (concat _ _)] ] =>
            rewrite map_concat
    end.

  (** Lemmas about Partition *)

  (*** If Δ(x0)=τ0 and Δ==Δ1,Δ2 and x ∉ Δ2 then Δ1(x0)=τ0 *)
  Lemma partition_not_in_r : forall {A} Δ Δ2 Δ1 x (τ : A),
    M.MapsTo x τ Δ ->
    Partition Δ Δ1 Δ2 ->
    ~ (M.In x Δ2) ->
    M.MapsTo x τ Δ1.
  Proof.
    intros ? ? ? ? x τ Hx [Hdisjoint Hmapsto] Hnotin.
    apply Hmapsto in Hx.
    destruct Hx; auto.
    * contradict Hnotin.
      exists τ; auto.
  Qed.

  Lemma partition_empty_l : forall A m,
    Partition m (M.empty A) m.
  Proof.
    intros.
    reflect_partition.
    * reduce_disjoint.
    * intros z. autorewrite with var_db; auto.
  Qed.
  #[global] Hint Resolve partition_empty_l : var_db.

  Lemma partition_empty_r : forall A m,
    Partition m m (M.empty A).
  Proof.
    intros.
    reflect_partition.
    * reduce_disjoint.
    * intros z. autorewrite with var_db; auto.
      destruct (M.find z m); auto.
  Qed.
  #[global] Hint Resolve partition_empty_r : var_db.

  Lemma partition_add_l : forall A x (a:A) m m1 m2,
    Partition m m1 m2 ->
    ~ M.In x m2 ->
    Partition (M.add x a m) (M.add x a m1) m2.
  Proof.
    intros.
    reflect_partition.
    * unfold Disjoint in *.
      intros k [Hin1 Hin2].
      autorewrite with var_db in Hin1.
      apply (Hdisj k). split; auto.
      destruct Hin1 as [Heq | ?]; auto.
      rewrite Heq in *; clear Heq.
      contradiction.
    * intros z. autorewrite with var_db.
      reduce_eq_dec; auto.
  Qed.

  Lemma partition_add_r : forall A x (a:A) m m1 m2,
    Partition m m1 m2 ->
    ~ M.In x m1 ->
    Partition (M.add x a m) m1 (M.add x a m2).
  Proof.
    intros.
    apply Partition_sym.
    apply partition_add_l; auto.
    apply Partition_sym; auto.
  Qed.

  Lemma partition_remove : forall {A} x0 (Δ Δ1 Δ2 : M.t A),
    Partition Δ Δ1 Δ2 ->
    Partition (M.remove x0 Δ) (M.remove x0 Δ1) (M.remove x0 Δ2).
  Proof.
    intros A x0 Δ Δ1 Δ2 Hpart.
    reflect_partition.
    - (* Disjoint (remove x0 Δ1) (remove x0 Δ2) *)
      apply disjoint_remove_1.
      apply disjoint_remove_2.
      auto.
    -
      intros k.
      autorewrite with var_db in *.
      reduce_eq_dec; auto.
  Qed.

  Lemma partition_empty_inv1 : forall {A} (Δ1 Δ2 : M.t A),
    Partition (M.empty _) Δ1 Δ2 ->
    M.Equal Δ1 (M.empty _).
  Admitted.

  Lemma partition_empty_inv2 : forall {A} (Δ1 Δ2 : M.t A),
    Partition (M.empty _) Δ1 Δ2 ->
    M.Equal Δ2 (M.empty _).
  Admitted.

  Lemma partition_map_iff : forall A B (f : A -> B) m m1 m2,
    Partition m m1 m2 <->
    Partition (M.map f m) (M.map f m1) (M.map f m2).
  Admitted.

  Lemma partition_map_inv : forall A B (f : A -> B) m n1 n2,
    Partition (M.map f m) n1 n2 ->
    exists m1 m2,
      M.Equal n1 (M.map f m1)
      /\
      M.Equal n2 (M.map f m2)
      /\
      Partition m m1 m2.
  Admitted.

  Lemma partition_empty1_eq : forall A m m0,
      Partition m (M.empty A) m0 ->
      M.Equal m m0.
  Admitted.

  Lemma partition_empty2_eq : forall A m m0,
      Partition m m0 (M.empty A) ->
      M.Equal m m0.
  Admitted.

  Ltac reduce_partition :=
    match goal with

      (* Partitions with the empty map *)
      | [ H : Partition (M.empty _) ?D1 ?D2 |- _ ] =>
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        assert (H1 : M.Equal D1 (M.empty _))
          by (exact (partition_empty_inv1 D1 D2 H));
        assert (H2 : M.Equal D2 (M.empty _))
          by (exact (partition_empty_inv2 D1 D2 H));
        subst_map;
        try clear H

      | [ H : Partition ?m (M.empty _) ?m0 |- _ ] =>
        apply partition_empty1_eq in H;
        subst_map
      | [ H : Partition ?m ?m0 (M.empty _) |- _ ] =>
        apply partition_empty2_eq in H;
        subst_map

      (* Partitions with remove *)
      | [ |- Partition (M.remove ?x _) (M.remove ?x _) (M.remove ?x _) ] =>
        apply partition_remove

      (* Partitions with map *)
      | [ |- Partition (M.map ?f _) (M.map ?f _) (M.map ?f _) ] =>
        apply partition_map_iff
      | [ H : Partition (M.map ?f _) (M.map ?f _) (M.map ?f _) |- _ ] =>
        apply partition_map_iff in H

      | [H : Partition (M.map ?f ?m) ?n1 ?n2 |- _] =>
        let m1 := fresh "m1" in
        let m2 := fresh "m2" in
        let Heq1 := fresh "Heq1" in
        let Heq2 := fresh "Heq2" in
        destruct (partition_map_inv _ _ _ _ _ _ H)
          as [m1 [m2 [Heq1 [Heq2 Hpart]]]]; auto;
        subst_map; try rewrite Heq1, Heq2 in *; try clear n1 Heq1 n2 Heq2
    end.

  Ltac vsimpl :=
  repeat match goal with
  | [ |- M.Empty _ ] => simpl_Empty
  | [ H : M.Empty _ |- _ ] => simpl_Empty

  | [ |- Disjoint _ _ ] => reduce_disjoint
  | [ H : Disjoint _ _ |- _ ] => reduce_disjoint

  | [ |- context[Partition _ _ _ ]] =>
    reduce_partition
  | [ H : context[Partition _ _ _ ] |- _ ] =>
    reduce_partition

  | [ H : M.Equal _ _ |- _ ] => subst_map
  end.
  End Proofs.


  Module Tactics.
  (**
    Provides:
      * compare x y       - destructs Map.E.eq_dec x y and substitutes
      * reduce_eq_dec     - applies compare to goals/hypotheses containing Map.E.eq_dec
      * subst_map         - eliminates hypotheses of the form Map.Equal m1 m2 by rewriting
      * reflect_partition - converts Partition hypotheses into Disjoint + Map.Equal (concat) form
      * vsimpl            - simplifies hypotheses and goals that use maps

    vsimpl builds on the following tactics in MapFacts:
      * simpl_Empty       - simplifies Map.Empty goals/hypotheses and substitutes
      * reduce_disjoint   - simplifies Disjoint goals/hypotheses using symmetry and concat lemmas
      * reduce_partition  - simplifies Partition hypotheses

    In addition, there are rewrite and auto databases for simplifying goals:
      * autorewrite with var_db [in H]
      * auto/eauto with var_db
  *)
    Ltac compare x y := Proofs.compare x y.
    Ltac reduce_eq_dec := Proofs.reduce_eq_dec.
    Ltac subst_map := Proofs.subst_map.
    Ltac reflect_partition := Proofs.reflect_partition.
    Ltac vsimpl := Proofs.vsimpl.
  End Tactics.

End FMap_fun.

Module FMap (E0 : OrderedType.OrderedType) <: FMapInterface.S.
  Module M := FSets.FMapList.Make E0.
  Include M.
    
  Module S := FSets.FSetList.Make E.

  Module MProofs := FMap_fun E M S.
  Include MProofs.
End FMap.

Module Var.

  Module V := OrderedTypeEx.UOT_to_OT (OrderedTypeEx.Nat_as_OT).
  Include V.
  Module Map := FMap V.
  Module FSet := Map.S.

  Definition fresh {A} (m : Map.t A) :=
    let f := fun x _ z_fresh => if Nat.leb z_fresh x then (x+1)%nat else z_fresh in
    Map.fold f m 0%nat.


  (** General properties of Var-specific eq_dec (nat equality) *)

  (*
  Lemma eq_dec_refl : forall x,
    eq_dec x x = left (eq_refl x).
  Proof.
    intros.
    induction x; simpl; auto.
    rewrite IHx; auto.
  Qed.
  #[global] Hint Rewrite eq_dec_refl : var_db.
*)


End Var.
(*
#[global] Hint Rewrite MapFacts.F.add_mapsto_iff : var_db.
#[global] Hint Rewrite MapFacts.F.empty_mapsto_iff : var_db.
#[global] Hint Rewrite MapFacts.F.add_in_iff : var_db.
#[global] Hint Rewrite MapFacts.F.map_o : var_db.
#[global] Hint Rewrite MapFacts.F.remove_o : var_db.
#[global] Hint Rewrite MapFacts.F.add_o : var_db.
#[global] Hint Rewrite MapFacts.F.empty_o : var_db.
#[global] Hint Rewrite Var.MapFacts.F.map_in_iff : var_db.

#[global] Hint Resolve Var.Map.empty_1 : var_db.

  #[global] Instance singletonProper : forall A,
    Proper (@eq t ==> @eq A ==> @Map.Equal A ==> iff) (@Singleton A).
  Proof.
    intros A x1 x2 Heq a1 a2 Ha m1 m2 Hm. subst.
    unfold Singleton.
    rewrite Hm. reflexivity.
  Qed.

  (** Concatenation *)
  
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
  #[global] Hint Rewrite concat_find : var_db.

  #[global] Instance concatProper : forall A,
    Proper (@Var.Map.Equal A ==>
     @Var.Map.Equal A ==> @Var.Map.Equal A) (@Var.concat A).
  Proof.
    intros A m1 m2 Hm n1 n2 Hn.
    intros z.
    repeat rewrite concat_find.
    rewrite Hm.
    destruct (Map.find z m2); auto.
  Qed.

  Lemma concat_in : forall A x (m1 m2 : Map.t A),
    Map.In x (concat m1 m2) <-> Map.In x m1 \/ Map.In x m2.
  Proof.
    intros A x m1 m2.
    repeat rewrite MapFacts.F.in_find_iff.
    rewrite concat_find.
    destruct (Map.find x m1); auto.
    * split; [intros | intros [? | ?]]; auto.
      inversion 1.
    * split; [intros | intros [? | ?]]; auto.
  Qed.
  #[global] Hint Rewrite concat_in : var_db.

  Lemma map_concat : forall {A B} (f : A -> B) m1 m2,
    Var.Map.Equal (Var.Map.map f (Var.concat m1 m2))
                  (Var.concat (Var.Map.map f m1) (Var.Map.map f m2)).
  Proof.
      intros.
      intros z.
      autorewrite with var_db.
      destruct (Map.find z m1); auto.
  Qed.
  #[global] Hint Rewrite @map_concat : var_db.


  Lemma concat_assoc : forall {A} (m1 m2 m3 : Var.Map.t A),
    Var.Map.Equal (Var.concat m1 (Var.concat m2 m3)) (Var.concat (Var.concat m1 m2) m3).
  Proof.
      intros.
      intros z.
      autorewrite with var_db.
      destruct (Map.find z m1); auto.
  Qed.

  (** Lemmas about FSets *)

  Lemma fset_in_union : forall x X1 X2,
    Var.FSet.In x (Var.FSet.union X1 X2)
    <->
    Var.FSet.In x X1 \/ Var.FSet.In x X2.
  Proof.
    intros x X1 X2. split.
    - apply Var.FSet.union_1.
    - intros [H | H].
      + apply Var.FSet.union_2; exact H.
      + apply Var.FSet.union_3; exact H.
  Qed.
  #[global] Hint Rewrite fset_in_union : var_db.

  (** General properties of maps *)

  Lemma eq_dec_refl : forall x,
    eq_dec x x = left (eq_refl x).
  Proof.
    intros.
    induction x; simpl; auto.
    rewrite IHx; auto.
  Qed.
  #[global] Hint Rewrite eq_dec_refl : var_db.


  Lemma singleton_singleton : forall A x (a : A),
    Var.Singleton x a (Var.Map.add x a (Var.Map.empty _)).
  Proof.
    intros A x a.
    intros z.
    reflexivity.
  Qed.

  (** Lemmas about remove *)

  Lemma var_remove_not_in : forall A x (m : Var.Map.t A),
    ~ Var.Map.In x m ->
    Var.Map.Equal
      (Var.Map.remove x m)
      m.
  Proof.
    intros ? ? ? Hin.
    intros z.
    autorewrite with var_db.

    destruct (Map.E.eq_dec x z); auto.
    {
      subst. apply MapFacts.F.not_find_in_iff in Hin.
      auto.
    }
  Qed.

  Lemma var_remove_map : forall A B x (f : A -> B) m,
    Var.Map.Equal
      (Var.Map.remove x (Var.Map.map f m))
      (Var.Map.map f (Var.Map.remove x m)).
  Proof.
    intros A B x f m z;
      autorewrite with var_db.
    destruct (Map.E.eq_dec x z) as [Heq | Hneq];
      subst; simpl; auto.
  Qed.
  #[global] Hint Rewrite var_remove_map : var_db.




  Ltac compare x y :=
    try replace (Map.E.eq_dec x y) with (eq_dec x y) in *; auto;
    destruct (eq_dec x y); subst;
      try contradiction.

  Ltac reduce_eq_dec :=
    match goal with
    | [ |- context[eq_dec ?x ?y] ] => compare x y
    | [ H : context[eq_dec ?x ?y] |- _ ] => compare x y
    | [ |- context[Map.E.eq_dec ?x ?y] ] => compare x y
    | [ H : context[Map.E.eq_dec ?x ?y] |- _ ] => compare x y
    end.

  Lemma remove_add : forall A x y (v : A) Gamma,
    Var.Map.Equal
      (Var.Map.remove x (Var.Map.add y v Gamma))
      (if eq_dec x y then Map.remove x Gamma else Var.Map.add y v (Var.Map.remove x Gamma)).
  Proof.
    intros.
    intros z.
      autorewrite with var_db.
      repeat (reduce_eq_dec; autorewrite with var_db; auto).
  Qed.
  #[global] Hint Rewrite remove_add : var_db.

  Lemma remove_empty : forall A x,
    Map.Equal (Map.remove x (@Map.empty A))
      (@Map.empty A).
  Proof.
    intros A x y.
    destruct (eq_dec x y) as [Heq | Hneq].
    - subst. rewrite MapFacts.F.remove_eq_o; auto.
    - rewrite MapFacts.F.remove_neq_o; auto.
  Qed.
  #[global] Hint Rewrite remove_empty : var_db.


  Lemma map_add : forall {A B} (f : A -> B) x a m,
    Var.Map.Equal (Var.Map.map f (Var.Map.add x a m))
                  (Var.Map.add x (f a) (Var.Map.map f m)).
  Proof.
    intros.
    intros z. autorewrite with var_db.
    compare x z; auto.
  Qed.
  #[global] Hint Rewrite @map_add : var_db.

  (*** Emtpy maps *)

  Lemma empty_map_equal : forall {A} (m : Var.Map.t A),
    Var.Map.Empty m -> Var.Map.Equal m (Var.Map.empty A).
  Proof.
    intros A m Hempty k.
    destruct (Var.Map.find k m) eqn:Hfind.
    - apply Var.Map.find_2 in Hfind. exfalso. eapply Hempty; eauto.
    - destruct (Var.Map.find k (Var.Map.empty A)) eqn:Hfind'.
      + apply Var.Map.find_2 in Hfind'.
        apply Var.MapFacts.F.empty_mapsto_iff in Hfind'. contradiction.
      + reflexivity.
  Qed.
  #[global] Hint Resolve @empty_map_equal : var_db.

  Lemma empty_map_Empty : forall {A B} (f : A -> B) m,
    Var.Map.Empty (Var.Map.map f m) <->
    Var.Map.Empty m.
  Proof.
    intros A B f m. split.
    - intros Hempty k v Hmaps.
      apply (Hempty k (f v)).
      apply Var.Map.map_1; exact Hmaps.
    - intros Hempty k v Hmaps.
      apply MapFacts.F.map_mapsto_iff in Hmaps.
      destruct Hmaps as [a [_ Ha]].
      exact (Hempty k a Ha).
  Qed.
  Lemma empty_map_empty : forall {A B} (f : A -> B),
    Var.Map.Equal (Var.Map.map f (Var.Map.empty A)) (Var.Map.empty B).
  Proof.
    intros A B f k.
    rewrite MapFacts.F.map_o.
    rewrite MapFacts.F.empty_o.
    reflexivity.
  Qed.
  #[global] Hint Rewrite @empty_map_empty : var_db.


  Lemma singleton_remove : forall {A} (a : A) x m,
    Var.Singleton x a m ->
    Var.Map.Empty (Var.Map.remove x m).
  Proof.
    intros A a x m H.
    unfold Var.Singleton in H.
    rewrite H.
    autorewrite with var_db.
    apply Map.empty_1.
  Qed.
  #[global] Hint Resolve @singleton_remove : var_db.

  Ltac subst_eq_hypothesis_fwd m :=
    repeat match goal with
    | [ Heq : Var.Map.Equal m _, H : context[m] |- _ ] =>
      setoid_rewrite Heq in H
    | [ Heq : Var.Map.Equal m _ |- context[m] ] =>
      setoid_rewrite Heq
    end;
    (* if there are no more occurrences of m, clear Heq *)
    try match goal with
    | [ Heq : Var.Map.Equal m _ |- _ ] => clear m Heq
    end.

  Ltac subst_eq_hypothesis_bwd m :=
    repeat match goal with
    | [ Heq : Var.Map.Equal _ m, H : context[m] |- _ ] =>
      setoid_rewrite <- Heq in H
    | [ Heq : Var.Map.Equal _ m |- context[m] ] =>
      setoid_rewrite <- Heq
    end;
    (* if there are no more occurrences of m, clear Heq *)
    try match goal with
    | [ Heq : Var.Map.Equal _ m |- _ ] => clear m Heq
    end.

  Ltac subst_map :=
    repeat match goal with
    | [ Heq : Var.Map.Equal ?m ?m |- _ ] => clear Heq; try clear m
    | [ Heq : Var.Map.Equal ?m _ |- _ ] =>
      subst_eq_hypothesis_fwd m
    (*| [ Heq : Var.Map.Equal _ ?m |- _ ] =>
      subst_eq_hypothesis m
      *)
    end.
  (*
    repeat match goal with
    | [ Heq : Var.Map.Equal (Var.Map.empty _) ?m2, H : context[?m2] |- _ ] =>
      setoid_rewrite <- Heq in H;
      try rewrite <- Heq in *;
      clear Heq
    | [ Heq : Var.Map.Equal (Var.Map.empty _) ?m2 |- context[?m2] ] =>
      setoid_rewrite <- Heq;
      try rewrite <- Heq in *;
      clear Heq
    | [ Heq : Var.Map.Equal ?m1 (Var.Map.empty _), H : context[?m1] |- _ ] =>
      setoid_rewrite Heq in H;
      try rewrite Heq in *;
      clear Heq
    | [ Heq : Var.Map.Equal ?m1 (Var.Map.empty _) |- context[?m1] ] =>
      setoid_rewrite Heq;
      try rewrite Heq in *;
      clear Heq

    | [ Heq : Var.Map.Equal ?m1 ?m2, H : context[?m1] |- _ ] =>
      setoid_rewrite Heq in H;
      try rewrite Heq in *;
      try clear m1 Heq
    | [ Heq : Var.Map.Equal ?m1 ?m2 |- context[?m1] ] =>
      setoid_rewrite Heq;
      try rewrite Heq in *;
      try clear m1 Heq
    end.
    *)

  Ltac simpl_Empty :=
      match goal with 
      | [ H : Var.Map.Empty (Var.Map.map _ _) |- _ ] =>
        apply empty_map_Empty in H
      | [ |- Var.Map.Empty (Var.Map.map _ _) ] =>
        apply empty_map_Empty

      (* Replace any instances of Empty m with m == empty
      and substitute *)
      | [ H : Var.Map.Empty ?m |- _ ] =>
        apply empty_map_equal in H;
        subst_map
      end.





  (** Lemmas about disjointness *)

  Lemma concat_disjoint : forall {A} (m1 m2 m3 : Var.Map.t A),
    Var.MapFacts.Disjoint m1 (Var.concat m2 m3) <->
    Var.MapFacts.Disjoint m1 m2 /\ Var.MapFacts.Disjoint m1 m3.
  Proof.
    intros A m1 m2 m3.
    unfold MapFacts.Disjoint.
    repeat split; intros.
    * specialize (H k); autorewrite with var_db in H.
      firstorder.
    * specialize (H k); autorewrite with var_db in H.
      firstorder.
    * autorewrite with var_db.
      firstorder.
  Qed.
  #[global] Hint Rewrite @concat_disjoint : var_db.

  Lemma disjoint_sym : forall {A} (m1 m2 : Var.Map.t A),
    Var.MapFacts.Disjoint m1 m2 ->
    Var.MapFacts.Disjoint m2 m1.
  Proof.
    intros ? ? ? H.
    unfold MapFacts.Disjoint.
    intros k; specialize (H k). firstorder.
  Qed.
  Lemma disjoint_map : forall {A B} (f : A -> B) m1 m2,
    Var.MapFacts.Disjoint (Var.Map.map f m1) (Var.Map.map f m2)
    <-> Var.MapFacts.Disjoint m1 m2.
  Proof.
    intros A B f m1 m2.
    unfold Var.MapFacts.Disjoint.
    split; intros H k [Hin1 Hin2].
    - apply (H k). split.
      + apply MapFacts.F.map_in_iff; exact Hin1.
      + apply MapFacts.F.map_in_iff; exact Hin2.
    - apply MapFacts.F.map_in_iff in Hin1.
      apply MapFacts.F.map_in_iff in Hin2.
      exact (H k (conj Hin1 Hin2)).
  Qed.

  Lemma disjoint_empty_1 : forall A m,
    Var.MapFacts.Disjoint (Var.Map.empty A) m.
  Proof.
    intros. intros z.
    rewrite MapFacts.F.empty_in_iff.
    intros [? ?]; contradiction.
  Qed.
  Lemma disjoint_empty_2 : forall A m,
    Var.MapFacts.Disjoint m (Var.Map.empty A).
  Proof.
    intros. intros z.
    rewrite MapFacts.F.empty_in_iff.
    intros [? ?]; contradiction.
  Qed.
  #[global] Hint Resolve disjoint_empty_1 disjoint_empty_2 : var_db.

  Lemma disjoint_remove_1 : forall {A} (m1 m2 : Map.t A) x,
    MapFacts.Disjoint m1 m2 ->
    MapFacts.Disjoint (Map.remove x m1) m2.
  Admitted.
  Lemma disjoint_remove_2 : forall {A} (m1 m2 : Map.t A) x,
    MapFacts.Disjoint m1 m2 ->
    MapFacts.Disjoint m1 (Map.remove x m2).
  Proof.
    intros.
    apply disjoint_sym. apply disjoint_remove_1.
    apply disjoint_sym. auto.
  Qed.

 
  Ltac reduce_disjoint :=
  repeat match goal with
        | [ H : Var.MapFacts.Disjoint ?m1 ?m2 |- Var.MapFacts.Disjoint ?m2 ?m1 ] =>
          apply disjoint_sym; exact H

        | [ |- Var.MapFacts.Disjoint (Var.Map.map _ _) (Var.Map.map _ _)] =>
          apply disjoint_map
        | [ H : Var.MapFacts.Disjoint (Var.Map.map _ _) (Var.Map.map _ _) |- _] =>
          apply disjoint_map in H

        | [ |- Var.MapFacts.Disjoint _ (Var.concat _ _)] =>
          apply concat_disjoint; split
        | [ |- Var.MapFacts.Disjoint _ (Var.concat _ _)] =>
          apply disjoint_sym; apply concat_disjoint; split; apply disjoint_sym
        | [ H : Var.MapFacts.Disjoint _ (Var.concat _ _) |- _ ] =>
          apply concat_disjoint in H;
          destruct H
        | [ H : Var.MapFacts.Disjoint (Var.concat _ _) _ |- _ ] =>
          apply disjoint_sym in H;
          apply concat_disjoint in H;
          let H1 := fresh "Hdisj" in
          let H2 := fresh "Hdisj" in
          destruct H as [H1 H2];
          apply disjoint_sym in H1;
          apply disjoint_sym in H2

        | [ |- Var.MapFacts.Disjoint (Map.empty _) _ ] =>
          apply disjoint_empty_1
        | [ |- Var.MapFacts.Disjoint _ (Map.empty _) ] =>
          apply disjoint_empty_2
  end.


  (** Reflection between partition and concat *)


  Lemma partition_concat : forall {A} (m m1 m2 : Var.Map.t A),
    Var.MapFacts.Partition m m1 m2 <->
    Var.MapFacts.Disjoint m1 m2 /\ Var.Map.Equal m (Var.concat m1 m2).
  Proof.
    intros A m m1 m2.
    split; [intros [Hdisj Hpart] | intros [Hdisjoint Heq]].
    * split; auto.
      intros k.
      rewrite concat_find.
      destruct (Map.find k m1) as [ a |] eqn:Hfind1.
      { specialize (Hpart k a);
        repeat rewrite MapFacts.F.find_mapsto_iff in Hpart.
        apply Hpart; auto.
      }
      destruct (Map.find k m2) as [a | ] eqn:Hfind2.
      {
        specialize (Hpart k a);
        repeat rewrite MapFacts.F.find_mapsto_iff in Hpart.
        apply Hpart; auto.
      }
      destruct (Map.find k m) as [a | ] eqn:Hfind; auto.
      { (* contradiction *)
        contradict Hfind.
        specialize (Hpart k a);
        repeat rewrite MapFacts.F.find_mapsto_iff in Hpart.
        rewrite Hpart, Hfind1, Hfind2.
        inversion 1; discriminate.
      }
    * split; auto.
      intros k a.
      rewrite Heq.
      repeat rewrite MapFacts.F.find_mapsto_iff.
      rewrite concat_find.
      destruct (Map.find k m1) eqn:Hfind1.
      {
        destruct (Map.find k m2) eqn:Hfind2; auto;
          try (firstorder; fail).
        { unfold MapFacts.Disjoint in Hdisjoint.
          exfalso; apply (Hdisjoint k).
          repeat rewrite MapFacts.F.in_find_iff.
          rewrite Hfind1, Hfind2.
          split; inversion 1.
        }
        firstorder. discriminate.
      }
      destruct (Map.find k m2) eqn:Hfind2; auto.
      {
        firstorder; try discriminate.
      }
      firstorder.
  Qed.

  Lemma concat_sym : forall {A} (m1 m2 : Var.Map.t A),
    Var.MapFacts.Disjoint m1 m2 ->
    Var.Map.Equal (Var.concat m1 m2) (Var.concat m2 m1).
  Proof.
    intros A m1 m2 Hdisj z.
    autorewrite with var_db.
    destruct (Map.find z m1) eqn:Hfind1; destruct (Map.find z m2) eqn:Hfind2; auto.
    exfalso. apply (Hdisj z). split.
    - apply MapFacts.F.in_find_iff. rewrite Hfind1; discriminate.
    - apply MapFacts.F.in_find_iff. rewrite Hfind2; discriminate.
  Qed.

  Ltac reflect_partition :=
    repeat match goal with
          | [ H : Var.MapFacts.Partition ?m ?m1 ?m2 |- _ ] =>
            apply partition_concat in H;
            let Hdisj := fresh "Hdisj" in
            let Heq := fresh "Heq" in
            destruct H as [Hdisj Heq];
            subst_map
          | [ |- Var.MapFacts.Partition ?m ?m1 ?m2 ] =>
            apply partition_concat; split
          | [ H : context[Var.Map.map _ (Var.concat _ _)] |- _] =>
            rewrite map_concat in H
          | [ |- context[Var.Map.map _ (Var.concat _ _)] ] =>
            rewrite map_concat
    end.

    (** Lemmas about Partition *)

    (*** If Δ(x0)=τ0 and Δ==Δ1,Δ2 and x ∉ Δ2 then Δ1(x0)=τ0 *)
    Lemma partition_not_in_r : forall {A} Δ Δ2 Δ1 x (τ : A),
      Var.Map.MapsTo x τ Δ ->
      Var.MapFacts.Partition Δ Δ1 Δ2 ->
      ~ (Var.Map.In x Δ2) ->
      Var.Map.MapsTo x τ Δ1.
    Proof.
      intros ? ? ? ? x τ Hx [Hdisjoint Hmapsto] Hnotin.
      apply Hmapsto in Hx.
      destruct Hx; auto.
      * contradict Hnotin.
        exists τ; auto.
    Qed.


    Lemma partition_empty_l : forall A m,
      Var.MapFacts.Partition m (Var.Map.empty A) m.
    Proof.
      intros.
      reflect_partition.
      * reduce_disjoint.
      * intros z. autorewrite with var_db; auto.
    Qed.
    Lemma partition_empty_r : forall A m,
      Var.MapFacts.Partition m m (Var.Map.empty A).
    Proof.
      intros.
      reflect_partition.
      * reduce_disjoint.
      * intros z. autorewrite with var_db; auto.
        destruct (Map.find z m); auto.
    Qed.

    Lemma partition_add_l : forall A x (a:A) m m1 m2,
      Var.MapFacts.Partition m m1 m2 ->
      ~ Map.In x m2 ->
      Var.MapFacts.Partition (Var.Map.add x a m) (Var.Map.add x a m1) m2.
    Proof.
      intros.
      reflect_partition.
      * unfold MapFacts.Disjoint in *.
        intros k [Hin1 Hin2].
        autorewrite with var_db in Hin1.
        apply (Hdisj k). split; auto.
        destruct Hin1; subst; auto.
        contradiction.
      * intros z. autorewrite with var_db.
        reduce_eq_dec; auto.
    Qed.
    Lemma partition_add_r : forall A x (a:A) m m1 m2,
      Var.MapFacts.Partition m m1 m2 ->
      ~ Map.In x m1 ->
      Var.MapFacts.Partition (Var.Map.add x a m) m1 (Var.Map.add x a m2).
    Proof.
      intros.
      apply Var.MapFacts.Partition_sym.
      apply partition_add_l; auto.
      apply Var.MapFacts.Partition_sym; auto.
    Qed.


    Lemma partition_remove : forall {A} x0 (Δ Δ1 Δ2 : Var.Map.t A),
      Var.MapFacts.Partition Δ Δ1 Δ2 ->
      Var.MapFacts.Partition (Var.Map.remove x0 Δ) (Var.Map.remove x0 Δ1) (Var.Map.remove x0 Δ2).
    Proof.
      intros A x0 Δ Δ1 Δ2 Hpart.
      reflect_partition.
      - (* Disjoint (remove x0 Δ1) (remove x0 Δ2) *)
        apply disjoint_remove_1.
        apply disjoint_remove_2.
        auto.
      -
        intros k.
        autorewrite with var_db in *.
        reduce_eq_dec; auto.
    Qed.


    Lemma partition_empty_inv1 : forall {A} (Δ1 Δ2 : Var.Map.t A),
      Var.MapFacts.Partition (Var.Map.empty _) Δ1 Δ2 ->
      Var.Map.Equal Δ1 (Var.Map.empty _).
    Admitted.
    Lemma partition_empty_inv2 : forall {A} (Δ1 Δ2 : Var.Map.t A),
      Var.MapFacts.Partition (Var.Map.empty _) Δ1 Δ2 ->
      Var.Map.Equal Δ2 (Var.Map.empty _).
    Admitted.


    Lemma partition_map_iff : forall A B (f : A -> B) m m1 m2,
      Var.MapFacts.Partition m m1 m2 <->
      Var.MapFacts.Partition (Var.Map.map f m) (Var.Map.map f m1) (Var.Map.map f m2).
    Admitted.


    Lemma partition_map_inv : forall A B (f : A -> B) m n1 n2,
      Var.MapFacts.Partition (Var.Map.map f m) n1 n2 ->
      exists m1 m2,
        Var.Map.Equal n1 (Var.Map.map f m1)
        /\
        Var.Map.Equal n2 (Var.Map.map f m2)
        /\
        Var.MapFacts.Partition m m1 m2.
    Admitted.

    Lemma partition_empty1_eq : forall A m m0,
        Var.MapFacts.Partition m (Var.Map.empty A) m0 ->
        Var.Map.Equal m m0.
    Admitted.
    Lemma partition_empty2_eq : forall A m m0,
        Var.MapFacts.Partition m m0 (Var.Map.empty A) ->
        Var.Map.Equal m m0.
    Admitted.

    
    Ltac reduce_partition :=
    match goal with

      (* Partitions with the empty map *)
      | [ H : Var.MapFacts.Partition (Var.Map.empty _) ?D1 ?D2 |- _ ] =>
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        assert (H1 : Map.Equal D1 (Map.empty _))
          by (exact (partition_empty_inv1 D1 D2 H));
        assert (H2 : Map.Equal D2 (Map.empty _))
          by (exact (partition_empty_inv2 D1 D2 H));
        subst_map;
        try clear H
      
      | [ H : Var.MapFacts.Partition ?m (Var.Map.empty _) ?m0 |- _ ] =>
        apply partition_empty1_eq in H;
        subst_map
      | [ H : Var.MapFacts.Partition ?m ?m0 (Var.Map.empty _) |- _ ] =>
        apply partition_empty2_eq in H;
        subst_map

      (* Partitions with remove*)
      | [ |- Var.MapFacts.Partition (Var.Map.remove ?x _) (Var.Map.remove ?x _) (Var.Map.remove ?x _) ] =>
        apply partition_remove

      (* Partitions with map *)
      | [ |- Var.MapFacts.Partition (Var.Map.map ?f _) (Var.Map.map ?f _) (Var.Map.map ?f _) ] =>
        apply partition_map_iff
      | [ H : Var.MapFacts.Partition (Var.Map.map ?f _) (Var.Map.map ?f _) (Var.Map.map ?f _) |- _ ] =>
        apply partition_map_iff in H

      | [H : Var.MapFacts.Partition (Var.Map.map ?f ?m) ?n1 ?n2 |- _] =>
        let m1 := fresh "m1" in
        let m2 := fresh "m2" in
        let Heq1 := fresh "Heq1" in
        let Heq2 := fresh "Heq2" in
        destruct (partition_map_inv _ _ _ _ _ _ H)
          as [m1 [m2 [Heq1 [Heq2 Hpart]]]]; auto;
        subst_map; try rewrite Heq1, Heq2 in *; try clear n1 Heq1 n2 Heq2
    end.


    Ltac vsimpl :=
    repeat match goal with
    | [ |- Map.Empty _ ] => simpl_Empty
    | [ H : Map.Empty _ |- _ ] => simpl_Empty

    | [ |- MapFacts.Disjoint _ _ ] => reduce_disjoint
    | [ H : MapFacts.Disjoint _ _ |- _ ] => reduce_disjoint

    | [ |- context[Var.MapFacts.Partition _ _ _ ]] =>
      reduce_partition
    | [ H : context[Var.MapFacts.Partition _ _ _ ] |- _ ] =>
      reduce_partition

    | [ H : Map.Equal _ _ |- _ ] => subst_map
    end.

  End Proofs.


Module Tactics.
  (**
    Provides:
      * compare x y       - destructs eq_dec x y (or Map.E.eq_dec x y) and substitutes
      * reduce_eq_dec     - applies compare to goals/hypotheses containing eq_dec or Map.E.eq_dec
      * subst_map         - eliminates hypotheses of the form Map.Equal m1 m2 by rewriting
      * reflect_partition - converts Partition hypotheses into Disjoint + Map.Equal (concat) form
      * vsimpl            - simplifies hypotheses and goals that use maps

    vsimpl builds on the following tactics in Proofs:
      * simpl_Empty       - simplifies Map.Empty goals/hypotheses and substitutes
      * reduce_disjoint   - simplifies Disjoint goals/hypotheses using symmetry and concat lemmas
      * reduce_partition  - simplifies Partition hypotheses

    In addition, there is are rewrite and auto databases for simplifying goals:
      * autorewrite with var_db [in H]
      * auto/eauto with var_db
  *)
  Ltac compare x y := Proofs.compare x y.
  Ltac reduce_eq_dec := Proofs.reduce_eq_dec.
  Ltac subst_map := Proofs.subst_map.
  Ltac reflect_partition := Proofs.reflect_partition.
  Ltac vsimpl := Proofs.vsimpl.
End Tactics.

End Var.
*)


Inductive unitary :=
| H | X | Y | Z | CNOT | SGATE | Sdag | TGATE | Tdag.


Module Config.
  
  Record t := {
    dim : nat;
    (*qrefs : Var.Map.t nat;*)
    qstate : Matrix dim dim
  }.

  (*
  Module Refs.
    Definition Partition cfg cfg1 cfg2 :=
      Var.MapFacts.Partition (qrefs cfg) (qrefs cfg1) (qrefs cfg2).
    Definition Singleton x cfg :=
      Var.Map.In x (qrefs cfg) /\ Var.Map.cardinal (qrefs cfg) = 1%nat.
    Definition Empty cfg :=
      Var.Map.Empty (qrefs cfg).

  End Refs.
  *)

  Record WellScoped (refs : Var.Map.t nat) (cfg : t) := {
    wf_qstate : Matrix.WF_Matrix (qstate cfg);
    wf_qrefs : List.Forall
              (fun x => snd x < dim cfg)%nat
              (Var.Map.elements refs)
  }.

  
    Definition find (x : Var.t) refs : nat :=
      match Var.Map.find x refs with
      | Some q => q
      | None   => 0%nat
      end.
      


  (* Project onto the state where qubit q is in the classical state |b> *)
  (*Definition proj q dim (b : bool) := pad_u dim q (bool_to_matrix b).*)
  Definition measure (b : bool) (x : Var.t) refs (cfg : t)
    : Var.Map.t nat * t :=
    let q := find x refs in
    let rho' := super (pad_u q (dim cfg) (bool_to_matrix b)) (qstate cfg) in
    (Var.Map.remove x refs, {|
      dim := dim cfg;
      qstate := rho'
    |}).

  Definition new (b : bool) refs (cfg : t) : Var.t * Var.Map.t nat * t :=
    let x := Var.fresh refs in
    let q := dim cfg in
    let rho' := kron (qstate cfg) (bool_to_ket b) in
    (x, Var.Map.add x q refs, {|
      dim := 1 + dim cfg;
      qstate := rho'
    |}).

  Definition apply_matrix (cfg : t) (U : Matrix (2 ^ dim cfg) (2 ^ dim cfg)) : t :=
  {|
    dim := dim cfg;
    qstate := super U (qstate cfg)
  |}.
  
  (**
    Inputs:
      - refs : an assignment of variables in indices in cfg
      - cfg : a configuration of dimension d
    Returns:
      - a fresh variable x
      - an updated map that includes refs along with x |-> d
      - an updated configuration where the dimension has been incremented to d+1
    Note that the quantum state inside the resulting configuration still has dimension d, and will need to be incremented.
  *)
  Definition fresh_var (refs : Var.Map.t nat) (cfg : t) : Var.t * Var.Map.t nat * t :=
    let d := dim cfg in
    let x := Var.fresh refs in
    let refs' := Var.Map.add x d refs in
    let cfg' := {| dim := 1 + dim cfg; qstate := qstate cfg |} in
    (x, refs', cfg').

  Definition epr_cfg cfg : nat * nat * t :=
    let d := dim cfg in
    let bell00 := Quantum.EPRpair † × Quantum.EPRpair in
    let rho' := kron (qstate cfg) bell00 in
    (d, 1+d, {|
      dim := 2 + dim cfg;
      qstate := rho'
    |})%nat.

  Definition epr refs (cfg : t) : Var.t * Var.t * Var.Map.t nat * t :=
    match epr_cfg cfg with
    | (idx1, idx2, cfg') =>
      let x1 := Var.fresh refs in
      let refs' := Var.Map.add x1 idx1 refs in
      let x2 := Var.fresh refs' in
      let refs'' := Var.Map.add x2 idx2 refs' in
      (x1, x2, refs'', cfg')
    end.


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

  Definition apply_gate (U : unitary) (xs : list Var.t) refs (cfg : t) : t :=
    let qs := List.map (fun x => find x refs) xs in
    apply_matrix cfg (gate_to_matrix _ U qs).

  (*
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
  *)

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


  Module V := OrderedTypeEx.UOT_to_OT (OrderedTypeEx.String_as_OT).
  Include V.
  
  Module Map := FMap(V).
  Module FSet := Map.S.

(*  #[global] Existing Instance MapProofs.F.EqualSetoid.*)

  Create HintDb actor_db.
  (*
  #[global] Hint Rewrite Actor.FSet.Facts.inter_iff : actor_db.
  #[global] Hint Rewrite Actor.FSetFacts.add_iff : actor_db.
  #[global] Hint Rewrite Actor.FSetFacts.singleton_iff : actor_db.
*)

End Actor.


Module ChorEnv.
    Definition t T := Actor.Map.t (Var.Map.t T).
    (* equivalence of ChorEnv.t *)
    Definition Equal {T} (G1 G2 : t T) : Prop := Actor.Map.Equiv (Var.Map.Equal) G1 G2.
    Definition find {T} (A : Actor.t) (G : t T) : Var.Map.t T :=
        match Actor.Map.find A G with
        | Some D => D
        | None => Var.Map.empty _
        end.

    Definition add {T} (A : Actor.t) (x : Var.t) (tau : T) (G : t T) : t T :=
        let D := find A G in
        Actor.Map.add A (Var.Map.add x tau D) G.

    Definition MapsTo {T} (A : Actor.t) (x : Var.t) (tau : T) (G : t T) : Prop :=
      Var.Map.MapsTo x tau (find A G).


  Definition epr (A B : Actor.t) (refs : t nat) (cfg : Config.t)
                 : Var.t * Var.t * t nat * Config.t :=
    match Config.epr_cfg cfg with
    | (idx1, idx2, cfg') =>
      let x1 := Var.fresh (find A refs) in
      let refs' := add A x1 idx1 refs in
      let x2 := Var.fresh (find B refs') in
      let refs'' := add B x2 idx2 refs' in

      (x1, x2, refs'', cfg')
    end.
End ChorEnv.