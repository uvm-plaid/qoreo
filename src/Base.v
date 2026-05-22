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
Create HintDb actor_db.
Create HintDb qoreo_db.

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
  #[local] Existing Instance F.EqualSetoid.
  #[local] Hint Rewrite F.add_mapsto_iff : qoreo_db.
  #[local] Hint Rewrite F.empty_mapsto_iff : qoreo_db.
  #[local] Hint Rewrite F.add_in_iff : qoreo_db.
  #[local] Hint Rewrite F.map_o : qoreo_db.
  #[local] Hint Rewrite F.remove_o : qoreo_db.
  #[local] Hint Rewrite F.add_o : qoreo_db.
  #[local] Hint Rewrite F.empty_o : qoreo_db.
  #[local] Hint Rewrite F.map_in_iff : qoreo_db.
  #[local] Hint Resolve M.empty_1 : qoreo_db.
  #[local] Hint Resolve Properties.Partition_sym : qoreo_db.

  Module Proofs.

  #[local] Instance singletonProper : forall A,
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
  #[local] Hint Rewrite concat_find : qoreo_db.

  #[local] Instance concatProper : forall A,
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
  #[local] Hint Rewrite concat_in : qoreo_db.

  Lemma map_concat : forall {A B} (f : A -> B) m1 m2,
    M.Equal (M.map f (concat m1 m2))
            (concat (M.map f m1) (M.map f m2)).
  Proof.
      intros.
      intros z.
      autorewrite with qoreo_db.
      destruct (M.find z m1); auto.
  Qed.
  #[local] Hint Rewrite @map_concat : qoreo_db.

  Lemma concat_assoc : forall {A} (m1 m2 m3 : M.t A),
    M.Equal (concat m1 (concat m2 m3)) (concat (concat m1 m2) m3).
  Proof.
      intros.
      intros z.
      autorewrite with qoreo_db.
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
  #[local] Existing Instance FSetProperties.Equal_ST.
  #[local] Instance domainProper : forall A,
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
  #[local] Hint Rewrite fset_in_union : qoreo_db.

  (** General properties of maps *)

  Lemma remove_not_in : forall A x (m : M.t A),
    ~ M.In x m ->
    M.Equal
      (M.remove x m)
      m.
  Proof.
    intros ? ? ? Hin.
    intros z.
    autorewrite with qoreo_db.
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
      autorewrite with qoreo_db.
    destruct (E.eq_dec x z) as [Heq | Hneq];
      subst; simpl; auto.
  Qed.
  #[local] Hint Rewrite remove_map : qoreo_db.

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
    autorewrite with qoreo_db.
    repeat (reduce_eq_dec; autorewrite with qoreo_db; auto).
  Qed.
  #[local] Hint Rewrite remove_add : qoreo_db.


  Lemma add_remove_eq : forall A x (a : A) m,
    M.Equal (M.add x a (M.remove x m))
                  (M.add x a m).
  Admitted.
  #[local] Hint Rewrite add_remove_eq : var_db.

  Lemma add_mapsto : forall A x (a : A) m,
    M.MapsTo x a m ->
    M.Equal (M.add x a m)
                  m.
  Admitted.
  #[local] Hint Resolve add_mapsto : var_db.


  Lemma add_neq_sym : forall A x y (a b : A) m,
  x <> y ->
  M.Equal (M.add x a (M.add y b m))
          (M.add y b (M.add x a m)).
  Admitted.

  Lemma add_add_eq : forall A x (a b : A) m,
    M.Equal 
      (M.add x a (M.add x b m))
      (M.add x a m).
  Admitted.

  Lemma remove_empty : forall A x,
    M.Equal (M.remove x (@M.empty A))
      (@M.empty A).
  Proof.
    intros A x y.
    autorewrite with qoreo_db.
    reduce_eq_dec; auto.
  Qed.
  #[local] Hint Rewrite remove_empty : qoreo_db.

  Lemma map_add : forall {A B} (f : A -> B) x a m,
    M.Equal (M.map f (M.add x a m))
            (M.add x (f a) (M.map f m)).
  Proof.
    intros.
    intros z. autorewrite with qoreo_db.
    compare x z; auto.
  Qed.
  #[local] Hint Rewrite @map_add : qoreo_db.

  (** Empty maps *)

  Lemma empty_map_equal : forall {A} (m : M.t A),
    M.Empty m -> M.Equal m (M.empty A).
  Proof.
    intros A m Hempty k.
    autorewrite with qoreo_db.
    destruct (M.find k m) eqn:Hfind; auto.
    apply M.find_2 in Hfind. exfalso. eapply Hempty; eauto.
  Qed.
  #[local] Hint Resolve @empty_map_equal : qoreo_db.

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
    autorewrite with qoreo_db.
    reflexivity.
  Qed.
  #[local] Hint Rewrite @empty_map_empty : qoreo_db.

  Lemma add_not_Empty : forall A x (a : A) m,
    ~ M.Empty (M.add x a m).
  Admitted.

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
    autorewrite with qoreo_db.
    compare x x.
    autorewrite with qoreo_db.
    apply M.empty_1.
  Qed.
  #[local] Hint Resolve @singleton_remove : qoreo_db.

  Lemma singleton_add_inversion : forall A x (a : A) y b m,
    Singleton x a (M.add y b m) ->
    x = y /\ a = b /\ M.Empty m.
  Admitted.

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
      | [ H : M.Empty (M.add _ _ _) |- _ ] =>
        exfalso; apply (add_not_Empty _ _ _ _ H)
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

  Ltac simpl_Singleton :=
    match goal with
    | [ H : Singleton _ _ (M.add _ _ _) |- _ ] =>
      apply singleton_add_inversion in H;
      destruct H as [? [? ?]]; subst
    | [ |- Singleton ?x _ (M.add ?a _ (M.empty _)) ] =>
      apply singleton_singleton
    end.

  (** Lemmas about disjointness *)

  Lemma concat_disjoint : forall {A} (m1 m2 m3 : M.t A),
    Disjoint m1 (concat m2 m3) <->
    Disjoint m1 m2 /\ Disjoint m1 m3.
  Proof.
    intros A m1 m2 m3.
    unfold Disjoint.
    repeat split; intros.
    * specialize (H k); autorewrite with qoreo_db in H.
      firstorder.
    * specialize (H k); autorewrite with qoreo_db in H.
      firstorder.
    * autorewrite with qoreo_db.
      firstorder.
  Qed.
  #[local] Hint Rewrite @concat_disjoint : qoreo_db.

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
  #[local] Hint Resolve disjoint_empty_1 disjoint_empty_2 : qoreo_db.

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


  Lemma disjoint_add_1 : forall A m1 m2 x (a : A),
    Disjoint (M.add x a m1) m2 <-> Disjoint m1 m2 /\ ~ M.In x m2.
  Admitted.
  Lemma disjoint_add_2 : forall A m1 m2 x (a : A),
    Disjoint m1 (M.add x a m2) <-> Disjoint m1 m2 /\ ~ M.In x m1.
  Admitted.

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
        | [ |- Disjoint (concat _ _) _] =>
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
    autorewrite with qoreo_db.
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
    * intros z. autorewrite with qoreo_db; auto.
  Qed.
  #[local] Hint Resolve partition_empty_l : qoreo_db.

  Lemma partition_empty_r : forall A m,
    Partition m m (M.empty A).
  Proof.
    intros.
    reflect_partition.
    * reduce_disjoint.
    * intros z. autorewrite with qoreo_db; auto.
      destruct (M.find z m); auto.
  Qed.
  #[local] Hint Resolve partition_empty_r : qoreo_db.

  Lemma partition_add_l : forall A x (a:A) m m1 m2,
    Partition m m1 m2 ->
    ~ M.In x m2 ->
    Partition (M.add x a m) (M.add x a m1) m2.
  Proof.
    intros.
    reflect_partition.
    * unfold Disjoint in *.
      intros k [Hin1 Hin2].
      autorewrite with qoreo_db in Hin1.
      apply (Hdisj k). split; auto.
      destruct Hin1 as [Heq | ?]; auto.
      rewrite Heq in *; clear Heq.
      contradiction.
    * intros z. autorewrite with qoreo_db.
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
      autorewrite with qoreo_db in *.
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

  Lemma partition_add_inversion : forall A (a : A) x m m1 m2,
    Partition (M.add x a m) m1 m2 ->
    ~ M.In x m ->
    (M.MapsTo x a m1 /\ ~ M.In x m2 /\ Partition m (M.remove x m1) m2)
    \/
    (~ M.In x m1 /\ M.MapsTo x a m2 /\ Partition m m1 (M.remove x m2)).
  Admitted.

  Ltac decide_equal :=
    repeat match goal with
    | [ H : M.MapsTo ?x ?a ?m |- Some ?a = M.find ?x ?m ] =>
      symmetry; apply M.find_1; auto
    | [ H : M.MapsTo ?x ?a ?m |- M.find ?x ?m = Some ?a ] =>
      apply M.find_1; auto
    | [ |- M.Equal _ _ ] =>
      intros z; autorewrite with var_db;
      repeat reduce_eq_dec; auto with var_db
    end; fail.

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

      (* partitions with add *)
      | [ H : Partition (M.add _ _ _) _ _ |- _ ] =>
        apply partition_add_inversion in H; auto;
        try destruct H as [[? [? ?]] | [? [? ?]]]

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

  | [ |- Singleton _ _ _ ] => simpl_Singleton
  | [ H : Singleton _ _ _ |- _ ] => simpl_Singleton

  | [ |- Disjoint _ _ ] => reduce_disjoint
  | [ H : Disjoint _ _ |- _ ] => reduce_disjoint

  | [ |- context[Partition _ _ _ ]] =>
    reduce_partition
  | [ H : context[Partition _ _ _ ] |- _ ] =>
    reduce_partition

  | [ H : M.Equal _ _ |- _ ] => subst_map
  end.



  (* move m to the left-most element of the concatenation list *)
  Ltac reduce_concat :=
    repeat match goal with
    | [ |- M.Equal (concat ?m _) (concat ?m _)] =>
      apply concatProper; try reflexivity
    | [ |- M.Equal (concat ?m _) (concat ?m0 ?m1)] =>
      rewrite (concat_sym m0 m1);
        [ | auto with var_db; vsimpl; auto with var_db ];
      repeat rewrite <- concat_assoc
    end.

  Ltac partition_concat :=
    match goal with
    | [ |- Partition (concat ?m1 ?m2) ?m1 _ ] =>
      reflect_partition;
        [ | reflexivity];
        vsimpl; auto with var_db

    | [ |- Partition (concat ?m1 ?m2) ?m2 _ ] =>
      reflect_partition;
        [ | rewrite (concat_sym m1 m2); auto;
            try reflexivity];
        vsimpl; auto with var_db

    | [ |- Partition _ (concat _ _) _ ] =>
      reflect_partition; vsimpl; auto with var_db
    | [ |- Partition _ _ (concat _ _) ] =>
      reflect_partition; vsimpl; auto with var_db
    end;
    reduce_concat.

  End Proofs.


  Module Tactics.
  (**
    Provides:
      * compare x y       - destructs Map.E.eq_dec x y and substitutes
      * reduce_eq_dec     - applies compare to goals/hypotheses containing Map.E.eq_dec
      * subst_map         - eliminates hypotheses of the form Map.Equal m1 m2 by rewriting
      * reflect_partition - converts Partition hypotheses into Disjoint + Map.Equal (concat) form
      * vsimpl            - simplifies hypotheses and goals that use maps

      * decide_equal - tries to prove goals of the form Equal m1 m2 through brute-force reasoning 
      * partition_concat  - simplifies goals specifically that deal with the intersection of partition and concatenation

    vsimpl builds on the following tactics in MapFacts:
      * simpl_Empty       - simplifies Map.Empty goals/hypotheses and substitutes
      * reduce_disjoint   - simplifies Disjoint goals/hypotheses using symmetry and concat lemmas
      * reduce_partition  - simplifies Partition hypotheses

    In addition, there are rewrite and auto databases for simplifying goals:
      * autorewrite with qoreo_db [in H]
      * auto/eauto with qoreo_db
  *)
    Ltac compare x y := Proofs.compare x y.
    Ltac reduce_eq_dec := Proofs.reduce_eq_dec.
    Ltac subst_map := Proofs.subst_map.
    Ltac reflect_partition := Proofs.reflect_partition.
    Ltac vsimpl := Proofs.vsimpl.
    Ltac partition_concat := Proofs.partition_concat.
    Ltac decide_equal := Proofs.decide_equal.
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

  Ltac simplify :=
    autorewrite with var_db;
      Map.Tactics.vsimpl;
      try (intuition; fail).


  (* Global var_db hints: instantiations of FMap_fun's local qoreo_db hints for Var.Map *)
  #[global] Hint Rewrite Map.Properties.F.add_mapsto_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.empty_mapsto_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.add_in_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.map_o : var_db.
  #[global] Hint Rewrite Map.Properties.F.remove_o : var_db.
  #[global] Hint Rewrite Map.Properties.F.add_o : var_db.
  #[global] Hint Rewrite Map.Properties.F.empty_o : var_db.
  #[global] Hint Rewrite Map.Properties.F.map_in_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.remove_mapsto_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.remove_in_iff : var_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_1 : var_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_2 : var_db.

  #[global] Existing Instance Map.Proofs.singletonProper.
  #[global] Existing Instance Map.Proofs.concatProper.
  #[global] Existing Instance Map.Proofs.domainProper.

  #[global] Hint Rewrite Map.Proofs.concat_find : var_db.
  #[global] Hint Rewrite Map.Proofs.concat_in : var_db.
  #[global] Hint Rewrite @Map.Proofs.map_concat : var_db.
  #[global] Hint Rewrite Map.Proofs.fset_in_union : var_db.
  #[global] Hint Rewrite Map.Proofs.remove_map : var_db.
  #[global] Hint Rewrite Map.Proofs.remove_add : var_db.
  #[global] Hint Rewrite Map.Proofs.remove_empty : var_db.
  #[global] Hint Rewrite @Map.Proofs.map_add : var_db.
  #[global] Hint Resolve @Map.Proofs.empty_map_equal : var_db.
  #[global] Hint Rewrite @Map.Proofs.empty_map_empty : var_db.
  #[global] Hint Rewrite @Map.Proofs.concat_disjoint : var_db.
  #[global] Hint Rewrite Map.Proofs.add_remove_eq : var_db.
  #[global] Hint Rewrite Map.Proofs.add_add_eq : var_db.

  (* separate out more expensive resolves into extra_var_db *)
  #[global] Hint Resolve Map.empty_1 : var_db.  
  #[global] Hint Resolve Map.Properties.Partition_sym : extra_var_db.
  #[global] Hint Resolve @Map.Proofs.singleton_remove : var_db.
  #[global] Hint Resolve Map.Proofs.add_mapsto : extra_var_db.
  #[global] Hint Resolve Map.Proofs.disjoint_empty_1 Map.Proofs.disjoint_empty_2 : var_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_l : var_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_r : var_db.
  #[global] Hint Resolve Map.M.remove_1 : var_db.
  #[global] Hint Resolve Map.Proofs.disjoint_sym : extra_var_db.
  #[global] Hint Resolve Map.Proofs.concat_assoc : extra_var_db.

  #[global] Hint Extern 4 (Map.Partition (Map.concat _ _) _ _) => Map.Proofs.partition_concat : extra_var_db.
  #[global] Hint Extern 4 (Map.Partition _ (Map.concat _ _) _) => Map.Tactics.partition_concat : extra_var_db.
  #[global] Hint Extern 4 (Map.Partition _ _ (Map.concat _ _)) => Map.Tactics.partition_concat : extra_var_db.

  #[global] Hint Rewrite Map.FSetProperties.inter_iff : var_db.
  #[global] Hint Rewrite Map.MProofs.FSetProperties.add_iff: var_db.
  #[global] Hint Rewrite Map.FSetProperties.singleton_iff : var_db.

End Var.

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

  Ltac simplify :=
    autorewrite with actor_db;
    Map.Tactics.vsimpl;
    try (intuition; fail).

(*  #[global] Existing Instance MapProofs.F.EqualSetoid.*)
  
  (* Global actor_db hints: instantiations of FMap_fun's local qoreo_db hints for Actor.Map *)
  #[global] Hint Rewrite Map.Properties.F.add_mapsto_iff : actor_db.
  #[global] Hint Rewrite Map.Properties.F.empty_mapsto_iff : actor_db.
  #[global] Hint Rewrite Map.Properties.F.add_in_iff : actor_db.
  #[global] Hint Rewrite Map.Properties.F.map_o : actor_db.
  #[global] Hint Rewrite Map.Properties.F.remove_o : actor_db.
  #[global] Hint Rewrite Map.Properties.F.add_o : actor_db.
  #[global] Hint Rewrite Map.Properties.F.empty_o : actor_db.
  #[global] Hint Rewrite Map.Properties.F.map_in_iff : actor_db.
  #[global] Hint Rewrite Map.Properties.F.remove_mapsto_iff : actor_db.
  #[global] Hint Resolve Map.empty_1 : actor_db.
  #[global] Hint Resolve Map.Properties.Partition_sym : actor_db.
  #[global] Hint Rewrite Map.Properties.F.remove_in_iff : actor_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_1 : actor_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_2 : actor_db.

  #[global] Existing Instance Map.Proofs.singletonProper.
  #[global] Existing Instance Map.Proofs.concatProper.
  #[global] Existing Instance Map.Proofs.domainProper.

  #[global] Hint Rewrite Map.Proofs.concat_find : actor_db.
  #[global] Hint Rewrite Map.Proofs.concat_in : actor_db.
  #[global] Hint Rewrite @Map.Proofs.map_concat : actor_db.
  #[global] Hint Rewrite Map.Proofs.fset_in_union : actor_db.
  #[global] Hint Rewrite Map.Proofs.remove_map : actor_db.
  #[global] Hint Rewrite Map.Proofs.remove_add : actor_db.
  #[global] Hint Rewrite Map.Proofs.remove_empty : actor_db.
  #[global] Hint Rewrite @Map.Proofs.map_add : actor_db.
  #[global] Hint Resolve @Map.Proofs.empty_map_equal : actor_db.
  #[global] Hint Rewrite @Map.Proofs.empty_map_empty : actor_db.
  #[global] Hint Resolve @Map.Proofs.singleton_remove : actor_db.
  #[global] Hint Rewrite @Map.Proofs.concat_disjoint : actor_db.
  #[global] Hint Rewrite Map.Proofs.add_remove_eq : actor_db.
  #[global] Hint Rewrite Map.Proofs.add_add_eq : actor_db.

  #[global] Hint Resolve Map.Proofs.add_mapsto : actor_db.
  #[global] Hint Resolve Map.Proofs.disjoint_empty_1 Map.Proofs.disjoint_empty_2 : actor_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_l : actor_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_r : actor_db.
  #[global] Hint Resolve Map.M.remove_1 : actor_db.
  #[global] Hint Resolve Map.Proofs.disjoint_sym : actor_db.
  #[global] Hint Resolve Map.Proofs.concat_assoc : actor_db.

  #[global] Hint Extern 4 (Map.Partition (Map.concat _ _) _ _) => Map.Proofs.partition_concat : actor_db.
  #[global] Hint Extern 4 (Map.Partition _ (Map.concat _ _) _) => Map.Tactics.partition_concat : actor_db.
  #[global] Hint Extern 4 (Map.Partition _ _ (Map.concat _ _)) => Map.Tactics.partition_concat : actor_db.

  #[global] Hint Rewrite Map.FSetProperties.inter_iff : actor_db.
  #[global] Hint Rewrite Map.MProofs.FSetProperties.add_iff: actor_db.
  #[global] Hint Rewrite Map.FSetProperties.singleton_iff : actor_db.

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

    Lemma MapsTo_add : forall T A x (tau : T) G,
      ChorEnv.MapsTo A x tau G ->
      ChorEnv.Equal (ChorEnv.add A x tau G)
                    G.
    Proof.
      intros T A x tau G H.
      unfold ChorEnv.Equal.
      unfold Actor.Map.Equiv, ChorEnv.add, ChorEnv.MapsTo, ChorEnv.find in *.
      split; [intros B | intros B a1 a2];
        autorewrite with actor_db var_db in *.
      * split; auto.
        intros [? | ?]; auto; subst.
        apply Actor.Map.Properties.F.in_find_iff.
        destruct (Actor.Map.find B G); try discriminate.
        apply Var.Map.Properties.F.empty_mapsto_iff in H; auto.
      * intros [ [? Hfind] | [? Ha1] ] Hmaps; subst.
        + apply Actor.Map.Properties.F.find_mapsto_iff in Hmaps.
          rewrite Hmaps in *; auto.
          apply Var.Map.Properties.F.find_mapsto_iff in H.
          intros z; autorewrite with var_db.
          Var.Map.Tactics.compare x z; auto.
        + apply Actor.Map.Properties.F.find_mapsto_iff in Hmaps.
          apply Actor.Map.Properties.F.find_mapsto_iff in Ha1.
          rewrite Hmaps in Ha1.
          inversion Ha1; subst; reflexivity.
    Qed.



    Lemma find_add : forall T A B x (a : T) G,
      Var.Map.Equal
        (ChorEnv.find A (ChorEnv.add B x a G))
        (if Actor.eq_dec A B then Var.Map.add x a (ChorEnv.find A G) else ChorEnv.find A G).
    Proof.
      intros.
      unfold ChorEnv.add, ChorEnv.find.
      autorewrite with actor_db.
      repeat Actor.Map.Tactics.reduce_eq_dec.
      + destruct (Actor.Map.find B G); try reflexivity.
      + destruct (Actor.Map.find B G); try reflexivity.
    Qed.
    #[global] Hint Rewrite find_add : var_db.
End ChorEnv.