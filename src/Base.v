From Stdlib Require FSets.FMapList FSets.FSetList 
                            FSets.FMapFacts
                            FSets.FMapInterface
                            OrderedType OrderedTypeEx.
From QuantumLib Require Import Matrix Pad Quantum.
From Stdlib Require Import String Morphisms (* for Proper *).
Require Import Setoid. (* for setoid_replace with *)

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

  Definition setminus {T} (S : FSet.t) (N : M.t T) : M.t T :=
    FSet.fold (fun x N' => M.remove x N') S N.

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

    #[local] Existing Instance FSetProperties.Equal_ST.
    Ltac compare x y :=
      let Heq := fresh "Heq" in
      destruct (E.eq_dec x y) as [Heq | Heq];
        [try (rewrite <- Heq in *; clear y Heq) | ];
        try contradiction;
        repeat match goal with
        | [ H : ~ E.eq ?x ?x |- _ ] => contradict H; reflexivity
        | [ H : E.eq ?x ?x   |- _ ] => clear H
        | [ H1 : ~ E.eq ?x ?y, H2 : ~ E.eq ?x ?y |- _ ] => clear H2
        | [ H1 : ~ E.eq ?x ?y, H2 : ~ E.eq ?y ?x |- _ ] => clear H2
        end.

    Ltac reduce_eq_dec :=
      match goal with
      | [ |- context[E.eq_dec ?x ?y] ] => compare x y
      | [ H : context[E.eq_dec ?x ?y] |- _ ] => compare x y
      end.


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

    (* remove *)

    Lemma remove_remove : forall T A (m : t T),
      Equal
        (M.remove A (M.remove A m))
        (M.remove A m).
    Proof.
      intros T A m B.
      autorewrite with qoreo_db.
      compare A B; auto.
    Qed.

    (** Domain *)
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

    Lemma domain_Empty : forall A (m : t A),
      M.Empty m ->
      FSet.Equal (domain m) FSet.empty.
    Proof.
      intros.
      unfold domain.
      apply fold_Empty; auto with qoreo_db.
      { apply FSetProperties.Equal_ST. }
    Qed.
    Lemma Add_add : forall A x (a : A) m m',
      Add x a m m' <-> Equal m' (M.add x a m).
    Proof.
      intros. unfold Add. split; auto.
    Qed.
    #[local] Hint Rewrite Add_add : qoreo_db.


    Lemma domain_add' :  forall A x (a : A) m,
      FSet.Equal (domain (M.add x a m))
                (FSet.add x (domain (M.remove x m))).
    Proof.
      intros.

      setoid_replace (add x a m) with (add x a (remove x m)).
        2:{
          intros z. autorewrite with qoreo_db.
          compare x z; auto.
        }
      unfold domain.
        rewrite fold_add.
        + reflexivity.
        + apply FSetProperties.Equal_ST.
        + clear x a m.
          intros x1 x2 Hx a1 a2 Ha X1 X2 HX.
          rewrite HX. rewrite Hx.
          reflexivity.
        + intros k k' ? ? X Heq.
          intros z.
          repeat rewrite FSetProperties.add_iff.
          intuition.
        + apply remove_1; auto. reflexivity.
    Qed.
    (* #[local] Hint Rewrite domain_add' : qoreo_db.*)



    Lemma domain_remove : forall A m x,
      FSet.Equal (domain (remove x m)) (FSet.remove x (@domain A m)).
    Proof.
      intros A m x z.
      rewrite FSetProperties.remove_iff.
      
      induction m using map_induction.
      * rewrite (domain_Empty _ m); auto.
        rewrite (domain_Empty _ (remove x m)).
        2:{
          unfold Empty in *.
          intros y b Hmaps.
          apply remove_3 in Hmaps.
          apply H in Hmaps; contradiction.
        }
        split; [intros Hin; split | intros [Hin Heq]];
          auto.
        apply FSetProperties.empty_iff in Hin. contradiction.

      * rewrite Add_add in H0.
        rewrite H0; clear m2 H0.
        compare x x0.
        + (* if equal *)
          setoid_replace (remove x (add x e m1))
            with (remove x m1).
          2:{
            intros w. autorewrite with qoreo_db.
            compare x w; auto.
          }
          rewrite IHm1.
          destruct IHm1 as [IHm1 IHm2].
          rewrite domain_add'.
          rewrite FSetProperties.add_iff.
          split; intros [Hin Hneq]; split; auto.
          {
            destruct Hin as [ | Hin]; try contradiction.
            apply IHm1 in Hin.
            destruct Hin as [Hin _ ].
            auto.
          }

        + (* if not equal *)
          setoid_replace (remove x (add x0 e m1))
            with (add x0 e (remove x m1)).
          2:{
            intros w. autorewrite with qoreo_db.
            compare x w; auto. compare x0 w; auto.
          }
          repeat rewrite domain_add'.
          repeat rewrite FSetProperties.add_iff.
          setoid_replace (remove x0 (remove x m1))
            with (remove x (remove x0 m1)).
          2:{
            intros w. autorewrite with qoreo_db.
            compare x0 w; auto.
            compare x w; auto.
          }
          setoid_replace (remove x0 m1)
            with m1.
          2:{
            intros w. autorewrite with qoreo_db.
            compare x0 w; auto.
            (* ~ In w m1 *)
            apply F.not_find_in_iff in H; auto.
          }
          rewrite IHm1.
          split; intros H0.
          {
            destruct H0 as [H0 |[Hin Hneq]]; auto.
            { 
              rewrite H0 in *; clear x0 H0.
              split; auto. left; reflexivity.
            }
          }
          {
            destruct H0 as [H0 Hneq].
            tauto.
          }
    Qed.

    Lemma domain_add :  forall A x (a : A) m,
      FSet.Equal (domain (M.add x a m))
                (FSet.add x (domain m)).
    Proof.
      intros.
      rewrite domain_add'.
      rewrite domain_remove.
      intros z.
      repeat rewrite FSetProperties.add_iff.
      rewrite FSetProperties.remove_iff.
      compare x z; auto with *; intuition.
    Qed.
    
    Lemma domain_In : forall A x (m : t A),
      FSet.In x (domain m) <-> M.In x m.
    Proof.
      intros A x m.
      induction m using map_induction.
      * rewrite domain_Empty; auto.
        rewrite FSetProperties.empty_iff.
        split; [inversion 1 | intros [a Hmaps]].
        apply H in Hmaps.
        contradiction.

      * rewrite Add_add in H0.
        rewrite H0; clear m2 H0.
        rewrite domain_add.
        rewrite FSetProperties.add_iff.
        autorewrite with qoreo_db.
        rewrite IHm1.
        reflexivity.
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

    Lemma remove_swap : forall A x y (m : M.t A),
      M.Equal (M.remove x (M.remove y m))
              (M.remove y (M.remove x m)).
    Proof.
      intros A x y m z.
      autorewrite with qoreo_db.
      repeat reduce_eq_dec; auto.
    Qed.

    Lemma add_remove_eq : forall A x (a : A) m,
      M.Equal (M.add x a (M.remove x m))
                    (M.add x a m).
    Proof.
      intros.
      intros z.
      autorewrite with qoreo_db.
      compare x z; auto.
    Qed.
    #[local] Hint Rewrite add_remove_eq : qoreo_db.

    Lemma add_mapsto : forall A x (a : A) m,
      M.MapsTo x a m ->
      M.Equal (M.add x a m)
                    m.
    Proof.
      intros.
      intros z.
      autorewrite with qoreo_db.
      compare x z; auto.
      apply F.find_mapsto_iff in H; auto.
    Qed.
    #[local] Hint Resolve add_mapsto : var_db.


    Lemma add_neq_sym : forall A x y (a b : A) m,
    (*x <> y ->*)
    ~ E.eq x y ->
    M.Equal (M.add x a (M.add y b m))
            (M.add y b (M.add x a m)).
    Proof.
      intros.
      intros z.
      autorewrite with qoreo_db.
      repeat reduce_eq_dec; auto.
    Qed.

    Lemma add_add_eq : forall A x (a b : A) m,
      M.Equal 
        (M.add x a (M.add x b m))
        (M.add x a m).
    Proof.
      intros.
      intros z.
      autorewrite with qoreo_db.
      repeat reduce_eq_dec; auto.
    Qed.

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
    Proof.
      intros.
      intros Hempty.
      unfold Empty in Hempty.
      apply (Hempty x a).
      apply add_1. reflexivity.
    Qed.

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


    Lemma singleton_empty : forall A x a,
      Singleton x a (M.empty A)
      <-> False.
    Proof.
      intros. unfold Singleton.
      split; intros H; try contradiction.
      specialize (H x).
      autorewrite with qoreo_db in H.
      compare x x; try discriminate.
    Qed.


    (* not quite true because m might be (M.add y b' empty)...
      also I'm having trouble with the x=y conclusion.
    *)
    Lemma singleton_add_inversion : forall A x (a : A) y b m,
      Singleton x a (M.add y b m) ->
      E.eq x y /\ a = b /\ M.Empty (M.remove y m).
    Proof.
      intros ? ? ? ? ? ? Hsing.
      unfold Singleton in Hsing.
      compare x y.
      2:{
        specialize (Hsing y). autorewrite with qoreo_db in Hsing.
        repeat reduce_eq_dec.
        discriminate.
      }
      split; try reflexivity.
      split.
      { (* a = b *)
        specialize (Hsing x).
        autorewrite with qoreo_db in Hsing.
        repeat reduce_eq_dec.
        inversion Hsing; auto.
      }
      (* Empty *)
      intros z c.
      specialize (Hsing z).
      intros Hmapsto; apply F.find_mapsto_iff in Hmapsto.
      autorewrite with qoreo_db in *.
      reduce_eq_dec; [discriminate | ].
      rewrite Hsing in Hmapsto; discriminate.
    Qed.

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

    Lemma Empty_concat : forall A (m1 m2 : M.t A),
      M.Empty (concat m1 m2) <-> M.Empty m1 /\ M.Empty m2.
    Proof.
      intros A m1 m2.
      split; intros Hempty.
      * apply empty_map_equal in Hempty.
        split; intros z a HMapsTo;
        apply F.find_mapsto_iff in HMapsTo. 
        + specialize (Hempty z);
          autorewrite with qoreo_db in *;
          rewrite HMapsTo in Hempty.
          discriminate.
        + specialize (Hempty z).
          autorewrite with qoreo_db in *.
          rewrite HMapsTo in Hempty.
          destruct (find z m1); discriminate.
      * destruct Hempty as [H1 H2];
        apply empty_map_equal in H1;
        apply empty_map_equal in H2.
        intros z a HMapsTo.
        apply F.find_mapsto_iff in HMapsTo.
        specialize (H1 z).
        specialize (H2 z).
        autorewrite with qoreo_db in *.
        rewrite H1 in *.
        rewrite H2 in *.
        discriminate. 
    Qed.


    Lemma Empty_find : forall A (m : t A),
      M.Empty m <-> forall z, M.find z m = None.
    Proof.
      intros A m. unfold Empty.
      split; intros Hin.
      * intros z.
        apply F.not_find_in_iff.
        intros [a Ha].
        apply Hin in Ha; auto.
      * intros z a Hmaps.
        specialize (Hin z).
        apply F.not_find_in_iff in Hin.
        apply Hin. exists a; auto.
    Qed.

    Ltac simpl_Empty :=
        match goal with
        | [ H : M.Empty (M.add _ _ _) |- _ ] =>
          exfalso; apply (add_not_Empty _ _ _ _ H)
        | [ H : M.Empty (M.map _ _) |- _ ] =>
          apply empty_map_Empty in H
        | [ |- M.Empty (M.map _ _) ] =>
          apply empty_map_Empty
        | [ |- Empty (empty _) ] => apply M.empty_1
        | [ H : M.Empty (concat _ _) |- _ ] =>
          rewrite <- Empty_concat in H; destruct H
        | [ |- M.Empty (concat _ _) ] =>
          rewrite Empty_concat

        (* Replace any remaining instances of Empty m with m == empty
        and substitute *)
        | [ H : M.Empty ?m |- _ ] =>
          apply empty_map_equal in H;
          subst_map
        end.

    Lemma Singleton_concat : forall A x (a : A) m1 m2,
      Singleton x a (concat m1 m2) ->
      Singleton x a m1 \/ (Empty m1 /\ Singleton x a m2).
    Proof.
      intros ? ? ? ? ? Hsing.
      destruct (find x m1) as [a' | ] eqn:Hfind.
      * (* if x occurs in m1 *)
        left.
        unfold Singleton in *.
        intros z.
        specialize (Hsing z).
        autorewrite with qoreo_db in *.
        compare x z.
        + rewrite Heq in *.
          rewrite Hfind in Hsing.
          inversion Hsing; subst; auto.
        + destruct (find z m1); auto; discriminate.
      * (* x not in m1 *)
        right.
        split.
        + intros z b Hmapsto.
          apply F.find_mapsto_iff in Hmapsto.
          specialize (Hsing z).
          autorewrite with qoreo_db in *.
          rewrite Hmapsto in Hsing.
          compare x z; inversion Hsing; subst; clear Hsing.
          rewrite Hfind in *; discriminate.
        + intros z.
          compare x z.
          - (* x = z *) 
            specialize (Hsing x).
            autorewrite with qoreo_db in *.
            rewrite Hfind in Hsing; auto.
          - (* x <> z *)
            autorewrite with qoreo_db in *.
            compare x z.
            specialize (Hsing z).
            autorewrite with qoreo_db in Hsing.
            reduce_eq_dec.
            destruct (find z m1); try discriminate; auto.
    Qed.

    Lemma Singleton_map : forall A B x (b : B) (f : A -> B) m,
      Singleton x b (map f m) <->
      exists a, f a = b /\ Singleton x a m.
    Proof.
      intros. unfold Singleton.
      split.
      * intros Heq.
        specialize (Heq x) as Hx.
        autorewrite with qoreo_db in Hx; reduce_eq_dec.
        destruct (find x m) as [a | ] eqn:Hfind;
          simpl in Heq; inversion Hx; subst; clear Hx.
          
        exists a. split; auto.
        intros z. specialize (Heq z).
        autorewrite with qoreo_db in *.
        reduce_eq_dec; auto.
        destruct (find z m); auto; discriminate.
      * intros [a [Ha Hm]]. subst.
        rewrite Hm.
        autorewrite with qoreo_db.
        reflexivity.
    Qed.

    Ltac simpl_Singleton :=
      match goal with
      | [ H : Singleton _ _ (M.add _ _ _) |- _ ] =>
        apply singleton_add_inversion in H;
        destruct H as [? [? ?]]; subst
      | [ |- Singleton ?x _ (M.add ?a _ (M.empty _)) ] =>
        apply singleton_singleton
      | [ H : Singleton _ _ (empty _) |- _ ] =>
        rewrite singleton_empty in H; contradiction
      | [ H : Singleton _ _ (concat _ _) |- _ ] =>
        apply Singleton_concat in H
      | [ H : Singleton _ _ (map _ _) |- _ ] =>
        rewrite Singleton_map in H;
        destruct H as [? [? ?]]

      (* Replace any remaining instances of Singleton with its definition *)
      | [ H : Singleton _ _ _ |- _ ] => unfold Singleton in *; subst_map
      | [ |- Singleton _ _ _ ] => unfold Singleton in *; subst_map
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
    Proof.
      intros.
      unfold Disjoint in *.
      intros z.
      rewrite F.remove_in_iff.
      intros [[Hneq Hin1] Hin2].
      apply (H z); auto.
    Qed.

    Lemma disjoint_remove_2 : forall {A} (m1 m2 : M.t A) x,
      Disjoint m1 m2 ->
      Disjoint m1 (M.remove x m2).
    Proof.
      intros.
      apply disjoint_sym. apply disjoint_remove_1.
      apply disjoint_sym. auto.
    Qed.

    Lemma disjoint_in_l : forall {A} (m1 m2 : M.t A) x,
      Disjoint m1 m2 ->
      M.In x m1 ->
      ~ M.In x m2.
    Proof.
      intros A m1 m2 x Hdisj Hin1 Hin2.
      apply (Hdisj x); auto.
    Qed.
    #[local] Hint Resolve disjoint_in_l : qoreo_db.

    Lemma disjoint_in_r : forall {A} (m1 m2 : M.t A) x,
      Disjoint m1 m2 ->
      M.In x m2 ->
      ~ M.In x m1.
    Proof.
      intros A m1 m2 x Hdisj Hin2 Hin1.
      apply (Hdisj x); auto.
    Qed.
    #[local] Hint Resolve disjoint_in_r : qoreo_db.


    Lemma disjoint_add_1 : forall A m1 m2 x (a : A),
      Disjoint (M.add x a m1) m2 <-> Disjoint m1 m2 /\ ~ M.In x m2.
    Proof.
      intros.
      split; intros Hdisj; try split.
      * intros z [Hin1 Hin2].
        apply (Hdisj z). split; auto.
        autorewrite with qoreo_db.
        auto.
      * intros Hin2.
        apply (Hdisj x).
        split; auto.
        autorewrite with qoreo_db.
        left; reflexivity.

      * destruct Hdisj as [Hdisj Hin].
        intros z [Hin1 Hin2].
        autorewrite with qoreo_db in Hin1.
        destruct Hin1 as [Heq | Hin1].
        { rewrite Heq in Hin; contradiction. }
        { apply (Hdisj z); auto. }
    Qed.
    Lemma disjoint_add_2 : forall A m1 m2 x (a : A),
      Disjoint m1 (M.add x a m2) <-> Disjoint m1 m2 /\ ~ M.In x m1.
    Proof.
      intros.
      split; [intros Hdisj | intros [Hdisj Hin]];
        apply disjoint_sym in Hdisj.
      {
        apply disjoint_add_1 in Hdisj.
        destruct Hdisj; split; auto.
        apply disjoint_sym; auto.
      }
      {
        apply disjoint_sym.
        apply disjoint_add_1.
        auto.
      }
    Qed.

    Ltac reduce_disjoint :=
    match goal with
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

    Lemma concat_add_l : forall A x (a : A) m1 m2,
      M.Equal (concat (M.add x a m1) m2)
              (M.add x a (concat m1 m2)).
    Proof.
      intros A x a m1 m2 z.
      autorewrite with qoreo_db.
      reduce_eq_dec; auto.
    Qed.
    #[local] Hint Rewrite @concat_add_l : qoreo_db.

    Lemma concat_add_r : forall A x (a : A) m1 m2,
      ~ M.In x m1 ->
      M.Equal (concat m1 (M.add x a m2))
              (M.add x a (concat m1 m2)).
    Proof.
      intros A x a m1 m2 Hin z.
      autorewrite with qoreo_db.
      compare x z.
      - apply F.not_find_in_iff in Hin. rewrite Hin; auto.
      - auto.
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
    Proof.
      intros ? ? ? [Hdisj Hmapsto].
      intros z.
      autorewrite with qoreo_db.
      destruct (find z Δ1) eqn:Hfind; auto.
      exfalso.
      absurd (MapsTo z a (empty A)).
      { autorewrite with qoreo_db. auto. }
      {
        apply Hmapsto.
        left.
        apply F.find_mapsto_iff; auto.
      }
    Qed.

    Lemma partition_empty_inv2 : forall {A} (Δ1 Δ2 : M.t A),
      Partition (M.empty _) Δ1 Δ2 ->
      M.Equal Δ2 (M.empty _).
    Proof.
      intros ? ? ? Hpart.
      apply Properties.Partition_sym in Hpart.
      apply partition_empty_inv1 in Hpart; auto.
    Qed.

    (* Only true in both directions if f is injective *)
    Lemma partition_map : forall A B (f : A -> B) m m1 m2,
      Partition m m1 m2 ->
      Partition (M.map f m) (M.map f m1) (M.map f m2).
    Proof.
      intros ? ? ? ? ? ? Hpart.
      reflect_partition.
      + apply disjoint_map; auto.
      + intros z. autorewrite with qoreo_db.
        destruct (find z m1) as [a | ] eqn:Hfind1;
          simpl; auto. 
    Qed.

    Lemma map_partition : forall A B (f : A -> B) m m1 m2,
      (forall x y, f x = f y -> x = y) ->
      Partition (M.map f m) (M.map f m1) (M.map f m2) ->
      Partition m m1 m2.
    Proof.
        intros ? ? ? ? ? ? Hinj Hpart.
        reflect_partition; apply disjoint_map in Hdisj; auto.
        intros z.
        specialize (Heq z).
        autorewrite with qoreo_db in *.
        destruct (find z m1) eqn:Hfind1.
        {
          destruct (find z m); simpl in Heq;
            inversion Heq; auto.
          apply Hinj in H0; subst; auto.
        }
        simpl in Heq.
        destruct (find z m); destruct (find z m2);
          auto;
          inversion Heq.
        apply Hinj in H0; subst; auto.
    Qed.

    Lemma partition_empty1_eq : forall A m m0,
        Partition m (M.empty A) m0 ->
        M.Equal m m0.
    Proof.
      intros ? ? ? Hpart.
      reflect_partition.
      intros z. autorewrite with qoreo_db.
      auto.
    Qed.

    Lemma partition_empty2_eq : forall A m m0,
        Partition m m0 (M.empty A) ->
        M.Equal m m0.
    Proof.
      intros ? ? ? Hpart.
      reflect_partition.
      intros z. autorewrite with qoreo_db.
      destruct (find z m0); auto.
    Qed.

    #[local] Hint Rewrite F.remove_in_iff : qoreo_db.
    #[local] Hint Rewrite F.remove_mapsto_iff : qoreo_db.

    Lemma partition_add_inversion : forall A (a : A) x m m1 m2,
      Partition (M.add x a m) m1 m2 ->
      ~ M.In x m ->
      (M.MapsTo x a m1 /\ ~ M.In x m2 /\ Partition m (M.remove x m1) m2)
      \/
      (~ M.In x m1 /\ M.MapsTo x a m2 /\ Partition m m1 (M.remove x m2)).
    Proof.
      intros ? ? ? ? ? ? Hpart Hin.
      assert (Hfind : (find x m1 = Some a /\ find x m2 = None) \/ 
                      (find x m1 = None   /\ find x m2 = Some a)).
      {
        reflect_partition.
        specialize (Heq x). autorewrite with qoreo_db in Heq.
        reduce_eq_dec.
        destruct (find x m1) as [b | ] eqn:Hfind1.
        + left. inversion Heq; subst; clear Heq. split; auto.
          destruct (find x m2) as [? | ] eqn:Hfind2; auto.
          (* contradiction *)
          exfalso. apply (Hdisj x). 
          repeat rewrite F.in_find_iff.
          rewrite Hfind1, Hfind2.
          split; discriminate.
        + right. auto.
      }

      apply (partition_remove x) in Hpart.
      rewrite remove_add in Hpart.
      reduce_eq_dec.
      rewrite (remove_not_in _ x m) in Hpart; auto.
      
      destruct Hfind as [[Hfind1 Hfind2] | [Hfind1 Hfind2]].
      + apply F.find_mapsto_iff in Hfind1.
        apply F.not_find_in_iff in Hfind2.
        left. split; auto. split; auto.
        rewrite (remove_not_in _ x m2) in Hpart; auto.
      + apply F.find_mapsto_iff in Hfind2.
        apply F.not_find_in_iff in Hfind1.
        right. split; auto. split; auto.
        rewrite (remove_not_in _ x m1) in Hpart; auto.
    Qed.


    Lemma partition_not_in_inversion : forall A (m m1 m2 : M.t A) x,
      Partition m m1 m2 ->
      ~ M.In x m <->
      ~ M.In x m1 /\ ~ M.In x m2.
    Proof.
      intros ? ? ? ? ? Hpart.
      reflect_partition.
      autorewrite with qoreo_db.
      intuition.
    Qed.


    (* move m to the left-most element of the concatenation list *)
    Ltac reduce_concat :=
      repeat match goal with
      | [ |- M.Equal (concat ?m _) (concat ?m _)] =>
        apply concatProper; try reflexivity
      | [ |- M.Equal (concat ?m _) (concat ?m0 ?m1)] =>
        rewrite (concat_sym m0 m1);
          [ | auto with var_db ];
        repeat rewrite <- concat_assoc
      end.

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
        (*
        | [ H : Partition (M.add _ _ _) _ _ |- _ ] =>
          apply partition_add_inversion in H; auto;
          try destruct H as [[? [? ?]] | [? [? ?]]]
        *)

        (* Partitions with remove *)
        | [ |- Partition (M.remove ?x _) (M.remove ?x _) (M.remove ?x _) ] =>
          apply partition_remove

        (* Partitions with map *)
        | [ |- Partition (M.map ?f _) (M.map ?f _) (M.map ?f _) ] =>
          apply partition_map
        (*
        | [ H : Partition (M.map ?f _) (M.map ?f _) (M.map ?f _) |- _ ] =>
          apply map_partition in H
          
          *)
        (*
        | [H : Partition (M.map ?f ?m) ?n1 ?n2 |- _] =>
          let m1 := fresh "m1" in
          let m2 := fresh "m2" in
          let Heq1 := fresh "Heq1" in
          let Heq2 := fresh "Heq2" in
          destruct (partition_map_inv _ _ _ _ _ _ H)
            as [m1 [m2 [Heq1 [Heq2 Hpart]]]]; auto;
          subst_map; try rewrite Heq1, Heq2 in *; try clear n1 Heq1 n2 Heq2
          *)


        (*
        (* ~In inversion *)
        | [ Hpart : Partition ?m ?m1 ?m2,
            Hin : ~ M.In ?x ?m |- _ ] =>
          let Hin' := fresh "Hin" in
          assert (Hin' : ~ M.In x m1 /\ ~ M.In x m2)
          by (eapply partition_not_in_inversion; eauto);
          destruct Hin';
          reduce_concat
        *)

        (* Partition with concat *)

        | [ |- Partition (concat ?m1 ?m2) ?m1 _ ] =>
          reflect_partition;
            [ | reflexivity];
          reduce_concat

        | [ |- Partition (concat ?m1 ?m2) ?m2 _ ] =>
          reflect_partition;
            [ | rewrite (concat_sym m1 m2); auto;
                try reflexivity];
          reduce_concat

        | [ |- Partition _ (concat _ _) _ ] =>
          reflect_partition; reduce_concat
        | [ |- Partition _ _ (concat _ _) ] =>
          reflect_partition; reduce_concat
      end.



    (* reflect_find db: normalizes In/MapsTo hypotheses to find-based form,
      then reduces the goal using autorewrite with db in * + reduce_eq_dec.
      fmap_decide_with db: calls reflect_find then closes with tauto/auto. *)
    Ltac reflect_find_body :=
      match goal with
      | [ H : M.In ?x ?m |- _ ] =>
        let v := fresh "v" in
        destruct H as [v H]; fold (M.MapsTo x v m) in H
      | [ H : M.MapsTo _ _ _ |- _ ] =>
        apply F.find_mapsto_iff in H;
        try rewrite H in *
      | [ H : ~ M.In ?x (concat ?m1 ?m2) |- _ ] =>
        rewrite concat_in in H
      | [ H : ~ (?P \/ ?Q) |- _ ] =>
        let Hl := fresh in let Hr := fresh in
        assert (Hl : ~P) by tauto;
        assert (Hr : ~Q) by tauto;
        clear H
      | [ H : ~ M.In ?x ?m |- _ ] =>
        apply F.not_find_in_iff in H;
        try rewrite H in *
      | [ H : Disjoint _ |- _ ] => unfold Disjoint in H
      | [ H : M.Empty _ |- _ ] => apply Empty_find in H


      | [ |- M.Equal _ _ ] => let z := fresh "z" in intro z
      | [ |- Disjoint _ _ ] => let z := fresh "z" in intro z
      | [ |- M.In _ _ ] => apply F.in_find_iff
      | [ |- ~ M.In _ _ ] => apply F.not_find_in_iff
      | [ |- M.MapsTo _ _ _ ] => apply F.find_mapsto_iff
      | [ |- M.Empty _ ] =>
        let z := fresh "z" in 
        apply Empty_find; intros z
      
      | [ H : M.find ?x ?m = _ |- context[M.find ?x ?m] ] => rewrite H
      end.

    (* instantiate this for each relevant hint database *)
    Ltac reflect_find :=
      repeat (
        reflect_find_body;
        autorewrite with qoreo_db in *;
        repeat reduce_eq_dec
      ).
    Ltac solve := 
      reflect_find; first [tauto | auto; fail].

    Ltac vsimpl :=
    repeat match goal with

    | [ H : ~ (?P \/ ?Q) |- _ ] =>
        let Hl := fresh in let Hr := fresh in
        assert (Hl : ~P) by tauto;
        assert (Hr : ~Q) by tauto;
        clear H
    | [ |- ~ (_ \/ _) ] =>
      apply Classical_Prop.and_not_or
    | [ H : _ /\ _ |- _ ] =>
      destruct H

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

    | [ H : Properties.Add ?x ?a ?m ?m' |- _ ] =>
      let Heq := fresh "Heq" in
      assert (Heq : M.Equal m'
              (M.add x a m))
        by auto;
      clear H;
      subst_map

    | [ H : M.Equal _ _ |- _ ] => subst_map
    end.

  End Proofs.

  Module FSetProofs.
    Fixpoint fset_of_elems (ls : list E.t) : FSet.t :=
      match ls with
      | [] => FSet.empty
      | A :: ls' => FSet.add A (fset_of_elems ls')
      end.

    Lemma fset_of_elems_Empty : forall ls1,
      FSet.Empty (fset_of_elems ls1) ->
      ls1 = [].
    Proof.
      induction ls1; intros Hempty; auto.
      {
        exfalso. simpl in Hempty.
        apply (Hempty a).
        apply FSet.add_1. reflexivity.
      }
    Qed.
    Lemma elements_empty :
      FSet.elements FSet.empty = [].
    Proof.
      destruct (FSet.elements FSet.empty) as [ | x ls] eqn:Hls; auto.
      exfalso.
      set (H := FSetProperties.elements_iff FSet.empty x).
      rewrite <- (FSetProperties.empty_iff x).
      rewrite FSetProperties.elements_iff.
      rewrite Hls.
      constructor.
      reflexivity.
    Qed.

    (* relies on being a list implementation of fset *)
    Lemma fset_reflect : forall (X : FSet.t),
      FSet.Equal X (fset_of_elems (FSet.elements X)).
    Proof.
      intros X z.
      rewrite FSetProperties.elements_iff at 1.
      remember (FSet.elements X) as ls eqn:Hls.
      clear X Hls.

      induction ls as [ | x ls]; simpl.
      { rewrite FSetProperties.elements_iff. rewrite elements_empty. reflexivity. }
      rewrite FSetProperties.add_iff.
      rewrite <- IHls.
      split.
      * intros Hin. inversion Hin; subst; clear Hin.
        { left. symmetry. auto. }
        { right. auto. }
      * intros [Heq | Hin].
        { apply SetoidList.InA_cons_hd. symmetry. auto. }
        { apply SetoidList.InA_cons_tl. auto. }
    Qed.

    Global Instance elements_Proper : Proper (FSet.Equal ==> SetoidList.equivlistA E.eq) FSet.elements.
    Proof.
      intros X1 X2 HX.
      unfold FSet.Equal in HX.
      {
        intros a. specialize (HX a).
        repeat rewrite FSetProperties.elements_iff in HX.
        auto.
      }
    Qed.
    Global Instance removeA_Proper :
      Proper (E.eq ==> SetoidList.equivlistA E.eq ==> SetoidList.equivlistA E.eq)
        (SetoidList.removeA E.eq_dec).
    Proof.
      intros A1 A2 HA ls1 ls2 Hls z.
      repeat rewrite SetoidList.removeA_InA.
      rewrite HA.
      rewrite Hls.
      reflexivity.
      all: apply FSetProperties.E_ST.
    Qed.

  Lemma elements_discriminate : forall X1 X2 A ls2,
      SetoidList.eqlistA E.eq (FSet.elements X1) [] ->
      SetoidList.eqlistA E.eq (FSet.elements X2) (A :: ls2) ->
      ~ FSet.Equal X1 X2.
  Proof.
    intros X1 X2 A ls2 H1 H2 HX.
      apply elements_Proper in HX.
      rewrite H1 in HX.
      rewrite H2 in HX.
      unfold SetoidList.equivlistA in HX.
      absurd (SetoidList.InA E.eq A []).
      { inversion 1. }
      rewrite HX. constructor. reflexivity.
  Qed.


    Lemma elements_cons_in : forall X B ls,
      FSet.elements X = B :: ls ->
      ~ List.In B ls.
    Proof.
      intros X B ls H.
      set (Hnodup := FSet.elements_3w X).
      rewrite H in Hnodup.
      inversion Hnodup; subst; auto.
      intros Hin. apply H2.
      apply SetoidList.InA_alt.
      exists B. split; auto. reflexivity.
    Qed.

    Lemma fset_of_elems_In_iff : forall ls A,
      FSet.In A (fset_of_elems ls) <-> SetoidList.InA E.eq A ls.
    Proof.
      induction ls as [ | B ls]; intros A; simpl.
      * rewrite FSetProperties.elements_iff.
        rewrite elements_empty.
        reflexivity.
      * rewrite FSetProperties.add_iff.
        rewrite SetoidList.InA_cons.
        rewrite IHls.
        intuition.
    Qed.
    
    Lemma remove_fset_of_elems : forall ls B,
      FSet.Equal (FSet.remove B (fset_of_elems ls))
                 (fset_of_elems (SetoidList.removeA E.eq_dec B ls)).
    Proof.
      intros ls B A.
      rewrite FSetProperties.remove_iff.
      repeat rewrite fset_of_elems_In_iff.
      rewrite SetoidList.removeA_InA.
      reflexivity.
      apply FSetProperties.E_ST.
    Qed.

    Lemma elements_cons_remove : forall X B ls,
      ~ SetoidList.InA E.eq B ls ->
      SetoidList.equivlistA E.eq (FSet.elements X) (B :: ls) ->
      SetoidList.equivlistA E.eq (FSet.elements (FSet.remove B X)) ls.
    Proof.
      intros X B ls Hin H A.
      rewrite <- FSetProperties.elements_iff.
      rewrite FSetProperties.remove_iff.
      set (HA := H A).
      rewrite SetoidList.InA_cons in HA.
      rewrite <- FSetProperties.elements_iff in HA.
      rewrite HA.
      split.
      * intros [[Heq | ?] Hneq]; auto.
        { exfalso. apply Hneq. symmetry. auto. }
      * intros HinA.
        Proofs.compare A B.
        split.
        2:{ intros Heq'; apply Heq; symmetry; auto. }
        right. auto. 
    Qed.

    Module E_facts := OrderedType.OrderedTypeFacts E.

    #[local] Instance ltProper : Proper (E.eq ==> E.eq ==> iff) E.lt.
      apply E_facts.lt_compat.
    Qed.
    Lemma ltStrict : StrictOrder E.lt.
    Proof.
      apply E_facts.lt_strorder.
    Qed.

    Lemma elements_Proper' : forall X1 X2,
      FSet.Equal X1 X2 ->
      SetoidList.eqlistA E.eq (FSet.elements X1) (FSet.elements X2).
    Proof.
      intros.
      assert (Sorted.Sorted E.lt (FSet.elements X1)).
      { apply FSet.elements_3. }
      assert (Sorted.Sorted E.lt (FSet.elements X2)).
      { apply FSet.elements_3. }
      assert (Equivalence E.eq).
      { apply FSetProperties.E_ST. }
      assert (StrictOrder E.lt).
      { apply ltStrict. } 
      eapply SetoidList.SortA_equivlistA_eqlistA; eauto.
      2:{ apply elements_Proper; auto. }
      { apply ltProper. }
    Qed.
  

    Lemma in_dec : forall x X, 
      { FSet.In x X } + { ~ FSet.In x X }.
    Proof.
      intros x X. remember (FSet.elements X) as ls eqn:Hls.
      assert (Hdup : SetoidList.NoDupA E.eq ls).
      { rewrite Hls. apply FSet.elements_3w. }
      assert (Hls' : SetoidList.equivlistA E.eq ls (FSet.elements X)).
      { rewrite Hls. reflexivity. }
      clear Hls.
      revert X Hls' Hdup.
      induction ls as [ | B ls]; intros X Hls Hdup.
      * right.
        rewrite FSetProperties.elements_iff.
        rewrite <- Hls. inversion 1.
      * destruct (IHls (FSet.remove B X)) as [Hin | Hin]; auto.
        2:{ inversion Hdup; auto. }
        { erewrite elements_cons_remove; [ reflexivity | | symmetry; auto ].
          inversion Hdup; subst; auto.
        }
        {
          rewrite FSetProperties.remove_iff in Hin.
          destruct Hin.
          left. auto.
        }
        rewrite FSetProperties.remove_iff in Hin.
        Proofs.compare x B.
        {
          left. rewrite Heq.
          rewrite FSetProperties.elements_iff.
          rewrite <- Hls. constructor; auto.
          reflexivity.
        }
        right. intros Hin'. apply Hin. split; auto.
        intros Heq'. apply Heq. symmetry. auto.
    Qed.


    (** setminus *)


    Lemma foldProper'' : forall ls1 ls2,
      SetoidList.eqlistA E.eq ls1 ls2 ->

      forall  T f (b1 b2 : M.t T),
      Equal b1 b2 ->
      Proper (Equal ==> E.eq ==> Equal) f ->

      M.Equal (fold_left f ls1 b1)
              (fold_left f ls2 b2).
    Proof.
      
      intros ls1 ls2 Hls;
      induction Hls; intros T f b1 b2 Hb Hf;
        simpl; auto.
      apply IHHls; auto.
      rewrite Hb. rewrite H.
      reflexivity.
    Qed.

    Instance fset_of_elems_Proper : Proper (SetoidList.eqlistA E.eq ==> FSet.Equal) fset_of_elems.
      intros ls1; induction ls1 as [ | A1 ls1];
        intros [ | A2 ls2] Heq; simpl.
      * reflexivity.
      * inversion Heq.
      * inversion Heq.
      * inversion Heq; subst; clear Heq.
        rewrite H2. rewrite (IHls1 ls2); auto.
        reflexivity. 
    Qed.

    Lemma foldProper' : forall ls1 ls2,
      SetoidList.eqlistA E.eq ls1 ls2 ->
      forall  T f (b1 b2 : M.t T),
      Equal b1 b2 ->
      Proper (E.eq ==> Equal ==>  Equal) f ->
      M.Equal (FSet.fold f (fset_of_elems ls1) b1)
              (FSet.fold f (fset_of_elems ls2) b2).
    Proof.
      intros.
      repeat rewrite FSet.fold_1.
      apply foldProper''; auto.
      + apply elements_Proper'.
        rewrite H.
        reflexivity.
      + clear ls1 ls2 H b1 b2 H0.
        intros ? ? Heq ? ? Heq'.
        rewrite Heq, Heq'.
        reflexivity.
    Qed.

    #[local] Instance foldProper : forall T f, 
      Proper (E.eq ==> Equal ==> Equal) f ->
      Proper (FSet.Equal ==> @M.Equal T ==> @M.Equal T) (@FSet.fold (M.t T) f).
    Proof.
      intros T f Hf X1 X2 HX M1 M2 HM.
      repeat rewrite FSet.fold_1.
      apply foldProper''; auto.
      2:{
        intros ? ? Heq ? ? Heq'. rewrite Heq, Heq'. reflexivity.
      }
      apply elements_Proper'; auto.
    Qed.

    #[local] Instance setminusProper : forall T, Proper (FSet.Equal ==> @M.Equal T ==> @M.Equal T) setminus.
    Proof.
      intros T X1 X2 HX M1 M2 HM.
      unfold setminus.
      apply foldProper; auto.
      clear M1 M2 HM X1 X2 HX.
      intros A1 A2 HA M1 M2 HM.
      rewrite HA. rewrite HM. reflexivity.
    Qed.

    Lemma mapsto_fset_fold_iff : forall T ls x a (m : t T),
      MapsTo x a (fold_left (fun n x => remove x n) ls m)
      <->
      ~ SetoidList.InA E.eq x ls /\ M.MapsTo x a m.
    Proof.
      intros T ls.
      induction ls as [ | D ls]; intros x a m; simpl.
      * intuition. inversion H0.
      * rewrite SetoidList.InA_cons.
        rewrite IHls.
        rewrite F.remove_mapsto_iff.
        intuition.
    Qed.

    Lemma setminus_mapsto_iff : forall {A} x (a : A) X m,
      M.MapsTo x a (setminus X m)
      <->
      ~ FSet.In x X /\ M.MapsTo x a m.
    Proof.
      intros. unfold setminus.
      rewrite FSet.fold_1.
      rewrite mapsto_fset_fold_iff.
      rewrite FSetProperties.elements_iff.
      reflexivity.
    Qed.

    Lemma removeA_eqlistA : forall ls A,
      ~ SetoidList.InA E.eq A ls ->
      SetoidList.eqlistA E.eq (SetoidList.removeA E.eq_dec A ls) ls.
    Proof.
      induction ls as [ | B ls]; intros A Hin; simpl.
      { constructor. }
      Proofs.compare A B.
      {
        exfalso. apply Hin. constructor; auto.
      }
      constructor; [reflexivity | ].
      apply IHls.
      {
        intros Hin0; apply Hin.
        apply SetoidList.InA_cons_tl; auto.
      }
    Qed.

    Lemma setminus_in_remove' : forall ls T A (m : t T),
      SetoidList.InA E.eq A ls ->
      SetoidList.NoDupA E.eq ls ->
      M.Equal
        (fold_left (fun n x => remove x n) ls m)
        (fold_left (fun n x => remove x n) (SetoidList.removeA E.eq_dec A ls) (remove A m)).
    Proof.
      induction ls as [ | B ls]; intros T A m Hin Hdup.
      * simpl. inversion Hin.
      * simpl. inversion Hdup; subst; clear Hdup.
        Proofs.compare A B.
        + (* A = B *)
          apply foldProper''.
          2:{ rewrite Heq. reflexivity. }
          2:{ intros ? ? Heq0 ? ? Heq0'.
              rewrite Heq0, Heq0'. reflexivity.
          }
          rewrite removeA_eqlistA.
          { reflexivity. }
          { rewrite Heq. auto. }
        + (* A <> B *)
          inversion Hin; subst; clear Hin;
            try contradiction.
          simpl.
          rewrite IHls; eauto.
          apply foldProper''; try reflexivity.
          2:{
            intros ? ? Heq0 ? ? Heq0';
            rewrite Heq0, Heq0'; reflexivity.
          }
          apply Proofs.remove_swap.
    Qed.


    Lemma hdrel_tail : forall l A B,
      Sorted.Sorted E.lt (B :: l) ->
      Sorted.HdRel E.lt A (B :: l) ->
      Sorted.HdRel E.lt A l.
    Proof.
      intros l A B Hsort Hhd.
      inversion Hhd; subst; clear Hhd.
      inversion Hsort; subst; clear Hsort.
      inversion H3; subst; clear H3; auto.
      constructor. rewrite H0; auto.
    Qed.

    Lemma hdrel_removeA : forall l A B,
      Sorted.Sorted E.lt l ->
      Sorted.HdRel E.lt A l ->
      Sorted.HdRel E.lt A (SetoidList.removeA F.eq_dec B l).
    Proof.
      induction l as [ | D l];
        intros A B Hsort Hhd; simpl; auto.
      inversion Hsort; subst.
      Proofs.compare B D.
      * apply IHl; auto. apply hdrel_tail in Hhd; auto.
      * inversion Hhd; subst; clear Hhd.
        constructor; auto.
    Qed.

    Lemma removeA_sorted : forall ls A,
      Sorted.Sorted E.lt ls ->
      Sorted.Sorted E.lt (SetoidList.removeA F.eq_dec A ls).
    Proof.
      intros ls A Hsort.
      induction Hsort; simpl.
      { constructor. }
      Proofs.compare A a; auto.
      constructor; auto.
      apply hdrel_removeA; auto.
    Qed.

    Lemma elements_remove : forall A X,
      SetoidList.eqlistA E.eq
        (FSet.elements (FSet.remove A X))
        (SetoidList.removeA E.eq_dec A (FSet.elements X)).
    Proof.
      intros.
      eapply SetoidList.SortA_equivlistA_eqlistA; auto.
      { apply FSetProperties.E_ST. }
      { apply ltStrict. }
      { apply ltProper. }
      { apply FSet.elements_3. }
      {
        apply removeA_sorted.
        apply FSet.elements_3.
      }

      intros D.
      rewrite SetoidList.removeA_InA.
      2:{ apply FSetProperties.E_ST. }

      repeat rewrite <- FSetProperties.elements_iff.
      rewrite FSetProperties.remove_iff.
      reflexivity.
  Qed.


  Lemma remove_add : forall A B X,
      FSet.Equal
        (FSet.remove A (FSet.add B X))
        (if E.eq_dec A B
          then FSet.remove A X
          else FSet.add B (FSet.remove A X)).
    Proof.
      intros.
      intros D.
      Proofs.compare A B.
      {
        repeat rewrite FSetProperties.remove_iff.
        repeat rewrite FSetProperties.add_iff.
        intuition.
      }
      {
        repeat rewrite FSetProperties.remove_iff.
        repeat rewrite FSetProperties.add_iff.
        repeat rewrite FSetProperties.remove_iff.
        intuition.
        apply Heq. rewrite H; symmetry; auto.
      }
    Qed.

    Lemma setminus_add : forall T A X (N: M.t T),
      M.Equal
        (setminus (FSet.add A X) N)
        (setminus (FSet.remove A X) (M.remove A N)).
    Proof.
      intros. 

      unfold setminus.
      repeat rewrite FSet.fold_1.

      rewrite (setminus_in_remove'  _ _ A).
      2:{
        rewrite <- FSetProperties.elements_iff.
        rewrite FSetProperties.add_iff.
        left. reflexivity.
      }
      2:{ apply FSet.elements_3w. }
      
      apply foldProper''; try reflexivity.
      2:{
        intros ? ? Heq ? ? Heq';
        rewrite Heq, Heq'; reflexivity.
      }

      rewrite <- elements_remove.
      apply elements_Proper'.
      rewrite remove_add.
      Proofs.compare A A.
      reflexivity.
    Qed.

    Lemma setminus_empty : forall T (M : t T),
      Equal (setminus FSet.empty M) M.
    Proof.
      intros T M.
      unfold setminus.
      rewrite FSet.fold_1.
      rewrite elements_empty.
      simpl.
      reflexivity.
    Qed.

    Lemma setminus_singleton : forall T A (N : M.t T),
      M.Equal
        (setminus (FSet.singleton A) N)
        (M.remove A N).
    Proof.
      intros.
      setoid_replace (FSet.singleton A)
        with (FSet.add A FSet.empty).
      2:{
        intros D.
        rewrite FSetProperties.add_iff.
        rewrite FSetProperties.singleton_iff.
        rewrite FSetProperties.empty_iff.
        intuition.
      }
      rewrite setminus_add.
      setoid_replace (FSet.remove A FSet.empty)
        with FSet.empty.
      2:{
        intros D.
        rewrite FSetProperties.remove_iff.
        rewrite FSetProperties.empty_iff.
        intuition.
      }
      rewrite setminus_empty.
      reflexivity.
    Qed.

    (** Add *)


    Lemma add_mem_iff : forall x y s,
      FSet.mem x (FSet.add y s)
      =
      if E.eq_dec x y then true else FSet.mem x s.
    Proof.
      intros.
      rewrite FSetProperties.add_b.
      unfold FSetProperties.eqb.
      Proofs.compare y x; simpl;
        Proofs.compare x y; auto.
      { exfalso. apply Heq0. symmetry. auto. }
    Qed.


    Lemma singleton_mem_iff : forall x y,
      FSet.mem y (FSet.singleton x)
      =
      if E.eq_dec x y then true else false.
    Proof.
      intros.
      rewrite FSetProperties.singleton_b.
      auto.
    Qed.



  End FSetProofs.

  Module Tactics.
  (**
    Provides:
      * compare x y       - destructs Map.E.eq_dec x y and substitutes
      * reduce_eq_dec     - applies compare to goals/hypotheses containing Map.E.eq_dec
      * subst_map         - eliminates hypotheses of the form Map.Equal m1 m2 by rewriting
      * reflect_partition - converts Partition hypotheses into Disjoint + Map.Equal (concat) form
      * vsimpl            - simplifies hypotheses and goals that use maps

      * reflect_find - simplifies hypotheses and goals by reflecting to the find function
      * solve - tries to prove goals through reflection to find 
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
    Ltac solve := Proofs.solve.

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
    repeat
    (autorewrite with var_db in *;
      Map.Tactics.vsimpl;
      repeat Map.Tactics.reduce_eq_dec;
      try (first [tauto | reflexivity | discriminate | auto | intuition]; fail)).

  (* instantiate this for each relevant hint database *)
  Ltac reflect_find :=
    repeat (
      Map.Proofs.reflect_find_body;
      autorewrite with var_db in *;
      repeat Map.Tactics.reduce_eq_dec
    ).
  Ltac solve := 
    repeat (reflect_find; first [tauto | discriminate | auto; fail | intuition]).

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
  #[global] Hint Rewrite Map.Properties.F.empty_in_iff : var_db.

  #[global] Hint Rewrite Map.Properties.F.remove_in_iff : var_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_1 : var_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_2 : var_db.

  #[global] Existing Instance Map.Proofs.singletonProper.
  #[global] Existing Instance Map.Proofs.concatProper.
  #[global] Existing Instance Map.Proofs.domainProper.
  #[global] Existing Instance Map.FSetProofs.setminusProper.

  #[global] Hint Rewrite Map.Proofs.concat_find : var_db.
  #[global] Hint Rewrite Map.Proofs.concat_in : var_db.
  #[global] Hint Rewrite @Map.Proofs.concat_add_l : var_db.
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
  #[global] Hint Rewrite Map.Proofs.singleton_empty : var_db.
  #[global] Hint Rewrite Map.Proofs.remove_remove : var_db.

  #[global] Hint Rewrite @Map.FSetProofs.setminus_mapsto_iff : var_db.
  #[global] Hint Rewrite Map.FSetProofs.setminus_add : var_db.
  #[global] Hint Rewrite Map.FSetProofs.setminus_singleton : var_db.
  #[global] Hint Rewrite Map.FSetProofs.add_mem_iff : var_db.
  #[global] Hint Rewrite Map.FSetProofs.singleton_mem_iff : var_db.

  (* separate out more expensive resolves into extra_var_db *)
  #[global] Hint Resolve Map.empty_1 : var_db.  
  #[global] Hint Resolve Map.Properties.Partition_sym : extra_var_db.
  #[global] Hint Resolve @Map.Proofs.singleton_remove : var_db.
  #[global] Hint Resolve Map.Proofs.add_mapsto : extra_var_db.
  #[global] Hint Resolve Map.Proofs.disjoint_empty_1 Map.Proofs.disjoint_empty_2 : var_db.
  #[global] Hint Resolve Map.Proofs.disjoint_in_l Map.Proofs.disjoint_in_r : var_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_l : var_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_r : var_db.
  #[global] Hint Resolve Map.M.remove_1 : var_db.
  #[global] Hint Resolve Map.Proofs.disjoint_sym : extra_var_db.
  #[global] Hint Resolve Map.Proofs.concat_assoc : extra_var_db.

  (*
  #[global] Hint Extern 4 (Map.Partition (Map.concat _ _) _ _) => Map.Proofs.partition_concat : extra_var_db.
  #[global] Hint Extern 4 (Map.Partition _ (Map.concat _ _) _) => Map.Tactics.partition_concat : extra_var_db.
  #[global] Hint Extern 4 (Map.Partition _ _ (Map.concat _ _)) => Map.Tactics.partition_concat : extra_var_db.
*)

  #[global] Hint Rewrite Map.FSetProperties.inter_iff : var_db.
  #[global] Hint Rewrite Map.MProofs.FSetProperties.add_iff: var_db.
  #[global] Hint Rewrite Map.FSetProperties.singleton_iff : var_db.
  #[global] Hint Rewrite Map.FSetProperties.add_iff : var_db.
  #[global] Hint Rewrite Map.FSetProperties.remove_iff : var_db.

End Var.

Inductive unitary :=
| H | X | Y | Z | CNOT | SGATE | Sdag | TGATE | Tdag.


Module Config.
  
  Record t := {
    dim : nat;
    (*qrefs : Var.Map.t nat;*)
    qstate : Matrix (Nat.pow 2 dim) (Nat.pow 2 dim)
  }.


  Record WellScoped (refs : Var.Map.t nat) (cfg : t) := {
    wf_qstate : Matrix.WF_Matrix (qstate cfg);
    (*wf_qrefs : List.Forall
              (fun x => snd x < dim cfg)%nat
              (Var.Map.elements refs)
              *)
    wf_qrefs : forall x, Var.Map.In x refs -> (x < dim cfg)%nat
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
    let rho' := super (pad_u (dim cfg) q (bool_to_matrix b)) (qstate cfg) in
    (Var.Map.remove x refs, {|
      dim := dim cfg;
      qstate := rho'
    |}).

  Definition new (b : bool) refs (cfg : t) : Var.t * Var.Map.t nat * t :=
    (*let x := Var.fresh refs in*)
    let x := dim cfg in (* don't want x to depend on refs *)
    let q := dim cfg in
    let rho' := kron (qstate cfg) (bool_to_ket b × (bool_to_ket b)†) in
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

  (* Properties of well-scopedness*)

  Global Instance WellScopedProper : Proper (Var.Map.Equal ==> eq ==> iff) Config.WellScoped.
  Proof.
    intros refs1 refs2 Hrefs cfg1 cfg2 Hcfg; subst.
    split; intros [wf_qstate wf_qrefs].
    + split; auto;
      intros x; setoid_rewrite <- Hrefs; auto.
    + split; auto;
      intros x; setoid_rewrite Hrefs; auto.
  Qed.

  Lemma WellScoped_concat : forall Θ1 Θ2 cfg,
    WellScoped (Var.Map.concat Θ1 Θ2) cfg 
    <->
    WellScoped Θ1 cfg /\ Config.WellScoped Θ2 cfg.
  Proof.
    intros ? ? ?.
    split.
    + intros [wf ws].
      split; split; auto;
      intros x Hin; apply ws;
      autorewrite with var_db; auto.
    + intros [[wf ws1] [_ ws2]].
      split; auto.
      intros x Hin. autorewrite with var_db in Hin.
      destruct Hin as [Hin | Hin];
        [apply ws1 | apply ws2]; auto.
  Qed.
  #[global] Hint Rewrite WellScoped_concat : var_db.

  Lemma WellScoped_empty : forall cfg,
    WF_Matrix (qstate cfg) ->
    WellScoped (Var.Map.empty nat) cfg.
  Proof.
    intros cfg HWF.
    split; auto.
    intros z Hin.
    autorewrite with var_db in *.
    contradiction.
  Qed.


  (* The operations on configurations form Proper relations *)
  Global Instance freshProper : forall A, 
      Proper (@Var.Map.Equal A ==> eq) Var.fresh.
  Proof.

    intros A refs1 refs2 Hrefs.
    unfold Var.fresh.
    apply Var.Map.Properties.fold_Equal; auto.
    + intros ? ? ? ? ? ? ? ? ?; subst; auto.
    + intros ? ? ? ? ? ?.
    
      destruct (k' + 1 <=? k) eqn:H_k'_k;
      destruct (a <=? k') eqn:Hk';
      destruct (a <=? k) eqn:Hk;
      destruct (k+1 <=? k') eqn:H_k_k';
      auto;
        try 
        (try rewrite Nat.leb_le in *;
        try rewrite Nat.leb_nle in *;
        lia).
      * rewrite H_k'_k; auto.
      * rewrite Hk'; auto.
      * rewrite H_k'_k; auto.
      * rewrite H_k'_k; auto. rewrite Hk'; auto.
      * rewrite Hk'; auto.
  Qed.   


      
  Global Instance find_Proper : Proper (eq ==> Var.Map.Equal ==> eq) find.
  Proof.
    intros x' x Hx refs1 refs2 Hrefs; subst.
    unfold Config.find. rewrite Hrefs; auto.
  Qed.

  Lemma measure_Proper : forall b x cfg refs1 refs2 refs1' refs2' cfg1' cfg2',
    Var.Map.Equal refs1 refs2 ->
    measure b x refs1 cfg = (refs1', cfg1') ->
    measure b x refs2 cfg = (refs2', cfg2') ->
    Var.Map.Equal refs1' refs2' /\ cfg1' = cfg2'.
  Proof.
    intros ? ? ? ? ? ? ? ? ?.
    intros Heq Hmeas1 Hmeas2.
    inversion Hmeas1; inversion Hmeas2; subst; clear Hmeas1 Hmeas2.
    split.
    + rewrite Heq. reflexivity.
    + unfold find. rewrite Heq. reflexivity.
  Qed.

  Global Instance measureProper :
    Proper (eq ==> eq ==> Var.Map.Equal ==> eq ==>
      RelationPairs.RelProd Var.Map.Equal eq)
      measure.
  Proof.
    intros ? b ? ? x ? refs1 refs2 Hrefs ? cfg ?;
      subst.
    
    eapply (measure_Proper b x cfg) in Hrefs;
      try reflexivity.
    destruct Hrefs as [Heq Heq'].
    split; unfold RelationPairs.RelCompFun;
      simpl; auto.
  Qed.

  Global Instance newProper :
    Proper (eq ==> Var.Map.Equal ==> eq ==>
      RelationPairs.RelProd (RelationPairs.RelProd eq Var.Map.Equal) eq)
      new.
  Proof.
    intros ? b ? refs1 refs2 Hrefs ? cfg ?; subst.
    repeat split; unfold RelationPairs.RelCompFun;
      simpl; auto.
    rewrite Hrefs; reflexivity.
  Qed.

  Global Instance eprProper :
    Proper (Var.Map.Equal ==> eq ==>
      RelationPairs.RelProd
      (RelationPairs.RelProd eq Var.Map.Equal)
      eq)
      epr.
  Proof.
    intros refs1 refs2 Hrefs ? cfg ?; subst;
    repeat split; unfold RelationPairs.RelCompFun;
      simpl; auto.
    * rewrite Hrefs; auto.
    * rewrite Hrefs. reflexivity.
  Qed. 

  Global Instance apply_gate_Proper :
    Proper (eq ==> eq ==> Var.Map.Equal ==> eq ==> eq) apply_gate.
  Proof.
    intros g' g Hg ls' ls Hls refs1 refs2 Hrefs cfg1 cfg2 Hcfg;
      subst.
    unfold Config.apply_gate.
    f_equal. f_equal.
    apply Proper_map; auto.
    intros x. rewrite Hrefs; auto.
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


  Module V := OrderedTypeEx.UOT_to_OT (OrderedTypeEx.String_as_OT).
  Include V.
  
  Module Map := FMap(V).
  Module FSet := Map.S.

  Ltac simplify :=
    repeat
    (autorewrite with actor_db in *;
      Map.Tactics.vsimpl;
      repeat Map.Tactics.reduce_eq_dec;
      try (first [tauto | reflexivity | discriminate | auto | intuition]; fail)).

  (* instantiate this for each relevant hint database *)
  Ltac reflect_find :=
    repeat (
      Map.Proofs.reflect_find_body;
      autorewrite with actor_db in *;
      repeat Map.Tactics.reduce_eq_dec
    ).
  Ltac solve := 
    repeat (reflect_find; first [tauto | discriminate | auto; fail | intuition]).

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
  #[global] Hint Rewrite Map.Properties.F.empty_in_iff : actor_db.

  #[global] Hint Resolve Map.empty_1 : actor_db.
  #[global] Hint Resolve Map.Properties.Partition_sym : actor_db.
  #[global] Hint Rewrite Map.Properties.F.remove_in_iff : actor_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_1 : actor_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_2 : actor_db.

  #[global] Existing Instance Map.Proofs.singletonProper.
  #[global] Existing Instance Map.Proofs.concatProper.
  #[global] Existing Instance Map.Proofs.domainProper.
  #[global] Existing Instance Map.FSetProofs.setminusProper.

  #[global] Hint Rewrite Map.Proofs.concat_find : actor_db.
  #[global] Hint Rewrite Map.Proofs.concat_in : actor_db.
  #[global] Hint Rewrite @Map.Proofs.concat_add_l : actor_db.
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
  #[global] Hint Rewrite Map.Proofs.singleton_empty : actor_db.
  #[global] Hint Rewrite Map.Proofs.remove_remove : actor_db.

  #[global] Hint Rewrite @Map.FSetProofs.setminus_mapsto_iff : actor_db.
  #[global] Hint Rewrite Map.FSetProofs.setminus_add : actor_db.
  #[global] Hint Rewrite Map.FSetProofs.setminus_singleton : actor_db.
  #[global] Hint Rewrite Map.FSetProofs.add_mem_iff : actor_db.
  #[global] Hint Rewrite Map.FSetProofs.singleton_mem_iff : actor_db.

  #[global] Hint Resolve Map.Proofs.add_mapsto : actor_db.
  #[global] Hint Resolve Map.Proofs.disjoint_empty_1 Map.Proofs.disjoint_empty_2 : actor_db.
  #[global] Hint Resolve Map.Proofs.disjoint_in_l Map.Proofs.disjoint_in_r : actor_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_l : actor_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_r : actor_db.
  #[global] Hint Resolve Map.M.remove_1 : actor_db.
  #[global] Hint Resolve Map.Proofs.disjoint_sym : actor_db.
  #[global] Hint Resolve Map.Proofs.concat_assoc : actor_db.

  (*
  #[global] Hint Extern 4 (Map.Partition (Map.concat _ _) _ _) => Map.Proofs.partition_concat : actor_db.
  #[global] Hint Extern 4 (Map.Partition _ (Map.concat _ _) _) => Map.Tactics.partition_concat : actor_db.
  #[global] Hint Extern 4 (Map.Partition _ _ (Map.concat _ _)) => Map.Tactics.partition_concat : actor_db.
  *)

  #[global] Hint Rewrite Map.FSetProperties.inter_iff : actor_db.
  #[global] Hint Rewrite Map.MProofs.FSetProperties.add_iff: actor_db.
  #[global] Hint Rewrite Map.FSetProperties.singleton_iff : actor_db.
  #[global] Hint Rewrite Map.FSetProperties.add_iff : actor_db.
  #[global] Hint Rewrite Map.FSetProperties.remove_iff : actor_db.

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


    Definition remove {T} (A : Actor.t) (x : Var.t) (CE : t T) :  t T :=
        (Actor.Map.add A (Var.Map.remove x (find A CE)) CE).

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
      (ChorEnv.find A (ChorEnv.add B x a G))
      = (if Actor.eq_dec A B then Var.Map.add x a (ChorEnv.find A G) else ChorEnv.find A G).
    Proof.
      intros.
      unfold ChorEnv.add, ChorEnv.find.
      autorewrite with actor_db.
      repeat Actor.Map.Tactics.reduce_eq_dec.
      + destruct (Actor.Map.find B G); try reflexivity.
      + destruct (Actor.Map.find B G); try reflexivity.
    Qed.
    #[global] Hint Rewrite find_add : var_db.


    Lemma find_add' : forall {T} A B M (M' : t T),
      (find A (Actor.Map.add B M M'))
      = (if Actor.eq_dec A B then M else find A M').
    Proof.
      intros.
      unfold find.
      Actor.simplify.
    Qed.
    #[global] Hint Rewrite @find_add' : var_db.

    Lemma find_remove : forall {T} A B x (G : t T),
      (ChorEnv.find A (ChorEnv.remove B x G))
      = (if Actor.eq_dec A B then Var.Map.remove x (find B G) else find A G).
    Proof.
      intros.
      unfold find. unfold remove.
      autorewrite with actor_db.
      repeat Actor.Map.Tactics.reduce_eq_dec; try reflexivity.
    Qed.
    #[global] Hint Rewrite @find_remove : var_db.

    Global Instance find_Proper : forall T, Proper (eq ==> Equal ==> Var.Map.Equal) (@find T).
    Proof.
      intros T ? A ? env1 env2 Henv; subst.
      unfold find. unfold Equal in Henv.
      destruct Henv as [Hiff Hmapsto].
      destruct (Actor.Map.find A env1) as [D1 | ] eqn:H1;
      destruct (Actor.Map.find A env2) as [D2 | ] eqn:H2.
      * apply (Hmapsto A); Actor.solve.
      * exfalso.
        apply Actor.Map.Properties.F.not_find_in_iff in H2.
        apply H2.
        rewrite <- Hiff.
        rewrite Actor.Map.Properties.F.in_find_iff.
        rewrite H1. congruence.
      * exfalso.
        apply Actor.Map.Properties.F.not_find_in_iff in H1.
        apply H1.
        rewrite Hiff.
        rewrite Actor.Map.Properties.F.in_find_iff.
        rewrite H2. congruence.
      * reflexivity.
    Qed.
      
    Global Instance add_Proper : forall T, Proper (eq ==> eq ==> eq ==> Equal ==> Equal) (@add T).
    Proof.
      intros T ? A ? ? x ? ? tau ? G1 G2 HG; subst.
      assert (Hfind : Var.Map.Equal (find A G1) (find A G2)) by (rewrite HG; reflexivity).
      destruct HG as [Hin Hmapsto].
      split; unfold add.
      * intros B.
        Actor.simplify.
        rewrite Hin. reflexivity.
      * intros B m1 m2 Hm1 Hm2.
        Actor.Map.Tactics.compare A B.
        { (* A = B *)
          Actor.reflect_find.
          inversion Hm2; subst; clear Hm2.
          destruct Hm1 as [[? ?] | [? ?]]; try contradiction.
          subst.
          rewrite Hfind.
          reflexivity.
        }
        { (* A <> B *)
          Actor.reflect_find.
          destruct Hm1 as [[? ?] | [_ Hm1]]; try contradiction.
          apply (Hmapsto B m1 m2); auto.
          Actor.solve.
        }
    Qed.

    Global Instance remove_Proper : forall T, Proper (eq ==> eq ==> Equal ==> Equal) (@remove T).
    Proof.
      intros T ? A ? ? x ? G1 G2 HG; subst.
      unfold remove.
      assert (Hfind : Var.Map.Equal (find A G1) (find A G2)) by (rewrite HG; reflexivity).
      destruct HG as [Hin Hmapsto].
      split.
      * intros B.
        Actor.simplify.
        rewrite Hin.
        reflexivity.
      * intros B D1 D2 H1 H2.
        Actor.Map.Tactics.compare A B.
        + (* A = B *)
          Actor.reflect_find.
          destruct H1 as [[_ ?] | [? _]]; try contradiction.
          inversion H2; subst; clear H2.
          rewrite Hfind.
          reflexivity.
        + (* A <> B *)
          Actor.reflect_find.
          destruct H1 as [[? _] | [_ H1]]; try contradiction.
          apply (Hmapsto B); auto.
          Actor.solve.
    Qed.

    Global Instance MapsTo_Proper : forall T,
        Proper (eq ==> eq ==> eq ==> Equal ==> iff) (@MapsTo T).
    Proof.
      intros T ? A ? ? x ? ? tau ? G1 G2 HG; subst.
      unfold MapsTo.
      rewrite HG.
      reflexivity.
    Qed.

    Global Instance Equal_refl : forall T, Reflexive (@Equal T).
    Proof.
      intros T x.
      split.
      * intros; reflexivity.
      * intros.
        Actor.solve.
        inversion H1; subst; reflexivity.
    Qed.

    Global Instance Equal_symm : forall T, Symmetric (@Equal T).
    Proof.
      intros T env1 env2 Heq.
      unfold Equal in *.
      unfold Actor.Map.Equiv in *.
      destruct Heq as [Hin Hmapsto].
      split.
      * intros. symmetry. auto.
      * intros. symmetry. apply (Hmapsto k e' e); auto.
    Qed.

    Global Instance Equal_trans : forall T, Transitive (@Equal T).
    Proof.
      intros T env1 env2 env3 [Hin Hmapsto] [Hin' Hmapsto'].
      split.
      * intros k. rewrite Hin. auto.
      * intros k e e' H1 H3.
        assert (Hin2 : Actor.Map.In k env2).
        { apply Hin. exists e. auto. }
        destruct Hin2 as [e2 Hmapsto2].
        rewrite Hmapsto; eauto.
    Qed.

    Global Instance actor_add_Proper : forall T, Proper (eq ==> @Var.Map.Equal T ==> Equal ==> @Equal T)
                                                        (@Actor.Map.add (Var.Map.t T)).
    Proof.
      intros T ? A ? D1 D2 HD T1 T2 [HT HT']; subst.
      split.
      * intros k. Actor.simplify. rewrite HT. reflexivity.
      * intros B e1 e2 He1 He2.
        Actor.simplify.
        destruct He1 as [[? ?] | [? He1]];
        destruct He2 as [[? ?] | [? He2]];
        subst; try contradiction; auto.
        (* A <> B *)
        eapply HT'; eauto.
    Qed.

    Lemma actor_map_Equal : forall T (M1 M2 : t T),
      Actor.Map.Equal M1 M2 -> Equal M1 M2.
    Proof.
      intros T M1 M2 Heq.
      split.
      * intros A. rewrite Heq. reflexivity.
      * intros A D1 D2 HD1 HD2.
        Actor.reflect_find.
        rewrite Heq in HD1.
        rewrite HD1 in HD2.
        inversion HD2; clear HD2.
        reflexivity.
    Qed.

    Lemma actor_map_Equal' : forall T (M1 M2 N1 N2 : t T),
      Actor.Map.Equal M1 M2 -> Actor.Map.Equal N1 N2 -> Equal M1 N1 -> Equal M2 N2.
    Proof.
      intros T M1 M2 N1 N2 HeqM HeqN Heq.
      apply actor_map_Equal in HeqM.
      apply actor_map_Equal in HeqN.
      rewrite <- HeqM.
      rewrite <- HeqN.
      auto.
    Qed.

    Global Instance Equal_Proper : forall T, Proper (Actor.Map.Equal ==> Actor.Map.Equal ==> iff) (@Equal T).
    Proof.
      intros T M1 M2 HM N1 N2 HN.
      split; intros.
      eapply actor_map_Equal'; eauto.
      eapply actor_map_Equal'; eauto; symmetry; auto.
    Qed.

End ChorEnv.