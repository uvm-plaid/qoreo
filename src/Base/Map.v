From Stdlib Require FSets.FMapList FSets.FSetList 
                            FSets.FMapFacts
                            FSets.FMapInterface
                            OrderedType OrderedTypeEx.
From Stdlib Require Export String.
From Stdlib Require Export Morphisms. (* for Proper *)
Require Export Setoid. (* for setoid_replace with *)


From Stdlib Require Lists.List.
Export List.ListNotations.
Open Scope list_scope.

Declare Scope qoreo.
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

    Lemma and_not_or : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
    Proof. tauto. Qed.


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
      apply and_not_or
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

      M.Equal (List.fold_left f ls1 b1)
              (List.fold_left f ls2 b2).
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
      MapsTo x a (List.fold_left (fun n x => remove x n) ls m)
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
        (List.fold_left (fun n x => remove x n) ls m)
        (List.fold_left (fun n x => remove x n) (SetoidList.removeA E.eq_dec A ls) (remove A m)).
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

    Lemma find_fold_left_nin : forall ls x T (M : t T),
      ~ M.In x M ->
      find x (List.fold_left (fun ls' x' => remove x' ls') ls M)
        = None.
    Proof.
      induction ls as [ | y ls]; intros x T M Hin; simpl.
      * destruct (find x M) as [v | ] eqn:Hfind; auto.
        exfalso.
        apply Hin. exists v.
        apply F.find_mapsto_iff; auto.
      * rewrite IHls; auto.
        intros Hin'.
        rewrite F.remove_in_iff in Hin'.
        destruct Hin'; contradiction.
    Qed.

    Lemma find_fold_left_nin_remove : forall ls x T (M : t T),
      ~ SetoidList.InA E.eq x ls ->
      find x (List.fold_left (fun ls' x' => remove x' ls') ls M)
        = find x M.
    Proof.
      induction ls as [ | y ls]; intros x T M Hin; auto.
      simpl.
      assert (~ SetoidList.InA E.eq x ls).
      { intros Hin'. apply Hin.
        apply SetoidList.InA_cons_tl; auto.
      }
      assert (~ E.eq x y).
      { intros Heq. apply Hin. constructor; auto. }
      rewrite IHls; auto.
      rewrite F.remove_neq_o; auto.
      { intros Heq. symmetry in Heq. contradiction. }
    Qed.

    Lemma find_fold_left_in_remove : forall ls x,
      SetoidList.InA E.eq x ls ->
      forall  T (M : t T),
      find x (List.fold_left (fun ls' x' => remove x' ls') ls M)
        = None.
    Proof.
      intros ls x Hin.
      induction Hin; intros T M; simpl.
      * rewrite find_fold_left_nin; auto.
        rewrite F.remove_in_iff.
        intros [Heq Hin].
        apply Heq. symmetry; auto.
      * rewrite IHHin; auto.
    Qed.

    Lemma find_setminus : forall T x X (m : t T),
      M.find x (setminus X m) = if in_dec x X then None else M.find x m.
    Proof.
      intros.
      unfold setminus.
      rewrite FSet.fold_1.
      destruct (in_dec x X) as [Hin | Hin].
      * rewrite find_fold_left_in_remove; auto.
        apply FSetProperties.elements_iff; auto.
      * rewrite find_fold_left_nin_remove; auto.
        rewrite <- FSetProperties.elements_iff; auto.
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

  Module Reflection.

  Inductive SetData :=
    | PrimSD : FSet.t -> SetData
    | EmptySD : SetData
    | AddSD : key -> SetData -> SetData
    | RemoveSD : key -> SetData -> SetData
    | UnionSD : SetData -> SetData -> SetData
    | IntersectSD : SetData -> SetData -> SetData
    .

  Module NormalSetData.
    (* 
        X ::= {x1,...,xn} ∪ Y1 ∪ ... ∪ Yn
        Y ::= Z1 ∩ ... ∩ Zm (must be non-empty)
        Z ::= Prim | Remove x Z
    *)
    Inductive NSD_Z := PrimNSD : FSet.t -> NSD_Z | RemoveNSD : key -> NSD_Z -> NSD_Z.
    Inductive NSD_Y := ZNSD : NSD_Z -> NSD_Y | ConsNSD : NSD_Z -> NSD_Y -> NSD_Y.
    Definition NSD := (list key * list NSD_Y)%type.

    Fixpoint appY Y1 Y2 :=
      match Y1 with
      | ZNSD Z1 => ConsNSD Z1 Y2
      | ConsNSD Z1 Y1' => ConsNSD Z1 (appY Y1' Y2)
      end.
    Fixpoint mapY f Y :=
      match Y with
      | ZNSD Z => ZNSD (f Z)
      | ConsNSD Z Y' => ConsNSD (f Z) (mapY f Y')
      end.

    (* From SetData to NSD *)
    (*
    PrimSD : FSet.t -> SetData
    | EmptySD : SetData
    | AddSD : key -> SetData -> SetData
    | RemoveSD : key -> SetData -> SetData
    | UnionSD : SetData -> SetData -> SetData
    | IntersectSD : SetData -> SetData -> SetData
    *)
    Definition primSD (X : FSet.t) : NSD :=
      ([],[ZNSD (PrimNSD X)]).

    Definition emptySD : NSD := ([],[]).

    Fixpoint insertKey (k : key) (l : list key) : list key :=
    match l with
    | [] => [k]
    | k'::l' =>
      if E.eq_dec k k' then k'::l'
      else k' :: insertKey k l'
    end.
    Definition addSD (x : key) (X : NSD) : NSD :=
      let (ks, Ys) := X in
      (insertKey x ks, Ys).

    
  Fixpoint removeKey k (l : list key) : list key :=
    match l with
    | [] => []
    | k'::l' => 
      if E.eq_dec k k'
      then removeKey k l'
      else k' :: removeKey k l'
    end.
    
  Fixpoint remove_NSD_Z k (Z : NSD_Z) :=
    match Z with
    | PrimNSD _ => RemoveNSD k Z
    | RemoveNSD k' Z' =>
      if E.eq_dec k k'
      then Z
      else RemoveNSD k' (remove_NSD_Z k Z')
    end.
  Definition remove_NSD_Y k (Y : NSD_Y) : NSD_Y :=
    mapY (remove_NSD_Z k) Y.
  Definition removeSD k (X : NSD) : NSD :=
    let (l,Ys) := X in
    (removeKey k l, List.map (remove_NSD_Y k) Ys).

  Fixpoint unionKeys (l1 l2 : list key) : list key :=
    match l1 with
    | [] => l2
    | k :: l1' => unionKeys l1' (insertKey k l2)
    end.

  Definition unionSD (X1 X2 : NSD) : NSD :=
    let (keys1, Ys1) := X1 in
    let (keys2, Ys2) := X2 in
    (unionKeys keys1 keys2, List.app Ys1 Ys2).


  (* Intersection *)
  Fixpoint key_in (k : key) (l : list key) : bool :=
    match l with
    | [] => false
    | k' :: l' => if E.eq_dec k k' then true else key_in k l'
    end.
  Fixpoint intersectKeys (keys1 keys2 : list key) : list key :=
    match keys1 with
    | [] => []
    | k :: keys1' =>
      if key_in k keys2
      then k :: intersectKeys keys1' keys2
      else intersectKeys keys1' keys2
    end.

  Definition intersectKeyY (k : key) (Y : NSD_Y) : NSD_Y :=
    ConsNSD (PrimNSD (FSet.singleton k)) Y.

  Definition intersectKeysX (keys : list key) (X : list NSD_Y)
      : list NSD_Y :=
    List.concat
      (List.map (fun k => List.map (intersectKeyY k) X) keys).

  (* Ys1 = Y1 ∪ ... ∪ Yn
     Ys2 = Y1' ∪ ... ∪ Ym'

     Ys1 ∩ Ys2 = Y1 ∩ Y1' ∪ ... ∪ Yn ∩ Ym'
   *)
  Definition intersectX (X1 X2 : list NSD_Y) : list NSD_Y :=
    List.concat
      (List.map (fun Y1 => List.map (appY Y1) X2) X1).

  (* Intersect key atoms directly; distribute key/conjunction and conjunction/
     conjunction pairs while keeping each result in NSD_Y form. *)
  Definition intersectSD (X1 X2 : NSD) : NSD :=
    let (keys1, Ys1) := X1 in
    let (keys2, Ys2) := X2 in
    (intersectKeys keys1 keys2,
     List.app (intersectKeysX keys1 Ys2)
       (List.app (intersectKeysX keys2 Ys1) (intersectX Ys1 Ys2))).




    (* From SetData to NSD *)
    (*
    PrimSD : FSet.t -> SetData
    | EmptySD : SetData
    | AddSD : key -> SetData -> SetData
    | RemoveSD : key -> SetData -> SetData
    | UnionSD : SetData -> SetData -> SetData
    | IntersectSD : SetData -> SetData -> SetData
    *)
  
    Fixpoint to_NSD (X : SetData) : NSD :=
      match X with
      | PrimSD Z => primSD Z
      | EmptySD  => emptySD
      | AddSD x X' => addSD x (to_NSD X')
      | RemoveSD x X' => removeSD x (to_NSD X')
      | UnionSD X1 X2 => unionSD (to_NSD X1) (to_NSD X2)
      | IntersectSD X1 X2 => intersectSD (to_NSD X1) (to_NSD X2)
      end.

    (* From NSD to SetData *)

    Fixpoint from_NSD_Z (Z : NSD_Z) : SetData :=
      match Z with
      | PrimNSD X => PrimSD X
      | RemoveNSD k Z' => RemoveSD k (from_NSD_Z Z')
      end.
    Fixpoint from_NSD_Y (Y : NSD_Y) :=
      match Y with
      | ZNSD Z => from_NSD_Z Z
      | ConsNSD Z Y' => IntersectSD (from_NSD_Z Z) (from_NSD_Y Y')
      end.
    Fixpoint from_NSD_X (X : list NSD_Y) :=
      match X with
      | [] => EmptySD
      | Y::X' => UnionSD (from_NSD_Y Y) (from_NSD_X X')
      end.
    Fixpoint from_NSD' (l : list key) (X : SetData) :=
      match l with
      | [] => X
      | k::l' => from_NSD' l' (AddSD k X)
      end.
    Definition from_NSD (X : NSD) : SetData :=
      let (l,X') := X in
      from_NSD' l (from_NSD_X X').

  End NormalSetData.

  Fixpoint fromSetData (S : SetData) : FSet.t :=
    match S with
    | PrimSD X => X
    | EmptySD => FSet.empty
    | AddSD x S' => FSet.add x (fromSetData S')
    | RemoveSD x S' => FSet.remove x (fromSetData S')
    | UnionSD S1 S2 => FSet.union (fromSetData S1) (fromSetData S2)
    | IntersectSD S1 S2 => FSet.inter (fromSetData S1) (fromSetData S2)
    end.

    Module Proof.

      Lemma from_NSD_add : forall x X,
        FSet.Equal
          (fromSetData (NormalSetData.from_NSD (NormalSetData.addSD x X)))
          (fromSetData (AddSD x (NormalSetData.from_NSD X))).
      Proof.
        intros x [keys Ys].
        simpl.
        assert (Hadd : forall ls k S,
            FSet.Equal
              (fromSetData
                (NormalSetData.from_NSD' ls (AddSD k S)))
              (fromSetData
                (AddSD k (NormalSetData.from_NSD' ls S)))).
        {
          intros ls.
          induction ls as [| y ls IH]; intros k S.
          - simpl. reflexivity.
          - simpl. rewrite IH. rewrite IH. 
            simpl. rewrite IH.
            simpl.
            intros z. 
            repeat rewrite FSetProperties.add_iff.
            tauto.
        }
        assert (Hinsert : forall ls k S,
            FSet.Equal
              (fromSetData
                (NormalSetData.from_NSD'
                  (NormalSetData.insertKey k ls) S))
              (fromSetData
                (AddSD k (NormalSetData.from_NSD' ls S)))).
        {
          intros ls.
          induction ls as [| y ls IH]; intros k S.
          - simpl. reflexivity.
          - simpl.
            destruct (E.eq_dec k y) as [Heq | Hneq].
            + rewrite Heq.
              simpl.
              rewrite (Hadd ls y S).
              simpl.
              intros z.
              repeat rewrite FSetProperties.add_iff.
              tauto.
            + simpl.
              rewrite (IH _ (AddSD y S)).
              reflexivity.
        }
        apply Hinsert.
      Qed.

      Lemma from_remove_NSD_Z : forall x Z,
            FSet.Equal
              (fromSetData (NormalSetData.from_NSD_Z
                (NormalSetData.remove_NSD_Z x Z)))
              (fromSetData (RemoveSD x
                (NormalSetData.from_NSD_Z Z))).
      Proof.
          intros x Z.
          induction Z as [S | k Z IH].
          - simpl. intros z.
            repeat rewrite FSetProperties.remove_iff.
            tauto.
          - simpl.
            destruct (E.eq_dec x k) as [Heq | Hneq].
            + rewrite Heq. simpl. intros z.
              repeat rewrite FSetProperties.remove_iff.
              tauto.
            + simpl. rewrite IH. simpl.
              intros z. repeat rewrite FSetProperties.remove_iff.
              tauto.
      Qed.

      Lemma from_remove_NSD_Y : forall x Y,
            FSet.Equal
              (fromSetData (NormalSetData.from_NSD_Y
                (NormalSetData.remove_NSD_Y x Y)))
              (fromSetData (RemoveSD x
                (NormalSetData.from_NSD_Y Y))).
      Proof.
        intros x Y; induction Y as [Z | Z Y].
          - simpl. 
            repeat rewrite from_remove_NSD_Z.
            simpl.
            reflexivity.
          - simpl. 
            repeat rewrite from_remove_NSD_Z.
            simpl.
            rewrite IHY.
            simpl.
            intros z.
            rewrite FSetProperties.inter_iff.
            repeat rewrite FSetProperties.remove_iff.          
            rewrite FSetProperties.inter_iff.
            tauto.
      Qed.

      Lemma from_remove_NSD_X : forall x Ys,
            FSet.Equal
              (fromSetData (NormalSetData.from_NSD_X
                (List.map (NormalSetData.remove_NSD_Y x) Ys)))
              (fromSetData (RemoveSD x
                (NormalSetData.from_NSD_X Ys))).
      Proof.
          intros x Ys.
          induction Ys as [| Y Ys IH].
          - simpl. intros z.
            repeat rewrite FSetProperties.remove_iff.
            rewrite FSetProperties.empty_iff.
            tauto.
          - simpl.
            rewrite from_remove_NSD_Y.
            rewrite IH. simpl.
            intros z.
            repeat rewrite FSetProperties.union_iff.
            repeat rewrite FSetProperties.remove_iff.
            repeat rewrite FSetProperties.union_iff.
            tauto.
      Qed.

      Lemma from_NSD'_iff : forall ls z X,
        FSet.In z (fromSetData (NormalSetData.from_NSD' ls X))
        <->
        SetoidList.InA E.eq z ls \/ FSet.In z (fromSetData X).
      Proof.
        induction ls as [ | k ls]; intros z X; simpl.
        * rewrite SetoidList.InA_nil.
          tauto.
        * rewrite IHls.
          simpl.
          rewrite FSetProperties.add_iff.
          rewrite SetoidList.InA_cons.
          intuition.
      Qed.

      Lemma in_removeKey_iff : forall ls x z,
        SetoidList.InA E.eq z (NormalSetData.removeKey x ls)
        <->
        SetoidList.InA E.eq z ls /\ ~ E.eq x z.
      Proof.
        induction ls as [ | k ls]; intros x z; simpl.
        * rewrite SetoidList.InA_nil. tauto.
        * rewrite SetoidList.InA_cons.
          Proofs.compare x k.
          + rewrite IHls. intuition.
            absurd (E.eq x z); auto.
            symmetry; auto.
          + rewrite SetoidList.InA_cons.
            rewrite IHls.
            intuition.
            rewrite <- H in H0.
            auto.
      Qed.

      Lemma from_remove_NSD' : forall x ls X,
        ~ FSet.In x (fromSetData X) ->
        FSet.Equal
          (fromSetData (NormalSetData.from_NSD' (NormalSetData.removeKey x ls) X))
          (fromSetData (RemoveSD x (NormalSetData.from_NSD' ls X))).
      Proof.
        intros x ls.
        induction ls as [ | k ls']; intros X Hin.
        * simpl. intros z.
          repeat rewrite FSetProperties.remove_iff.
          Proofs.compare x z.
          + tauto.
          + tauto.
        * simpl. Proofs.compare x k.
          + rewrite IHls'; auto.
            simpl.
            intros z.
            repeat rewrite FSetProperties.remove_iff.
            repeat rewrite from_NSD'_iff.
            simpl.
            repeat rewrite FSetProperties.add_iff.
            rewrite Heq.
            tauto.
          + simpl.
            intros z.
            repeat rewrite FSetProperties.remove_iff.
            repeat rewrite from_NSD'_iff.
            simpl.
            repeat rewrite FSetProperties.add_iff.
            rewrite in_removeKey_iff.
            intuition.
            { apply Heq. rewrite H. auto. }
            { rewrite <- H0 in H. contradiction. }
      Qed. 


      Lemma NSD_X_iff : forall X z,
        FSet.In z (fromSetData (NormalSetData.from_NSD_X X))
        <->
        exists Y, List.In Y X /\ FSet.In z (fromSetData (NormalSetData.from_NSD_Y Y)).
      Proof.
        induction X as [ | Y X]; intros z; simpl.
        * rewrite FSetProperties.empty_iff.
          intuition.
          destruct H as [Y [? ?]].
          tauto.
        * repeat rewrite FSetProperties.union_iff.
          rewrite IHX.
          intuition.
          + exists Y; auto.
          + destruct H0 as [Y0 [H0 H0']].
            exists Y0. tauto.
          + destruct H as [Y0 [[? | H0] H0']].
            - subst. auto.
            - right. exists Y0; auto.
      Qed.

      Inductive InY Z : NormalSetData.NSD_Y -> Prop :=
      | InBaseY : InY Z (NormalSetData.ZNSD Z)
      | InHeadY : forall Y, InY Z (NormalSetData.ConsNSD Z Y)
      | InTailY : forall Y Z0,
        InY Z Y ->
        InY Z (NormalSetData.ConsNSD Z0 Y).
      

      Lemma NSD_Y_iff : forall z Y,
        FSet.In z (fromSetData (NormalSetData.from_NSD_Y Y))
        <->
        forall Z, InY Z Y -> FSet.In z (fromSetData (NormalSetData.from_NSD_Z Z)).
      Proof.
        intros z; induction Y as [ Z | Z Y].
        * simpl. intuition.
          + inversion H0; subst; auto.
          + apply H. constructor. 
        * simpl.
          rewrite FSetProperties.inter_iff.
          rewrite IHY.
          split.
          + intros [H1 H2] Z0 HZ0.
            inversion HZ0; subst; auto.
          + intros H.
            split; auto.
            { apply H. constructor. }
            {
              intros Z0 HZ0. apply H.
              apply InTailY; auto.
            }
      Qed.  


      Lemma from_NSD_remove : forall x X,
        FSet.Equal
          (fromSetData (NormalSetData.from_NSD (NormalSetData.removeSD x X)))
          (fromSetData (RemoveSD x (NormalSetData.from_NSD X))).
      Proof.
        intros x [keys Ys] z.
        simpl.
        rewrite FSetProperties.remove_iff.
        rewrite from_remove_NSD'.
        2:{
          rewrite NSD_X_iff.
          intros [Y [HY Hin]].
          rewrite List.in_map_iff in HY.
          destruct HY as [Y0 [? HY]]; subst.
          rewrite from_remove_NSD_Y in Hin.
          simpl in Hin.
          rewrite FSetProperties.remove_iff in Hin.
          destruct Hin as [_ Hin]; apply Hin; reflexivity.
        }
        repeat rewrite from_NSD'_iff.
        simpl.
        rewrite FSetProperties.remove_iff.
        repeat rewrite from_NSD'_iff.
        split.
        * intuition.
          right.
          rewrite NSD_X_iff in *.
          destruct H as [Y [HY H]].
          rewrite List.in_map_iff in HY.
          destruct HY as [Y0 [? HY0]]; subst.
          exists Y0.
          split; auto.
          rewrite from_remove_NSD_Y in H.
          simpl in H. rewrite FSetProperties.remove_iff in H.
          intuition.
        * intuition.
          right.
          rewrite NSD_X_iff in *.
          destruct H as [Y [HY H]].
          exists (NormalSetData.remove_NSD_Y x Y).
          split.
          + rewrite List.in_map_iff.
            exists Y; auto.
          + rewrite from_remove_NSD_Y. simpl.
            rewrite FSetProperties.remove_iff.
            auto.
      Qed.

      Lemma in_insertKey_iff : forall k ls z,
        SetoidList.InA E.eq z (NormalSetData.insertKey k ls) <->
        E.eq z k \/ SetoidList.InA E.eq z ls.
      Proof.
        intros k ls.
        induction ls as [| y ls IH]; intros z; simpl.
        - rewrite SetoidList.InA_cons.
          tauto.
        - Proofs.compare k y.
          + rewrite SetoidList.InA_cons.
            tauto.
          + repeat rewrite SetoidList.InA_cons.
            rewrite IH.
            tauto.
      Qed.

      Lemma in_unionKeys_iff : forall ls1 ls2 z,
        SetoidList.InA E.eq z (NormalSetData.unionKeys ls1 ls2) <->
        SetoidList.InA E.eq z ls1 \/ SetoidList.InA E.eq z ls2.
      Proof.
        intros ls1.
        induction ls1 as [| k ls1 IH]; intros ls2 z; simpl.
        - rewrite SetoidList.InA_nil. tauto.
        - repeat rewrite SetoidList.InA_cons, IH, in_insertKey_iff.
          tauto.
      Qed.

      Lemma from_NSD_X_app : forall Ys1 Ys2,
        FSet.Equal
          (fromSetData
            (NormalSetData.from_NSD_X (List.app Ys1 Ys2)))
          (FSet.union
            (fromSetData (NormalSetData.from_NSD_X Ys1))
            (fromSetData (NormalSetData.from_NSD_X Ys2))).
      Proof.
        intros Ys1 Ys2 z.
        induction Ys1 as [| Y Ys1 IH]; simpl.
        - rewrite FSetProperties.union_iff, FSetProperties.empty_iff.
          tauto.
        - repeat rewrite FSetProperties.union_iff.
          rewrite IH, FSetProperties.union_iff.
          tauto.
      Qed.

      Lemma from_NSD_union : forall X1 X2,
        FSet.Equal
          (fromSetData (NormalSetData.from_NSD (NormalSetData.unionSD X1 X2)))
          (fromSetData (UnionSD (NormalSetData.from_NSD X1) (NormalSetData.from_NSD X2))).
      Proof.
        intros [keys1 Ys1] [keys2 Ys2].
        simpl.
        intros z.
        repeat rewrite from_NSD'_iff.
        rewrite from_NSD_X_app.
        repeat rewrite FSetProperties.union_iff, in_unionKeys_iff.
        rewrite FSetProperties.union_iff.
        repeat rewrite from_NSD'_iff.
        tauto.
      Qed.

      (* Intersection *)
      Lemma key_in_iff : forall x keys,
        SetoidList.InA E.eq x keys
        <->
        NormalSetData.key_in x keys = true.
      Proof.
        intros x keys. induction keys as [ | k keys].
        * rewrite SetoidList.InA_nil. simpl. intuition.
        * simpl. rewrite SetoidList.InA_cons.
          rewrite IHkeys.
          Proofs.compare x k.
          + intuition.
          + tauto.
      Qed.
      Lemma intersectKeys_iff : forall keys1 keys2 x,
        SetoidList.InA E.eq x (NormalSetData.intersectKeys keys1 keys2)
        <->
        SetoidList.InA E.eq x keys1 /\ SetoidList.InA E.eq x keys2.
      Proof.
        induction keys1 as [ | k keys1];
          intros keys2 x; simpl.
        * repeat rewrite SetoidList.InA_nil. tauto.
        * rewrite SetoidList.InA_cons.
          destruct (NormalSetData.key_in k keys2) eqn:Hin2.
          + rewrite <- key_in_iff in Hin2.
            rewrite SetoidList.InA_cons.
            rewrite IHkeys1.
            intuition.
            rewrite H0. auto.
          + rewrite IHkeys1.
            intuition.
            rewrite H in H1.
            rewrite key_in_iff in H1.
            rewrite H1 in Hin2.
            discriminate.
      Qed.


      Lemma inY_cons_iff : forall Z Z' Y,
        InY Z (NormalSetData.ConsNSD Z' Y)
        <->
        Z = Z' \/ InY Z Y.
      Proof.
        intros; split; intro H.
        * inversion H; auto.
        * destruct H; subst.
          + constructor.
          + apply InTailY; auto. 
      Qed.
      Lemma inY_Z_iff : forall Z Z',
        InY Z (NormalSetData.ZNSD Z')
        <->
        Z = Z'.
      Proof.
        intros; split; intros H.
        * inversion H; auto.
        * subst; constructor. 
      Qed.
      Lemma inY_appY_iff : forall Y1 Y2 Z,
          InY Z (NormalSetData.appY Y1 Y2)
          <->
          InY Z Y1 \/ InY Z Y2.
      Proof.
        induction Y1 as [ Z1 | Z1 Y1]; intros Y2 Z; simpl.
        * rewrite inY_cons_iff. rewrite inY_Z_iff. reflexivity.
        * repeat rewrite inY_cons_iff.
          rewrite IHY1. tauto.   
      Qed.


      Lemma from_NSD_intersect_X : forall Ys1 Ys2,
        FSet.Equal
          (fromSetData (NormalSetData.from_NSD_X (NormalSetData.intersectX Ys1 Ys2)))
          (FSet.inter (fromSetData (NormalSetData.from_NSD_X Ys1))
                      (fromSetData (NormalSetData.from_NSD_X Ys2))).
      Proof.
        induction Ys1 as [ | Y Ys1]; intros Ys2; simpl.
        * intros z.
          rewrite FSetProperties.inter_iff.
          rewrite FSetProperties.empty_iff.
          tauto.
        * unfold NormalSetData.intersectX in *. simpl.
          rewrite from_NSD_X_app.
          rewrite IHYs1.
          intros z.
          rewrite FSetProperties.inter_iff.
          repeat rewrite FSetProperties.union_iff.
          repeat rewrite FSetProperties.inter_iff.
          rewrite NSD_X_iff.
          intuition.
          + destruct H0 as [Y0 [HY1 HY2]].
            rewrite List.in_map_iff in HY1.
            destruct HY1 as [Y' [? HY1]]. subst.
            rewrite NSD_Y_iff in HY2.
            rewrite NSD_Y_iff.
            left.
            intros Z HZ.
            apply HY2.
            rewrite inY_appY_iff.
            tauto.
            
          + rewrite NSD_X_iff.
            destruct H0 as [Y0 [HY1 HY2]].
            rewrite  List.in_map_iff in HY1.
            destruct HY1 as [Y' [? HY1]]. subst.
            exists Y'; split; auto.

            rewrite NSD_Y_iff in HY2.
            rewrite NSD_Y_iff.
            intros Z HZ.
            apply HY2.
            rewrite inY_appY_iff.
            tauto.

          + left.
          
            rewrite NSD_X_iff in H1.
            destruct H1 as [Y0 [HY0 H1]].
            

            exists (NormalSetData.appY Y Y0).
            split; auto.
            - rewrite List.in_map_iff.
              exists Y0. auto.
            - rewrite NSD_Y_iff in *.
              intros Z HZ.
              rewrite inY_appY_iff in HZ.
              destruct HZ as [HZ | HZ]; auto.
      Qed.

      Lemma from_NSD_intersectKeyY : forall Y k,
        FSet.Equal
          (fromSetData (NormalSetData.from_NSD_Y (NormalSetData.intersectKeyY k Y)))
          (FSet.inter
            (FSet.singleton k)
            (fromSetData (NormalSetData.from_NSD_Y Y))).
      Proof.
        destruct Y as [Z | Z Y]; intros k; simpl.
        { reflexivity. }
        reflexivity.
      Qed.
      

      Lemma from_NSD_intersectKeysX : forall keys X,
        FSet.Equal
          (fromSetData (NormalSetData.from_NSD_X (NormalSetData.intersectKeysX keys X)))
          (FSet.inter
            (fromSetData (NormalSetData.from_NSD' keys EmptySD))
            (fromSetData (NormalSetData.from_NSD_X X))).
      Proof.
        induction keys as [ | k keys]; 
          intros X.
        * simpl. 
          intros z.
          rewrite FSetProperties.inter_iff.
          rewrite FSetProperties.empty_iff.
          tauto.
        * simpl.
          unfold NormalSetData.intersectKeysX in *.
          simpl.
          rewrite from_NSD_X_app.
          
          rewrite IHkeys.
          intros z.
          repeat rewrite FSetProperties.union_iff.
          repeat rewrite FSetProperties.inter_iff.
          repeat rewrite from_NSD'_iff.
          simpl.
          repeat rewrite FSetProperties.add_iff.
          rewrite FSetProperties.empty_iff.
          repeat rewrite NSD_X_iff.

          intuition.
          + destruct H0 as [Y [Hin1 Hin2]].
            rewrite List.in_map_iff in Hin1.
            destruct Hin1 as [Y0 [HinY1 HinY2]].
            subst.
            rewrite from_NSD_intersectKeyY in Hin2.
            rewrite FSetProperties.inter_iff in Hin2.
            rewrite FSetProperties.singleton_iff in Hin2.
            tauto.
          + destruct H0 as [Y [Hin1 Hin2]].
            rewrite List.in_map_iff in Hin1.
            destruct Hin1 as [Y0 [HinY1 HinY2]].
            subst.
            rewrite from_NSD_intersectKeyY in Hin2.
            repeat rewrite FSetProperties.inter_iff in Hin2.
            rewrite FSetProperties.singleton_iff in Hin2.
            exists Y0. tauto.
          + destruct H1 as [Y [Hin1 Hin2]].
            destruct (NormalSetData.key_in z keys) eqn:Hin.
            ++ right.
               rewrite key_in_iff.
               intuition.
               exists Y.
               tauto.
            ++ left. 
               exists (NormalSetData.intersectKeyY k Y).
               rewrite from_NSD_intersectKeyY.
               rewrite FSetProperties.inter_iff.
               rewrite FSetProperties.singleton_iff.
               intuition.
               rewrite List.in_map_iff.
               exists Y. split; auto.
      Qed.

      Lemma from_NSD_intersect : forall X1 X2,
        FSet.Equal
          (fromSetData (NormalSetData.from_NSD (NormalSetData.intersectSD X1 X2)))
          (fromSetData (IntersectSD (NormalSetData.from_NSD X1) (NormalSetData.from_NSD X2))).
      Proof.
        intros [keys1 Ys1] [keys2 Ys2]. simpl.
        intros z.
        rewrite from_NSD'_iff.
        rewrite intersectKeys_iff.
        repeat rewrite from_NSD_X_app.
        repeat rewrite FSetProperties.union_iff, FSetProperties.inter_iff.
        repeat rewrite FSetProperties.union_iff.
        rewrite from_NSD_intersect_X.
        repeat rewrite from_NSD'_iff.
        repeat rewrite from_NSD_intersectKeysX.
        repeat rewrite FSetProperties.inter_iff.
        repeat rewrite from_NSD'_iff.
        simpl. rewrite FSetProperties.empty_iff.
        tauto.
      Qed.

      Lemma to_from_NSD : forall D,
        FSet.Equal (fromSetData (NormalSetData.from_NSD (NormalSetData.to_NSD D)))
                  (fromSetData D).
      Proof.
        induction D.
        * simpl.
          intros z.
          rewrite FSetProperties.union_iff.
          rewrite FSetProperties.empty_iff.
          intuition.

        * simpl. reflexivity.
        * simpl. rewrite from_NSD_add.
          simpl. rewrite IHD. reflexivity.
        * simpl. rewrite from_NSD_remove.
          simpl. rewrite IHD.
          reflexivity.
        * simpl. rewrite from_NSD_union.
          simpl. rewrite IHD1, IHD2.
          reflexivity. 
        * simpl. rewrite from_NSD_intersect.
          simpl. rewrite IHD1, IHD2.
          reflexivity. 
      Qed.
    End Proof.


    Ltac reify_set e :=
    lazymatch e with
    | FSet.empty => constr:(EmptySD)
    | FSet.add ?x ?S =>
      let S' := reify_set S in
      constr:(AddSD x S')
    | FSet.remove ?x ?S =>
      let S' := reify_set S in
      constr:(RemoveSD x S')
    | FSet.union ?S1 ?S2 =>
      let S1' := reify_set S1 in
      let S2' := reify_set S2 in
      constr:(UnionSD S1' S2')
    | FSet.inter ?S1 ?S2 =>
      let S1' := reify_set S1 in
      let S2' := reify_set S2 in
      constr:(IntersectSD S1' S2')
    | _ => constr:(PrimSD e)
    end.

  Ltac reflect_set' :=
    match goal with
    | [ |- FSet.Equal ?X1 ?X2 ] =>
      let Y1 := reify_set X1 in
      let Y2 := reify_set X2 in
      try replace X1 with (fromSetData Y1) by reflexivity;
      try replace X2 with (fromSetData Y2) by reflexivity;
      try rewrite <- (Proof.to_from_NSD Y1);
      try rewrite <- (Proof.to_from_NSD Y2);
      simpl
    end.
  Ltac reflect_set :=
    reflect_set';
    try reflexivity;
    repeat Proofs.reduce_eq_dec; simpl;
    try reflexivity.

  Example reflect_set_union_empty (x : key) :
    FSet.Equal
      (FSet.union (FSet.add x FSet.empty) FSet.empty)
      (FSet.add x FSet.empty).
  Proof.
    reflect_set.
  Qed.

  Example reflect_set_intersect_empty (x : key) :
    FSet.Equal
      (FSet.inter (FSet.add x FSet.empty) FSet.empty)
      FSet.empty.
  Proof.
    reflect_set.
  Qed.
  

  Example reflect_set_intersect_shared_key (x : key) :
    FSet.Equal
      (FSet.inter (FSet.add x FSet.empty) (FSet.add x FSet.empty))
      (FSet.add x FSet.empty).
  Proof.
    reflect_set.
  Qed.

  Example reflect_set_remove_added_key (x : key) :
    FSet.Equal
      (FSet.remove x (FSet.add x FSet.empty))
      FSet.empty.
  Proof.
    reflect_set.
  Qed.

  Example reflect_set_remove_added_key' (x y : key) Z :
    ~ E.eq y x ->
    FSet.Equal
      (FSet.remove x (FSet.add y (FSet.add x Z)))
      (FSet.add y (FSet.remove x Z)).
  Proof.
    intros.
    reflect_set.
    Proofs.reduce_eq_dec; simpl.
    Proofs.reduce_eq_dec; simpl.
    reflexivity.
  Qed.

  Example reflect_set_opaque_union_empty (S : FSet.t) :
    FSet.Equal (FSet.union S FSet.empty) S.
  Proof.
    reflect_set.
  Qed.

  Example reflect_set_intersect_distributes
      (S1 S2 S3 : FSet.t) :
    FSet.Equal
      (FSet.inter (FSet.union S1 S2) S3)
      (FSet.union (FSet.inter S1 S3) (FSet.inter S2 S3)).
  Proof.
    reflect_set.
  Qed.

  Inductive MapData {A} :=
    | PrimD : M.t A -> MapData
    | EmptyD : MapData
    | AddD  : key -> A -> MapData -> MapData
    | RemoveD : key -> MapData -> MapData
    | SingletonD : key -> A -> MapData
    | ConcatD : MapData -> MapData -> MapData
    | SetMinusD : SetData -> MapData -> MapData.
  Arguments MapData A : clear implicits.

  Fixpoint fromMapData {A} (d : MapData A) : M.t A :=
    match d with
    | PrimD m => m
    | EmptyD => M.empty _
    | AddD x a M' => M.add x a (fromMapData M')
    | RemoveD x M' => M.remove x (fromMapData M')
    | SingletonD x a => M.add x a (M.empty _)
    | ConcatD M1 M2 => concat (fromMapData M1) (fromMapData M2)
    | SetMinusD X M' => setminus (fromSetData X) (fromMapData M')
    end.


  (** Normal form for maps, evaluated by [find]: a priority list of items;
      the first item that yields [Some] wins. *)
  Module NormalMapData.
    Inductive Item {A} :=
      | EntryI : key -> A -> Item
      | PrimI : M.t A -> list key -> Item. (* map with masked keys *)
    Arguments Item A : clear implicits.
    Definition NMD A := list (Item A).

    Definition evalItem {A} (it : Item A) (k : key) : option A :=
      match it with
      | EntryI x a => if E.eq_dec k x then Some a else None
      | PrimI p ms => if NormalSetData.key_in k ms then None else M.find k p
      end.

    Fixpoint lookup {A} (l : NMD A) (k : key) : option A :=
      match l with
      | [] => None
      | it :: l' =>
        match evalItem it k with
        | Some a => Some a
        | None => lookup l' k
        end
      end.

    Fixpoint removeN {A} (x : key) (l : NMD A) : NMD A :=
      match l with
      | [] => []
      | EntryI k a :: l' =>
        if E.eq_dec k x then removeN x l' else EntryI k a :: removeN x l'
      | PrimI p ms :: l' => PrimI p (x :: ms) :: removeN x l'
      end.

    Definition addN {A} (x : key) (a : A) (l : NMD A) : NMD A :=
      EntryI x a :: removeN x l.
    Arguments addN : simpl never.

    Definition concatN {A} (l1 l2 : NMD A) : NMD A := l1 ++ l2.

    Fixpoint norm {A} (d : MapData A) : NMD A :=
      match d with
      | PrimD m => [PrimI m []]
      | EmptyD => []
      | AddD x a d' => addN x a (norm d')
      | RemoveD x d' => removeN x (norm d')
      | SingletonD x a => [EntryI x a]
      | ConcatD d1 d2 => concatN (norm d1) (norm d2)
      | SetMinusD X d' => [PrimI (setminus (fromSetData X) (fromMapData d')) []]
      end.

    Lemma lookup_removeN : forall A (l : NMD A) x k,
      lookup (removeN x l) k = if E.eq_dec k x then None else lookup l k.
    Proof.
      induction l as [|[k' a|p ms] l IH]; intros x k; simpl.
      - destruct (E.eq_dec k x); auto.
      - destruct (E.eq_dec k' x) as [Hk'x|Hk'x].
        + rewrite IH.
          destruct (E.eq_dec k x) as [Hkx|Hkx]; auto.
          destruct (E.eq_dec k k') as [Hkk'|Hkk']; auto.
          exfalso. apply Hkx. eapply E.eq_trans; eauto.
        + simpl. destruct (E.eq_dec k k') as [Hkk'|Hkk'].
          * destruct (E.eq_dec k x) as [Hkx|Hkx]; auto.
            exfalso. apply Hk'x. eapply E.eq_trans; [apply E.eq_sym|]; eauto.
          * rewrite IH. reflexivity.
      - simpl. rewrite IH. destruct (E.eq_dec k x); reflexivity.
    Qed.

    Lemma lookup_app : forall A (l1 l2 : NMD A) k,
      lookup (l1 ++ l2) k = match lookup l1 k with Some a => Some a | None => lookup l2 k end.
    Proof.
      induction l1 as [|it l1 IH]; intros; simpl; auto.
      destruct (evalItem it k); auto.
    Qed.

    Lemma lookup_addN : forall A x (a : A) l k,
      lookup (addN x a l) k = if E.eq_dec k x then Some a else lookup l k.
    Proof.
      intros. unfold addN. simpl.
      destruct (E.eq_dec k x); auto.
      rewrite lookup_removeN. destruct (E.eq_dec k x); auto; contradiction.
    Qed.

    Lemma find_norm : forall A (d : MapData A) z,
      M.find z (fromMapData d) = lookup (norm d) z.
    Proof.
      induction d as [m| |k a d IHd|k d IHd|k a|d1 IHd1 d2 IHd2|X d IHd]; intros z; simpl norm; simpl fromMapData.
      - simpl lookup. destruct (M.find z m); reflexivity.
      - apply F.empty_o.
      - rewrite lookup_addN, F.add_o, <- IHd.
        destruct (E.eq_dec z k), (F.eq_dec k z); try reflexivity;
          exfalso; firstorder using E.eq_sym.
      - rewrite lookup_removeN, F.remove_o, <- IHd.
        destruct (E.eq_dec z k), (F.eq_dec k z); try reflexivity;
          exfalso; firstorder using E.eq_sym.
      - simpl lookup. rewrite F.add_o, F.empty_o.
        destruct (E.eq_dec z k), (F.eq_dec k z); try reflexivity;
          exfalso; firstorder using E.eq_sym.
      - unfold concatN. rewrite Proofs.concat_find, lookup_app, IHd1, IHd2. reflexivity.
      - simpl lookup. destruct (M.find z (setminus (fromSetData X) (fromMapData d)));
          reflexivity.
    Qed.

    Lemma equal_of_lookup : forall A (d1 d2 : MapData A),
      (forall k, lookup (norm d1) k = lookup (norm d2) k) ->
      M.Equal (fromMapData d1) (fromMapData d2).
    Proof.
      intros A d1 d2 H k. rewrite !find_norm. apply H.
    Qed.
  End NormalMapData.


    Ltac reify e :=
    lazymatch type of e with
    | M.t ?A =>
      lazymatch e with
      | M.empty _ => constr:(@EmptyD A)
      | M.add ?x ?a (M.empty _) => constr:(@SingletonD A x a)
      | M.add ?x ?a ?m =>
        let m' := reify m in
        constr:(@AddD A x a m')
      | M.remove ?x ?m =>
        let m' := reify m in
        constr:(@RemoveD A x m')
      | concat ?m1 ?m2 =>
        let m1' := reify m1 in
        let m2' := reify m2 in
        constr:(@ConcatD A m1' m2')
      | setminus ?S ?m =>
        let S' := reify_set S in
        let m' := reify m in
        constr:(@SetMinusD A S' m')
      | _ => constr:(@PrimD A e)
      end
    end.

  Ltac reflect_map' :=
    match goal with
    | [ |- M.Equal ?m1 ?m2 ] =>
      let d1 := reify m1 in
      let d2 := reify m2 in
      change (M.Equal (fromMapData d1) (fromMapData d2));
      apply NormalMapData.equal_of_lookup; intro z;
      simpl NormalMapData.norm; unfold NormalMapData.addN;
      simpl NormalMapData.removeN; simpl NormalMapData.lookup
    end.

  Ltac reflect_map :=
    reflect_map';
    repeat (Proofs.reduce_eq_dec; simpl);
    try reflexivity;
    try (exfalso; eauto using E.eq_sym, E.eq_trans).

  Example reflect_map_add_remove {A} (x : key) (a : A) (m : M.t A) :
    M.Equal (M.remove x (M.add x a m)) (M.remove x m).
  Proof. reflect_map. Qed.

  Example reflect_map_add_add {A} (x : key) (a b : A) (m : M.t A) :
    M.Equal (M.add x a (M.add x b m)) (M.add x a m).
  Proof. reflect_map. Qed.

  Example reflect_map_concat_empty {A} (m : M.t A) :
    M.Equal (concat m (M.empty A)) m.
  Proof. reflect_map. Qed.

  Example reflect_map_add_comm {A} (x y : key) (a b : A) (m : M.t A) :
    ~ E.eq x y ->
    M.Equal (M.add x a (M.add y b m)) (M.add y b (M.add x a m)).
  Proof.
    intros. reflect_map.
  Qed.

  Example reflect_map_concat_add {A} (x : key) (a : A) (m1 m2 : M.t A) :
    M.Equal (concat (M.add x a m1) m2) (M.add x a (concat m1 m2)).
  Proof. reflect_map. Qed.

  End Reflection.

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