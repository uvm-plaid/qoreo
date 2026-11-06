From Qoreo.Base Require Var Actor Config ChorEnv.
From Qoreo.Expr Require Expr BaseProofs.
From Qoreo.Choreography Require Choreography.

From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms (* for Proper *).
Require Import Stdlib.Program.Equality.

From Qoreo.Base Require Var Config ChorEnv.
From Qoreo.Expr Require Expr.
From Qoreo.Choreography Require Choreography.
From Qoreo.Network Require Import Network Proofs.
From Stdlib Require Import Morphisms (* for Proper *).

Module Label := Choreography.Label.
Module Choreography := Choreography.Choreography.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Stdlib.Structures.Equalities.
Import Actor.Map.Tactics.
Import Choreography.

Import ChorEnv.Notation.
Open Scope qoreo_scope.

Lemma epp_in_pat : forall p x A,
    Pattern.in_pat x (Pattern.epp A p) 
    = Choreography.Pattern.in_pat A x p.
Proof.
    induction p; intros x A; simpl; auto.
    * Actor.Map.Tactics.reduce_eq_dec; subst; auto.
    * Actor.Map.Tactics.reduce_eq_dec; subst; simpl;
        auto.
      Var.Map.Tactics.reduce_eq_dec; subst; auto.
    * rewrite IHp1, IHp2; auto.
    * Actor.Map.Tactics.reduce_eq_dec; subst; auto.
Qed.


Lemma actors_subst : forall C A x v,
    Choreography.actors (subst A x v C)
    = Choreography.actors C.
Proof.
    induction C; intros A x v; simpl; auto;
      try rewrite IHC1;
      try rewrite IHC2;
      auto.
    * destruct (Choreography.Pattern.in_pat A x t0); auto.
      rewrite IHC2; auto.
Qed.

Lemma epp_subst : forall C A B x v,
    epp B (Choreography.subst A x v C)
    = if Actor.eq_dec A B
      then Process.subst x v (epp B C)
      else epp B C.
Proof.
    induction C; intros A B x v; simpl; auto;
        try (repeat Actor.Map.Tactics.reduce_eq_dec;
             subst; auto; fail).
    * (* LetIn *)
      rewrite IHC1.
      rewrite epp_in_pat.
      Actor.Map.Tactics.compare A B;
        destruct (Choreography.Pattern.in_pat A x t0) eqn:Hin;
        auto;
        try rewrite IHC2;
        Actor.simplify.
    * rewrite IHC1.
      Actor.Map.Tactics.compare A B;
        try rewrite IHC2; auto;
        Actor.simplify.
    * rewrite IHC1.
      repeat Actor.Map.Tactics.reduce_eq_dec;
        simpl; auto;
        repeat rewrite actors_subst;
        repeat rewrite IHC2;
        Actor.simplify.
      match goal with
      | [ |- context[Actor.Map.FSetProofs.in_dec ?A ?X]] =>
        destruct (Actor.Map.FSetProofs.in_dec A X)
          as [Hin | Hin]
      end; auto.
Qed.

Lemma epp_val : forall A C,
    Choreography.Val C ->
    Process.Val (epp A C).
Proof.
    intros ? C HC.
    induction HC; simpl;
      try constructor; auto.
    Actor.simplify; constructor; auto.
Qed.

Lemma soundness_local : forall C A refs cfg C' refs' cfg',
    Choreography.step C refs cfg (Label.Loc A) C' refs' cfg' ->
    Process.step (epp A C) (Label.Internal (refs!!A) cfg (refs'!!A) cfg') (epp A C').
Proof.
    intros ? ? ? ? ? ? ? Hstep.
    dependent induction Hstep; simpl.
    * constructor; auto.
    * Actor.simplify.
      rewrite epp_subst. Actor.simplify.
      apply Process.LetInB; simpl; auto.
      { constructor; auto. }
    * rewrite epp_subst. Actor.simplify. 
      apply Process.LetInB; simpl; auto.
      repeat constructor.
    * (* DELAY *)
      (* A ∉ actors p  ==> Pattern.epp A p = unit-ish *)
      (* Doesn't actually step to the thing, but is equivalent to the thing. *)
      admit.
    * Actor.simplify.
      rewrite H0. ChorEnv.simplify.
      constructor; auto.
    * apply Process.PairC1; auto.
    * apply Process.PairC2; auto.
      apply epp_val; auto.
    * rewrite H0. ChorEnv.simplify; subst.
      { constructor; auto. }
      { constructor; auto. }
    * Actor.simplify.
      rewrite H0.
      ChorEnv.simplify.
      constructor; auto.
Admitted.

Lemma soundness_send : forall C A e B refs cfg C' refs' cfg',
    Choreography.step C refs cfg (Choreography.Label.Send A e B) C' refs' cfg' ->
    Process.step (epp A C) (Network.Label.Send e B) (epp A C').
Proof.
  intros ? ? ? ? ? ? ? ? ? Hstep.
  dependent induction Hstep; simpl.
  * apply Process.LetInC; auto.
  * admit (* delay rule *).
  * apply Process.PairC1; auto.
  * apply Process.PairC2; auto.
    apply epp_val; auto.
  * Actor.Map.Tactics.reduce_eq_dec. 
    Actor.Map.Tactics.reduce_eq_dec.
    + (* self-send... *) admit.
    + apply Process.SendB; auto.
Admitted.

Lemma soundness_receive : forall C A e B refs cfg C' refs' cfg',
    Choreography.step C refs cfg (Choreography.Label.Send A e B) C' refs' cfg' ->
    Process.step (epp B C) (Network.Label.Receive A e) (epp B C').
Proof.
  intros ? ? ? ? ? ? ? ? ? Hstep.
  dependent induction Hstep; simpl.
  * apply Process.LetInC; auto.
  * admit (* delay rule *).
  * apply Process.PairC1; auto.
  * apply Process.PairC2; auto.
    apply epp_val; auto.
  * Actor.simplify. 
    + (* self-send... *) admit.
    + apply Process.ReceiveB; auto.
Admitted.  

Lemma epp_not_in_eq : forall C refs cfg l C' refs' cfg' A,
  Choreography.step C refs cfg l C' refs' cfg' ->
  ~ Actor.FSet.In A (Choreography.Label.actors l) ->
  epp A C' = epp A C.
Admitted.

Theorem soundness : forall l C C' refs cfg refs' cfg',
    Choreography.step C refs cfg l C' refs' cfg' ->
    forall N,
      (forall D, Actor.FSet.In D (Choreography.Label.actors l) -> Actor.Map.In D N) ->
      EPP_N C N ->
    exists N', Network.step N refs cfg l N' refs' cfg'
              /\ EPP_N C'  N'.
Proof.
  destruct l as [A e B | | | | ]; intros.
  * (* Send *)
    exists (Actor.Map.add A (epp A C') (Actor.Map.add B (epp B C') N)).
    split.
    2:{
      apply Network.Proofs.EPP_N_spec.
      intros D PD HD.
      Actor.simplify.
      destruct HD as [[? ?] | HD]; subst; auto.
      destruct HD as [? [[? ?] | [? HD]]]; subst; auto.
      erewrite epp_not_in_eq; eauto.
      2:{ simpl. Actor.simplify. }
      rewrite Network.Proofs.EPP_N_spec in H1.
      apply H1; auto.
    }
    eapply Network.Send.
    4:{ eapply soundness_send; eauto. }
    4:{ eapply soundness_receive; eauto. }
    4:{ reflexivity. }

Admitted.