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
From Qoreo.Network Require Import Network.
From Stdlib Require Import Morphisms (* for Proper *).

Module Label := Choreography.Label.
Module Choreography := Choreography.Choreography.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Stdlib.Structures.Equalities.
Import Actor.Map.Tactics.
From Qoreo.Network Require Import Proofs.



Notation "T '!' A" := (ChorEnv.find A T)
  (no associativity, at level 60).

From Qoreo.Network Require Import Soundness.

Lemma step_epp_eq : forall C T ρ l C' T' ρ',
    Choreography.step C T ρ l C' T' ρ' ->
    forall A,
    ~ Actor.FSet.In A (Label.actors l) ->
    epp A C' = epp A C (* /\ Var.Map.Equal (T'!A) (T!A).*).
Proof.
    intros ? ? ? ? ? ? ? Hstep.
    induction Hstep; intros A0 HA0;
      subst; simpl in *; auto;
      try rewrite IHHstep; auto.
    * (* LetVar *)
      rewrite epp_subst.
      Actor.simplify. 
      admit (* not equal, but equivalent up to letunit *).
    * (* LetBang *) 
      rewrite epp_subst.
      Actor.simplify. 
      admit (* not equal, but equivalent up to letunit *).
    * (* LetPair *)
      admit (* not equal, but equivalent *).
    * (* LetUnit *) admit (* again *).
    * Actor.simplify.
    * Actor.simplify.
    * Actor.simplify.
    * Actor.simplify.
    * Actor.simplify.
    * Actor.simplify.
      destruct (Actor.Map.FSetProofs.in_dec A0
                    (Actor.FSet.union (Choreography.actors C1)
                                      (Choreography.actors C2)))
        as [Hin | Hin].
      {
        (* contradiction *)
        contradict H2.
        rewrite H0.
        Actor.simplify.
      }
      (* need to also know that C1 and C2 have the same type;
         if A0 is not in either of them,
         then epp A0 C1 = epp A0 C2. *)
      admit.
Admitted.

Lemma completeness_local : forall G D T C tau,
    Choreography.WellTyped G D T C tau ->
    forall Θ ρ Θ' ρ' P' A,
    Process.step (epp A C) (Label.Internal Θ ρ Θ' ρ') P' ->
    Var.Map.Equal (T ! A) Θ ->
    ChorEnv.WellScoped T ρ ->

    (* one of two options: *)
    (* either C -A-> C' such that [C']_A = P' *)
    (* or C -l-> C' such that A ∉ l,
           in which case [C']_A = [C]_A *)
    exists l C' T' ρ',
        Choreography.step C T ρ l C' T' ρ'
        /\ 
        ((l = Label.Loc A /\ epp A C' = P')
        \/ ~ Actor.FSet.In A (Label.actors l)).
Proof.
    intros ? ? ? ? ? HWT.
    induction HWT;
      intros Θ ρ Θ' ρ' P' A0 Hstep HT HWS;
      simpl in *.
    * (* LetIn *)
      inversion Hstep; subst; clear Hstep.
      + (* LetInC *)
        apply IHHWT1 in H9; auto.
        2:{ admit (* true *). }
        2:{ admit (* true *). }
        destruct H9 as [l [C1' [T' [ρ'' [Hstep IH]]]]].
        exists l.
        exists (Choreography.LetIn p C1' C2).
        exists T' (* not quite T', should be a subset *).
        exists  ρ''.
        split.
        { apply Choreography.LetInC; auto. admit (* almost *). }
        destruct IH as [[Hl HP1'] | Hnin];
          subst; auto.

      + (* LetInB *)
        (* By choreography progess (add well-typed assumption),
           either C1 is a value, or it can take a step.
           If C1 is a value, then (LetIn p C1 C2 -> something)
           Otherwise, (second case) it can take a step. 
        *)
        admit.

    * 
      Actor.Map.Tactics.compare A0 A.
      2:{ inversion Hstep. }
      inversion Hstep; subst; clear Hstep.
      (* e -> e' *)
      exists (Label.Loc A0).
      exists (Choreography.Loc A0 e').
      exists (Actor.Map.add A0 Θ' T).
      exists ρ'.
      split.
      { eapply Choreography.LocC; eauto.
        2:{ reflexivity. }
        rewrite HT; auto.
      }
      left. split; auto.
      simpl. Actor.simplify.

    * (* Unit *) inversion Hstep.
    * (* Pair *)
      inversion Hstep; subst; clear Hstep.
      + (* C1 *)
        apply IHHWT1 in H5.
        2:{ admit (* true? *). }
        2:{ admit (* true *). }
        destruct H5 as [l [C1' [T1' [ρ1' [Hstep IH]]]]].
        exists l; exists (Choreography.Pair C1' C2).
        exists T1' (* not quite*).
        exists ρ1'.
        split.
        { apply Choreography.PairC1; auto. admit (* almost *). }
        simpl. 
        destruct IH as [[? ?] | ?]; subst; auto.
      + (* C2 *)
        admit (* same as C1 *).

    * (* Bang *)
      Actor.Map.Tactics.compare A0 A;
      Actor.Map.Tactics.compare A0 B.
      {
        inversion Hstep; subst; clear Hstep.
        exists (Choreography.Label.Loc A0).
        exists (Choreography.Send A0 e' A0).
        exists (Actor.Map.add A0 Θ' T).
        exists ρ'.
        split.
        { eapply Choreography.SendC; eauto.
            rewrite HT. eauto.
            reflexivity.
        }
        left. split; auto. simpl. Actor.simplify.
      }
      { inversion Hstep; subst; clear Hstep.
        exists (Choreography.Label.Loc A0).
        exists (Choreography.Send A0 e' B).
        exists (Actor.Map.add A0 Θ' T).
        exists ρ'.
        split.
        { eapply Choreography.SendC; eauto.
            rewrite HT. eauto.
            reflexivity.
        }
        left. split; auto. simpl. Actor.simplify.
      }
      { inversion Hstep. }
      { inversion Hstep. }

    * (* EPR *)
      (* Hstep can never step via an Internal step *)
      exfalso.
      Actor.Map.Tactics.compare A0 A;
      Actor.Map.Tactics.compare A0 B;
      subst;
      repeat match goal with
      | [ Hstep : Process.step _ _ _ |- _] =>
        inversion Hstep; subst; clear Hstep
      end.

    * Actor.Map.Tactics.compare A0 A.
      {
        inversion Hstep; subst; clear Hstep.
        exists (Label.Loc A0).
        exists (Choreography.If A0 e' C1 C2).
        eexists. exists ρ'.
        split.
        { eapply Choreography.IfC; eauto.
          admit. reflexivity.
        }
        left. split; auto.
        simpl. Actor.simplify.
      }
      destruct (Actor.Map.FSetProofs.in_dec A0
                  (Actor.FSet.union (Choreography.actors C1)
                                    (Choreography.actors C2)))
            as [Hin | Hin].
      { inversion Hstep. }
      {
        exfalso.
        (* (epp A0 C1) will only possibly take a step as a
           unit-equivalence... *)
        admit.
      }


Admitted.

Lemma send_completeness : forall C A B v PA' PB' T ρ,
    A <> B ->
    Process.step (epp A C) (Network.Label.Send v B) PA' ->
    Process.step (epp B C) (Network.Label.Receive A v) PB' ->
    exists C',
        (forall D, epp D C' = if Actor.eq_dec D A then PA' else if Actor.eq_dec D B then PB' else epp D C)
        /\ Choreography.step C T ρ (Choreography.Label.Send A v B) C' T ρ.
Proof.
    induction C; intros A B v PA' PB' T ρ ? HstepA HstepB;
      simpl in *.
    * inversion HstepA; subst; clear HstepA.
      inversion HstepB; subst; clear HstepB.
      edestruct IHC1 with (T := T) (ρ := ρ)
        as [C1' [HP Hstep']];
        eauto; subst.
      exists (Choreography.LetIn t C1' C2).
      repeat split; simpl; subst; auto.
      2:{ apply Choreography.LetInC; auto. }
      {
        intros D. rewrite HP.
        Actor.simplify.
      }

    * repeat Actor.Map.Tactics.reduce_eq_dec;
      inversion HstepA; subst; clear HstepA.
    * inversion HstepA.
    * (* Pair *) admit.
    * (* Send *)
      repeat Actor.Map.Tactics.reduce_eq_dec;
      try (inversion HstepA; fail);
      try (inversion HstepB; fail).
      inversion HstepA; subst; clear HstepA.
      inversion HstepB; subst; clear HstepB.
      exists (Choreography.Loc B v).
      repeat split; simpl; Actor.simplify; auto.
      2:{ apply Choreography.SendB; auto. reflexivity. }
      { intros D. Actor.simplify. }

    * (* EPR *) 
      repeat Actor.Map.Tactics.reduce_eq_dec;
      repeat match goal with
      | [ H : Process.step _ _ _ |- _ ] => inversion H; subst; clear H
      end.

    * (* If *) 
      repeat Actor.Map.Tactics.reduce_eq_dec.
      inversion HstepB.
      inversion HstepA.
      destruct (Actor.Map.FSetProofs.in_dec A
                  (Actor.FSet.union (Choreography.actors C1)
                                    (Choreography.actors C2)))
        as [Hin | Hin].
      { inversion HstepA. }
      destruct (Actor.Map.FSetProofs.in_dec B
                  (Actor.FSet.union (Choreography.actors C1)
                                    (Choreography.actors C2)))
        as [Hin' | Hin'].
      inversion HstepB.
      edestruct IHC1 with (T := T) (ρ := ρ) (A := A) (B := B); eauto.
      admit (* no this is not right. It's a problem with epp for if *).

Admitted.


Theorem completeness : forall N T ρ l N' T' ρ',

    Network.step N T ρ l N' T' ρ' ->

    forall C,
    EPP_N C N ->
    (forall D, Actor.FSet.In D (Choreography.actors C) -> Actor.Map.In D N) ->
    exists C', EPP_N C' N' /\
                Choreography.step C T ρ l C' T' ρ' /\
                (forall D, Actor.FSet.In D (Choreography.actors C') -> Actor.Map.In D N').
Proof.
    intros ? ? ? ? ? ? ? Hstep.
    induction Hstep; intros ? HEPP Hin.
    * (* Internal *) admit (* need to restate lemma *).
    * (* Send *)
      subst.
      edestruct send_completeness
        with (A := A) (B := B) (T := refs) (ρ := cfg)
        as [C' [HP Hstep']]; eauto.
      { (* what if A = B? this should be impossible, process.step should be deterministic-ish *) admit. }

      + rewrite EPP_N_spec in HEPP.
        erewrite HEPP; eauto.
      
      + rewrite EPP_N_spec in HEPP.
        erewrite HEPP; eauto.

      + subst.
        exists C'.
        repeat split; auto.
        { rewrite H4. rewrite EPP_N_spec.
          intros D PD HD.
          rewrite HP.
          Actor.Map.Tactics.compare A D;
            [Actor.simplify | ].
          Actor.Map.Tactics.compare B D;
            [Actor.simplify | ].
          Actor.simplify.
          rewrite EPP_N_spec in HEPP.
          apply HEPP.
          tauto.
        }
        { rewrite H5. auto. }
        { (* actors C = actors C *) admit. }
      
    * (* EPR *) 
      admit.
    * (* If *) admit.
Admitted.
