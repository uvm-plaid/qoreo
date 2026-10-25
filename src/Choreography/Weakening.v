From Qoreo.Base Require Import Var.
From Qoreo.Expr Require Expr BaseProofs Weakening Preservation.
From Qoreo.Choreography Require Import Choreography BaseProofs Lemmas.
Import HelperLemmas.



(** * Proofs about well-typedness *)
Lemma wt_disjoint : forall C A G D T tau,
    WellTyped G D T C tau ->
    Var.Map.Properties.Disjoint (ChorEnv.find A G) (ChorEnv.find A D).
Proof.
  intros ? ? ? ? ? ? HWT.
  induction HWT; ChorEnv.simplify.
  * ChorEnv.specialize_partition A.
    Var.Map.Tactics.reflect_partition.
    Var.Map.Tactics.rewrite_map (D ! A).
    Var.Map.Tactics.rewrite_map (D' ! A).
    Var.Map.Tactics.rewrite_map (G' ! A).
    Var.simplify.
  * Actor.Map.Tactics.compare A A0.
    { (* A = A0 *)
      eapply BaseProofs.wt_disjoint; eauto.
    }
    { (* A <> A0 *)
      ChorEnv.specialize_with A.
      Actor.simplify.
      assert (HD : Var.Map.Empty (D!A)) by auto.
      apply Var.Map.Proofs.empty_map_equal in HD.
      rewrite HD.
      Var.simplify.
    }
  * ChorEnv.specialize_with A.
    Var.Map.Tactics.rewrite_map (D!A).
    Var.simplify.
  * ChorEnv.specialize_partition A.
    Var.Map.Tactics.reflect_partition.
    Var.Map.Tactics.rewrite_map (D ! A).
    Var.simplify.
  * Actor.Map.Tactics.compare A A0.
    { (* A = A0 *)
      eapply BaseProofs.wt_disjoint; eauto.
    }
    { (* A <> A0 *)
      ChorEnv.specialize_with A.
      Actor.simplify.
      assert (HD : Var.Map.Empty (D!A)) by auto.
      apply Var.Map.Proofs.empty_map_equal in HD.
      rewrite HD.
      Var.simplify.
    }

  * ChorEnv.specialize_with A.
    Var.Map.Tactics.rewrite_map (D!A).
    Var.simplify.
  * Actor.Map.Tactics.compare A A0.
    { (* A = A0 *)
      ChorEnv.specialize_with A.
      ChorEnv.simplify.
      Var.Map.Tactics.reflect_partition.
      Var.Map.Tactics.rewrite_map (D!A).
      Var.simplify.
      split; auto. 

      eapply BaseProofs.wt_disjoint; eauto.
    }
    { (* A <> A0 *)
      ChorEnv.specialize_with A.
      ChorEnv.simplify.
      Var.Map.Tactics.rewrite_map (D!A).
      auto.
    }
Qed.


Lemma weakening_gen : forall C G D T tau,
    WellTyped G D T C tau ->
    forall G' G0,
      (forall A0,
          (Var.Map.Partition (ChorEnv.find A0 G') (ChorEnv.find A0 G) (ChorEnv.find A0 G0)) /\
          (Var.Map.Properties.Disjoint (ChorEnv.find A0 G0) (ChorEnv.find A0 D))) ->
      WellTyped G' D T C tau.
  Proof.
    intros C G D T tau HWT.
    induction HWT; intros G0' G0 HE.
    (*

    - eapply Nil; eauto.

    - eapply EPR; [assumption | | assumption | assumption].
      apply (IHHWT
               (ChorEnv.remove B y (ChorEnv.remove A x G0))
               (ChorEnv.remove B y (ChorEnv.remove A x G'))).
      intros A0.
      destruct (HE A0) as [HEpart HEdisj].
      split.
      + pose proof (partition_remove_all G' G G0 A0 A x HEpart)
          as HEpart_x.
        apply (partition_remove_all
                 (ChorEnv.remove A x G')
                 (ChorEnv.remove A x G)
                 (ChorEnv.remove A x G0)
                 A0 B y HEpart_x).
      + pose proof (remove_add_dj_env G0 D A0 A x Expr.QUBIT HEdisj)
          as HEdisj_x.
        apply (remove_add_dj_env
                 (ChorEnv.remove A x G0)
                 (ChorEnv.add A x Expr.QUBIT D)
                 A0 B y Expr.QUBIT HEdisj_x).

    (* Send *)
    - destruct (HE A) as [HEA HEB].
      pose proof (partition_dj
                    (ChorEnv.find A G0) (ChorEnv.find A D)
                    DeltaA1 DeltaA2 HEB H1) as HPDJ.
      pose proof (Expr.Weakening.weakening_gen
                    (ChorEnv.find A G0) (ChorEnv.find A G)
                    DeltaA1 ThetaA1 e (Expr.BANG tau) H0
                    (ChorEnv.find A G') HEA HPDJ) as HEWG.
      eapply Send.
      { assumption. }
      { exact HEWG. }
      { apply (IHHWT
                 (ChorEnv.remove B y G0)
                 (ChorEnv.add B y tau G')).
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split.
        { apply (map_subset_add A0 B y tau G' G G0 HEpart). }
        { pose proof
            (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEdisj H1)
            as Hpdje.
          apply (remove_dj_env G0 (Actor.Map.add A DeltaA2 D)
                               A0 B y Hpdje). }
      }
      { assumption. }
      { assumption. }

    (* LetBang *)
    - destruct (HE A) as [HEA HEB].
      pose proof (partition_dj
                    (ChorEnv.find A G0) (ChorEnv.find A D)
                    DeltaA1 DeltaA2 HEB H0) as HPDJ.
      pose proof (Expr.Weakening.weakening_gen
                    (ChorEnv.find A G0) (ChorEnv.find A G)
                    DeltaA1 ThetaA1 e (Expr.BANG tau) H
                    (ChorEnv.find A G') HEA HPDJ) as HEWG.
      eapply LetBang.
      { exact HEWG. }
      { apply (IHHWT
                 (ChorEnv.remove A x G0)
                 (ChorEnv.add A x tau G')).
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split.
        { apply (map_subset_add A0 A x tau G' G G0 HEpart). }
        { pose proof
            (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEdisj H0)
            as Hpdje.
          apply (remove_dj_env G0 (Actor.Map.add A DeltaA2 D)
                               A0 A x Hpdje). }
      }
      { assumption. }
      { assumption. }

    (* LetIn: weaken the expression with partition_dj. Apply the tail induction
       hypothesis after removing the bound variable from G and adding it to D.
       Use partition_remove_all, partition_dj_env, remove_add_dj_env, and
       addadd8 to prove the transformed context conditions. *)
    - destruct (HE A) as [HEAA HEAB].
      pose proof (partition_dj
                    (ChorEnv.find A G0) (ChorEnv.find A D)
                    DeltaA1 DeltaA2 HEAB H0) as Hpdj.
      eapply LetIn.
      { eapply (Expr.Weakening.weakening_gen
                  (ChorEnv.find A G0)
                  (ChorEnv.find A G)
                  DeltaA1 ThetaA1 e tau H
                  (ChorEnv.find A G') HEAA Hpdj). }
      { apply (IHHWT
                 (ChorEnv.remove A x G0)
                 (ChorEnv.remove A x G')).
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split.
        { apply (partition_remove_all G' G G0 A0 A x HEpart). }
        { pose proof
            (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEdisj H0)
            as Hpdje.
          rewrite (addadd8 D A x tau DeltaA2).
          pose proof
            (remove_add_dj_env G0 (Actor.Map.add A DeltaA2 D)
                               A0 A x tau Hpdje) as Htail_disj.
          exact Htail_disj. }
      }
      { assumption. }
      { assumption. }
      { assumption. }

    (* LetPair *)
    - destruct (HE A) as [HEAA HEAB].
      pose proof (partition_dj
                    (ChorEnv.find A G0) (ChorEnv.find A D)
                    DeltaA1 DeltaA2 HEAB H0) as Hpdj.
      eapply LetPair.
      { eapply (Expr.Weakening.weakening_gen
                  (ChorEnv.find A G0)
                  (ChorEnv.find A G)
                  DeltaA1 ThetaA1 e (Expr.Tensor tau1 tau2) H
                  (ChorEnv.find A G') HEAA Hpdj). }
      { apply (IHHWT
                 (ChorEnv.remove A x1 (ChorEnv.remove A x2 G0))
                 (ChorEnv.remove A x1 (ChorEnv.remove A x2 G'))).
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split.
        { pose proof (partition_remove_all G' G G0 A0 A x2 HEpart)
            as HEpart_x2.
          apply (partition_remove_all
                   (ChorEnv.remove A x2 G')
                   (ChorEnv.remove A x2 G)
                   (ChorEnv.remove A x2 G0)
                   A0 A x1 HEpart_x2). }
        { rewrite (addadd8 D A x1 tau1
                     (Var.Map.add x2 tau2 DeltaA2)).
          rewrite (addadd8 D A x2 tau2 DeltaA2).
          pose proof
            (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEdisj H0)
            as Hpdje.
          pose proof
            (remove_add_dj_env G0 (Actor.Map.add A DeltaA2 D)
                               A0 A x2 tau2 Hpdje) as Hpdj_x2.
          apply (remove_add_dj_env
                   (ChorEnv.remove A x2 G0)
                   (ChorEnv.add A x2 tau2 (Actor.Map.add A DeltaA2 D))
                   A0 A x1 tau1 Hpdj_x2). }
      }
      { assumption. }
      { assumption. }
      { assumption. }
      { assumption. }
      { assumption. }

    (* If *)
    - destruct (HE A) as [HEA HEB].
    (*
      pose proof (partition_dj
                    (ChorEnv.find A G0) (ChorEnv.find A D)
                    DeltaA1 DeltaA' HEB H0) as HPDJ.
      pose proof (Expr.Weakening.weakening_gen
                    (ChorEnv.find A G0) (ChorEnv.find A G)
                    DeltaA1 ThetaA1 e Expr.BIT H
                    (ChorEnv.find A G') HEA HPDJ) as HEWG.
      pose proof
        (partitioning (ChorEnv.find A D) DeltaA2 DeltaA1 DeltaA' DeltaA3
                      H0 H1)
        as [Hpart12 [Hpart13 [HpartD3 HpartD2]]].
      assert (HpartD2' :
        Var.Map.Partition (ChorEnv.find A D)
          (Var.Map.concat DeltaA1 DeltaA3) DeltaA2).
      {
        Var.Map.Tactics.reflect_partition.
        { apply Var.Map.Proofs.disjoint_sym; auto. }
        { rewrite Heq0.
          repeat rewrite <- Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym DeltaA2 DeltaA3); auto.
          reflexivity.
        }
          
      }*)

      eapply If; eauto.
      + eapply Expr.Weakening.weakening_gen; eauto.
        ChorEnv.simplify.
        ChorEnv.specialize_partition A.
        autorewrite with var_db in *.
        Var.Map.Tactics.reflect_partition.
        Var.Map.Tactics.rewrite_map (D ! A).
        Var.simplify.
        
      + eapply IHHWT1.
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split; eauto.

        (* Want: G0!A0 ⊥ D'!A0
          Know:
            G0!A0 ⊥ D!A0
            D = (A ↦ DeltaA) ++ D' ++ D''
          So:
            G0!A0 ⊥ D'!A0
            G0!A0 ⊥ D''!A0
        *)

        ChorEnv.specialize_partition A0.
        Var.Map.Tactics.reflect_partition.

        Var.Map.Tactics.rewrite_map (D!A0).
        Var.Map.Tactics.rewrite_map (M0!A0).
        Var.simplify.

      + eapply IHHWT2.
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split; eauto.

        (* Want: G0!A0 ⊥ D'!A0
          Know:
            G0!A0 ⊥ D!A0
            D = (A ↦ DeltaA) ++ D' ++ D''
          So:
            G0!A0 ⊥ D'!A0
            G0!A0 ⊥ D''!A0
        *)

        ChorEnv.specialize_partition A0.
        Var.Map.Tactics.reflect_partition.

        Var.Map.Tactics.rewrite_map (D!A0).
        Var.Map.Tactics.rewrite_map (M0!A0).
        Var.simplify.

      + eapply IHHWT3.
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split; eauto.

        (* Want: G0!A0 ⊥ D''!A0
          Know:
            G0!A0 ⊥ D!A0
            D = (A ↦ DeltaA) ++ D' ++ D''
          So:
            G0!A0 ⊥ D'!A0
            G0!A0 ⊥ D''!A0
        *)

        ChorEnv.specialize_partition A0.
        Var.Map.Tactics.reflect_partition.

        Var.Map.Tactics.rewrite_map (D!A0).
        Var.Map.Tactics.rewrite_map (M0!A0).
        Var.simplify.
        *)
  Admitted.



(** Weakening *)
(*
Lemma cfg_weakening_stepC :
  forall I C T T' cfg l I' cfg' Theta A0,
    Insn.stepC I T cfg l I' T' cfg' ->
    Label.WellFormed l ->
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T) ->
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T') ->
    step (Choreography.Do I C)
      (Actor.Map.add A0
        (Var.Map.concat Theta (ChorEnv.find A0 T)) T)
      cfg l
      (Choreography.Do I' C)
      (Actor.Map.add A0
        (Var.Map.concat Theta (ChorEnv.find A0 T')) T')
      cfg'.
(* Proof outline: invert stepC. Reuse old expression-step weakening
   tactics for SendC, LetC, LetBangC, and LetPairC.
*)
Proof.
  intros ? ? ? ? ? ? ? ? ? ? Hstep.
  inversion Hstep; subst; clear Hstep;
    intros HWF Hdisj Hdisj'.
  * (* SendC *)
    rewrite H0 in *; clear T' H0.
    Actor.Map.Tactics.compare A A0.
    + ChorEnv.simplify.
      apply StepC.
      apply Insn.SendC with (TA' := (Var.Map.concat Theta TA')).
      2:{ intros D. ChorEnv.simplify. }

      eapply Expr.Preservation.cfg_weakening_2; eauto.
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }

    + (* A0 <> A *)
      ChorEnv.simplify.
      apply StepC.
      eapply Insn.SendC with (TA' := TA').
      2:{ intros D. ChorEnv.simplify. }
      ChorEnv.simplify.

  * (* LetC *)

    rewrite H0 in *; clear T' H0.
    Actor.Map.Tactics.compare A A0.
    + ChorEnv.simplify.
      constructor.
      econstructor; eauto.
      2:{ ChorEnv.simplify. }

      eapply Expr.Preservation.cfg_weakening_2; eauto.
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }

    + (* A0 <> A *)
      ChorEnv.simplify.
      apply StepC.
      eapply Insn.LetC with (TA' := TA').
      2:{ intros D. ChorEnv.simplify. }
      ChorEnv.simplify.

  * (* LetBangC *) 
    rewrite H0 in *; clear T' H0.
    Actor.Map.Tactics.compare A A0.
    + ChorEnv.simplify.
      apply StepC.
      econstructor; eauto.
      2:{ ChorEnv.simplify. }

      eapply Expr.Preservation.cfg_weakening_2; eauto.
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }

    + (* A0 <> A *)
      ChorEnv.simplify.
      apply StepC.
      eapply Insn.LetBangC with (TA' := TA').
      2:{ intros D. ChorEnv.simplify. }
      ChorEnv.simplify.

  * (* LetPairC *)
    rewrite H0 in *; clear T' H0.
    Actor.Map.Tactics.compare A A0.
    + ChorEnv.simplify.
      apply StepC.
      econstructor; eauto.
      2:{ ChorEnv.simplify. }

      eapply Expr.Preservation.cfg_weakening_2; eauto.
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
    + (* A0 <> A *)
      ChorEnv.simplify.
      apply StepC.
      eapply Insn.LetPairC with (TA' := TA').
      2:{ intros D. ChorEnv.simplify. }
      ChorEnv.simplify.
Qed.

Lemma cfg_weakening_stepB :
  forall C T T' cfg l C' cfg' Theta A0,
    stepB C T cfg l C' T' cfg' ->
    Label.WellFormed l ->
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T) ->
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T') ->
    step C
      (Actor.Map.add A0
        (Var.Map.concat Theta (ChorEnv.find A0 T)) T)
      cfg l C'
      (Actor.Map.add A0
        (Var.Map.concat Theta (ChorEnv.find A0 T')) T')
      cfg'.
(* Proof outline: invert stepB. Reuse old beta-case tactics; handle
   IfB by preserving the environment and configuration.
*)
Proof.
  intros ? ? ? ? ? ? ? ? ? Hstep ? ? ?.
  apply StepB.
  inversion Hstep; subst; clear Hstep;
    try match goal with
    | [ H : ChorEnv.Equal ?T ?T' |- _ ] =>
      rewrite H in *; clear T H
    end;
    try (econstructor; eauto; reflexivity).
  * (* EPR *)
    inversion H; subst; clear H.
    econstructor; eauto.
    { 
      unfold ChorEnv.epr in *.
      destruct (Config.epr_cfg cfg) as [[idx1 idx2] cfg0] eqn:Hepr.
      inversion H2; subst; clear H2.
      reflexivity.
    }
    {
      intros D.
      repeat (rewrite ChorEnv.find_add).
      inversion H2; subst; clear H2.
      Actor.Map.Tactics.reduce_eq_dec.
      {
        ChorEnv.simplify.
        Var.solve.
      }
      {
        ChorEnv.simplify.
        Var.solve.
      }
    }

  * (* EPR *)
    inversion H; subst; clear H.
    econstructor; eauto.
    { 
      unfold ChorEnv.epr in *.
      destruct (Config.epr_cfg cfg) as [[idx1 idx2] cfg0] eqn:Hepr.
      inversion H2; subst; clear H2.
      reflexivity.
    }
    {
      intros D.
      repeat (rewrite ChorEnv.find_add).
      inversion H2; subst; clear H2.
      Actor.Map.Tactics.reduce_eq_dec.
      {
        ChorEnv.simplify.
        Var.solve.
      }
      {
        ChorEnv.simplify.
        Var.solve.
      }
    }
Qed.

Lemma cfg_weakening_IfC :
  forall TA' A e C1 C2 C0 T cfg e' T' cfg' Theta A0,
    Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->
    ChorEnv.Equal T' (Actor.Map.add A TA' T) ->
    Label.WellFormed (Label.Loc A) ->
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T) ->
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T') ->
    step (Choreography.If A e C1 C2 C0)
      (Actor.Map.add A0
        (Var.Map.concat Theta (ChorEnv.find A0 T)) T)
      cfg (Label.Loc A)
      (Choreography.If A e' C1 C2 C0)
      (Actor.Map.add A0
        (Var.Map.concat Theta (ChorEnv.find A0 T')) T')
      cfg'.
Proof.
  intros.
  rewrite H0 in *; clear T' H0.
  Actor.Map.Tactics.compare A A0.
    + ChorEnv.simplify.
      eapply IfC.
      2:{ ChorEnv.simplify. }

      eapply Expr.Preservation.cfg_weakening_2; eauto.
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
    + (* A0 <> A *)
      ChorEnv.simplify.
      eapply IfC with (TA' := TA').
      { ChorEnv.simplify. }
      { intros D. ChorEnv.simplify. }
Qed.
*)

Lemma cfg_weakening' : forall C T1 cfg l C' T1' cfg',
    step C T1 cfg l C' T1' cfg' ->

    Label.WellFormed l ->
    forall T2 T2' Theta A0,
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T1) ->
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T1') ->

    ChorEnv.Equal T2 (Actor.Map.add A0 (Var.Map.concat Theta (ChorEnv.find A0 T1)) T1) ->
    ChorEnv.Equal T2' (Actor.Map.add A0 (Var.Map.concat Theta (ChorEnv.find A0 T1')) T1') ->

    step C T2 cfg l C' T2' cfg'.
Admitted.

(* This version of cfg_weakening is equivalent to the previous one, but appears to be easier to use in practice *)
Lemma cfg_weakening : forall C T1 cfg l C' T1' cfg',
    step C T1 cfg l C' T1' cfg' ->

    (*Choreography.WellFormed C ->*)
    forall T2 T2' Theta A0,
    Var.Map.Partition (ChorEnv.find A0 T2) Theta (ChorEnv.find A0 T1) ->
    Var.Map.Partition (ChorEnv.find A0 T2') Theta (ChorEnv.find A0 T1') ->

    (forall B0, B0 <> A0 -> Var.Map.Equal (ChorEnv.find B0 T2) (ChorEnv.find B0 T1)) ->
    (forall B0, B0 <> A0 -> Var.Map.Equal (ChorEnv.find B0 T2') (ChorEnv.find B0 T1')) ->

    step C T2 cfg l C' T2' cfg'.
Proof.
  intros.
  Var.Map.Tactics.reflect_partition.
  (*eapply cfg_weakening'; eauto.
  { eapply step_wf_label; eauto. }
  { intros D. ChorEnv.simplify. }
  { intros D. ChorEnv.simplify. }
   *)
Admitted.
