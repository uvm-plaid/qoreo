From Qoreo.Base Require Import Var.
From Qoreo.Expr Require Expr BaseProofs.
From Qoreo.Choreography Require Import Choreography BaseProofs Lemmas.
Import HelperLemmas.



(** * Proofs about well-typedness *)
Lemma wt_disjoint : forall C A G D T,
    WellTyped G D T C ->
    Var.Map.Properties.Disjoint (ChorEnv.find A G) (ChorEnv.find A D).
Proof.
  intros ? ? ? ? ? HWT.
  induction HWT; ChorEnv.simplify.
  * unfold ChorEnv.Empty in *.
    rewrite H.
    Var.simplify.

  * intros z [Hin1 Hin2].
    Var.Map.Tactics.compare z y.
    apply (H2 z).
    split; auto.
    Var.simplify.

  * intros z [Hin1 Hin2].
    Var.Map.Tactics.compare z x.
    apply (H2 z).
    split; auto.
    Var.simplify.

  * Var.Map.Tactics.reflect_partition.
    rewrite Heq1.
    Var.simplify.
    split; auto.
    eapply Expr.BaseProofs.wt_disjoint; eauto.

  * Var.Map.Tactics.reflect_partition.
    rewrite Heq0.
    Var.simplify.
    split; auto.
    eapply Expr.BaseProofs.wt_disjoint; eauto.

  * Var.Map.Tactics.reflect_partition.
    rewrite Heq0.
    Var.simplify.
    split.
    { eapply Expr.BaseProofs.wt_disjoint; eauto. }
    { 
      intros z [Hin1 Hin2].
      Var.Map.Tactics.compare x z.
      apply (H3 z).
      split; auto.
      Var.simplify.
    }

  * Var.Map.Tactics.reflect_partition.
    rewrite Heq0.
    Var.simplify.
    split; auto.
    { eapply Expr.BaseProofs.wt_disjoint; eauto. }
    { 
      intros z [Hin1 Hin2].
      Var.Map.Tactics.compare z x1.
      Var.Map.Tactics.compare z x2.
      apply (H5 z).
      split; auto.
      Var.simplify.
    }

  * Var.Map.Tactics.reflect_partition.
    rewrite Heq0.
    Var.simplify.
    repeat split; auto.
    eapply Expr.BaseProofs.wt_disjoint; eauto.
Qed.

Lemma weakening_gen : forall C G D T G0,
    WellTyped G D T C ->
    forall G',
      (forall A0,
          (Var.Map.Partition (ChorEnv.find A0 G') (ChorEnv.find A0 G) (ChorEnv.find A0 G0)) /\
          (Var.Map.Properties.Disjoint (ChorEnv.find A0 G0) (ChorEnv.find A0 D))) ->
      WellTyped G' D T C.
  Proof.
    intros C G D T G0 HWT.
    generalize dependent G0.
    induction HWT; intros G0 G' HE.

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
          
      }
      eapply If.
      { exact HEWG. }
      { apply (IHHWT1 G0 G').
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split.
        { exact HEpart. }
        { eapply partition_dj_env; eauto. }
      }
      { apply (IHHWT2 G0 G').
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split.
        { exact HEpart. }
        { apply (partition_dj_env A0 A G0 D
                   (Var.Map.concat DeltaA1 DeltaA3) DeltaA2
                   HEdisj HpartD2'). }
      }
      { apply (IHHWT3 G0 G').
        intros A0.
        destruct (HE A0) as [HEpart HEdisj].
        split.
        { exact HEpart. }
        { apply (partition_dj_env A0 A G0 D
                   (Var.Map.concat DeltaA1 DeltaA2) DeltaA3
                   HEdisj HpartD3). }
      }
      { Var.Map.Tactics.reflect_partition.
        2:{
          rewrite Heq.
          rewrite <- Var.Map.Proofs.concat_assoc.
          reflexivity.
        }
        Var.simplify.
      }
      { Var.Map.Tactics.reflect_partition.
        2:{
          Var.simplify.
          rewrite Var.Map.Proofs.concat_sym; auto.
          reflexivity.
        }
        Var.simplify.
      }
      2:{
        Var.Map.Tactics.reflect_partition.
        2:{ reflexivity. }
        Var.simplify.
      }
      { Var.Map.Tactics.reflect_partition; Var.simplify. }
  Qed.



(** Weakening *)
Lemma cfg_weakening' : forall C T1 cfg l C' T1' cfg',
    step C T1 cfg l C' T1' cfg' ->

    Label.WellFormed l ->
    forall T2 T2' Theta A0,
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T1) ->
    Var.Map.Properties.Disjoint Theta (ChorEnv.find A0 T1') ->

    ChorEnv.Equal T2 (Actor.Map.add A0 (Var.Map.concat Theta (ChorEnv.find A0 T1)) T1) ->
    ChorEnv.Equal T2' (Actor.Map.add A0 (Var.Map.concat Theta (ChorEnv.find A0 T1')) T1') ->

    step C T2 cfg l C' T2' cfg'.
Proof.
(* TODO
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep; intros HWF T2 T2' Theta A0 Hpart Hpart' Heq Heq';
    rewrite Heq, Heq' in *; clear T2 T2' Heq Heq'.
  * (* SendC *)
    rewrite H0 in *; clear T' H0.
    Actor.Map.Tactics.compare A A0.
    + ChorEnv.simplify.
      apply SendC with (TA' := (Var.Map.concat Theta TA')).
      2:{ intros D. ChorEnv.simplify. }

      eapply Expr.cfg_weakening_2; eauto.
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }

    + (* A0 <> A *)
      ChorEnv.simplify.
      eapply SendC with (TA' := TA').
      2:{ intros D. ChorEnv.simplify. }
      ChorEnv.simplify.

  * (* SendB*)
    rewrite H0 in *; clear refs H0.
    ChorEnv.simplify.
    econstructor; eauto.
    reflexivity.

  * (* EPRB *)
    inversion HWF; subst; clear HWF.
    rewrite H0 in *; clear T' H0.
    ChorEnv.simplify.
    Var.Map.Tactics.reflect_partition.

    unfold ChorEnv.epr in *.
    destruct (Config.epr_cfg cfg) as [[idx1 idx2] cfg0] eqn:Hepr.
    inversion H; subst; clear H.

    econstructor; eauto.
    {
      unfold ChorEnv.epr in *.
      rewrite Hepr.
      reflexivity.
    }
    {
      intros D.
      ChorEnv.simplify.
      Var.solve.
      Var.solve.
    }

  * (* EPRB' *)
    inversion HWF; subst; clear HWF.
    rewrite H0 in *; clear T' H0.
    ChorEnv.simplify.
    Var.Map.Tactics.reflect_partition.

    unfold ChorEnv.epr in *.
    destruct (Config.epr_cfg cfg) as [[idx1 idx2] cfg0] eqn:Hepr.
    inversion H; subst; clear H.

    econstructor; eauto.
    {
      unfold ChorEnv.epr in *.
      rewrite Hepr.
      reflexivity.
    }
    {
      intros D.
      ChorEnv.simplify.
      Var.solve.
      Var.solve.
    }

  * (* LetC *)

    rewrite H0 in *; clear T' H0.
    Actor.Map.Tactics.compare A A0.
    + ChorEnv.simplify.
      econstructor; eauto.
      2:{ ChorEnv.simplify. }

      eapply Expr.cfg_weakening_2; eauto.
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }

    + (* A0 <> A *)
      ChorEnv.simplify.
      eapply LetC with (TA' := TA').
      2:{ intros D. ChorEnv.simplify. }
      ChorEnv.simplify.

  * (* LetB *)
    rewrite H1 in *; clear refs H1.
    econstructor; eauto.
    reflexivity.

  * (* LetBangC *) 
    rewrite H0 in *; clear T' H0.
    Actor.Map.Tactics.compare A A0.
    + ChorEnv.simplify.
      econstructor; eauto.
      2:{ ChorEnv.simplify. }

      eapply Expr.cfg_weakening_2; eauto.
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }

    + (* A0 <> A *)
      ChorEnv.simplify.
      eapply LetBangC with (TA' := TA').
      2:{ intros D. ChorEnv.simplify. }
      ChorEnv.simplify.

  * (* LetBangB *)
    rewrite H0 in *; clear refs' H0.
    econstructor; eauto.
    reflexivity.

  * (* LetPairC *)
    rewrite H0 in *; clear T' H0.
    Actor.Map.Tactics.compare A A0.
    + ChorEnv.simplify.
      econstructor; eauto.
      2:{ ChorEnv.simplify. }

      eapply Expr.cfg_weakening_2; eauto.
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }
      { Var.Map.Tactics.reflect_partition; eauto. ChorEnv.simplify. }

    + (* A0 <> A *)
      ChorEnv.simplify.
      eapply LetPairC with (TA' := TA').
      2:{ intros D. ChorEnv.simplify. }
      ChorEnv.simplify.

  * (* LetPairB *)
    rewrite H2 in *; clear refs' H2.
    econstructor; eauto.
    reflexivity.

  * (* Delay *)
    apply Delay; auto.
    eapply IHHstep; eauto; reflexivity.
Qed.
*) Admitted.

(* This version of cfg_weakening is equivalent to the previous one, but appears to be easier to use in practice *)
Lemma cfg_weakening : forall C T1 cfg l C' T1' cfg',
    step C T1 cfg l C' T1' cfg' ->

    Choreography.WellFormed C ->
    forall T2 T2' Theta A0,
    Var.Map.Partition (ChorEnv.find A0 T2) Theta (ChorEnv.find A0 T1) ->
    Var.Map.Partition (ChorEnv.find A0 T2') Theta (ChorEnv.find A0 T1') ->

    (forall B0, B0 <> A0 -> Var.Map.Equal (ChorEnv.find B0 T2) (ChorEnv.find B0 T1)) ->
    (forall B0, B0 <> A0 -> Var.Map.Equal (ChorEnv.find B0 T2') (ChorEnv.find B0 T1')) ->

    step C T2 cfg l C' T2' cfg'.
Proof.
  intros.
  Var.Map.Tactics.reflect_partition.
  eapply cfg_weakening'; eauto.
  { eapply step_wf_label; eauto. }
  { intros D. ChorEnv.simplify. }
  { intros D. ChorEnv.simplify. }
Qed.
