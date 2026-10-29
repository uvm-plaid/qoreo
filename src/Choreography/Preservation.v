From Qoreo.Base Require Import Var.
From Qoreo.Expr Require Expr BaseProofs Preservation.
From Qoreo.Choreography Require Import Choreography BaseProofs Lemmas Weakening Substitution.
Import HelperLemmas.



(** * Lemmas about well-formedness and well-scopedness *)


Lemma WellTyped_WellFormed : forall Γ Delta Theta C,
  WellTyped Γ Delta Theta C ->
  Choreography.WellFormed C.
Proof.
  intros ? ? ? ? HWT.
  induction HWT; constructor; auto; constructor; auto.
Qed.


Lemma WellScoped_preservationC : forall I Theta ρ l I' Theta' ρ',
  Insn.stepC I Theta ρ l I' Theta' ρ' ->
  Insn.WellFormed I ->
  ChorEnv.WellScoped Theta ρ ->
  ChorEnv.WellScoped Theta' ρ'.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep; intros HWT HWS;
  try match goal with
  | [ H : ChorEnv.Equal ?A ?B |- _ ] =>
    rewrite H in *; clear A H
  end; 
  auto;
  unfold ChorEnv.WellScoped in *.

  * assert (Config.WellScoped TA' cfg').
    { eapply Expr.Preservation.WellScoped_preservation; eauto. }
    intros D. ChorEnv.simplify.
    eapply Config.WellScoped_monotonic; eauto.
    eapply Expr.BaseProofs.step_dim_monotonic; eauto.
    
  * assert (Config.WellScoped TA' cfg').
    { eapply Expr.Preservation.WellScoped_preservation; eauto. }
    intros D. ChorEnv.simplify.
    eapply Config.WellScoped_monotonic; eauto.
    eapply Expr.BaseProofs.step_dim_monotonic; eauto.

  * assert (Config.WellScoped TA' cfg').
    { eapply Expr.Preservation.WellScoped_preservation; eauto. }
    intros D. ChorEnv.simplify.
    eapply Config.WellScoped_monotonic; eauto.
    eapply Expr.BaseProofs.step_dim_monotonic; eauto.

  * assert (Config.WellScoped TA' cfg').
    { eapply Expr.Preservation.WellScoped_preservation; eauto. }
    intros D. ChorEnv.simplify.
    eapply Config.WellScoped_monotonic; eauto.
    eapply Expr.BaseProofs.step_dim_monotonic; eauto.
Qed.


Lemma WellScoped_preservationB : forall C Theta ρ l C' Theta' ρ',
  Choreography.stepB C Theta ρ l C' Theta' ρ' ->
  Choreography.WellFormed C ->
  ChorEnv.WellScoped Theta ρ ->
  ChorEnv.WellScoped Theta' ρ'.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  destruct Hstep; intros HWT HWS; subst;
  try match goal with
  | [ H : ChorEnv.Equal ?A ?B |- _ ] =>
    rewrite H in *; clear A H
  end; auto.
* eapply ChorEnv.WellScoped_epr; eauto.
  inversion HWT; subst; clear HWT.
  match goal with
  | [ H : Insn.WellFormed (Insn.EPR _ _ _ _) |- _ ] =>
    inversion H; subst; auto
  end.
* eapply ChorEnv.WellScoped_epr; eauto.
  inversion HWT; subst; clear HWT.
  match goal with
  | [ H : Insn.WellFormed (Insn.EPR _ _ _ _) |- _ ] =>
    inversion H; subst; auto
  end.
Qed.


Lemma WellScoped_preservation : forall C Theta ρ l C' Theta' ρ',
  Choreography.step C Theta ρ l C' Theta' ρ' ->
  Choreography.WellFormed C ->
  ChorEnv.WellScoped Theta ρ ->
  ChorEnv.WellScoped Theta' ρ'.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep; intros HWT HWS;
  try match goal with
  | [ H : ChorEnv.Equal ?A ?B |- _ ] =>
    rewrite H in *; clear A H
  end; auto.

* eapply WellScoped_preservationC; eauto.
  inversion HWT; subst; auto.
* inversion HWT; subst; clear HWT.
  assert (Config.WellScoped TA' cfg').
  { eapply Expr.Preservation.WellScoped_preservation; eauto. }
  intros D. ChorEnv.simplify.
  eapply Config.WellScoped_monotonic; eauto.
  eapply Expr.BaseProofs.step_dim_monotonic; eauto.
* eapply WellScoped_preservationB; eauto.
* inversion HWT; subst; clear HWT.
  apply IHHstep; auto.
* inversion HWT; subst; clear HWT.
  apply IHHstep; auto.
Qed.



Lemma epr_inversion : forall A B T1 cfg1 q1 q2 T2 cfg2,
    A <> B ->
    ChorEnv.epr A B T1 cfg1 = (q1, q2, T2, cfg2) ->
    ChorEnv.WellScoped T1 cfg1 ->
    (exists idx1 idx2,
        Var.Map.Partition (ChorEnv.find A T2) (ChorEnv.find A T1)
	  (Var.Map.add q1 idx1 (Var.Map.empty _)) /\
        Var.Map.Partition (ChorEnv.find B T2) (ChorEnv.find B T1)
	  (Var.Map.add q2 idx2 (Var.Map.empty _))) /\
      ChorEnv.Equal T1
        (Actor.Map.add B (ChorEnv.find B T1) (
             Actor.Map.add A (ChorEnv.find A T1) T2)).
Proof.
  intros A B T1 cfg1 q1 q2 T2 cfg2 Heq Hepr HWS.
  unfold ChorEnv.epr in Hepr.
  destruct (Config.epr_cfg cfg1) as [[idx1 idx2] cfg'] eqn:Eqnepr.
  inversion Hepr; subst; clear Hepr.

  split.
  2:{
    intros D.
    ChorEnv.simplify.
  }
  exists q1, q2.
  assert (~ Var.Map.In q1 (ChorEnv.find A T1)) as Hq1.
  {
    intros Hin.
    inversion Eqnepr; subst; clear Eqnepr.
    unfold ChorEnv.WellScoped in HWS.
    apply (Config.wf_qrefs _ cfg1) in Hin; auto.
    lia.
  }
  assert (~ Var.Map.In q2 (ChorEnv.find B T1)) as Hq2.
  {
    intros Hin.
    inversion Eqnepr; subst; clear Eqnepr.
    unfold ChorEnv.WellScoped in HWS.
    apply (Config.wf_qrefs _ cfg1) in Hin; auto.
    lia.
  }
  split.
  {
    ChorEnv.simplify.
    apply Var.Map.Proofs.partition_add_r; auto with var_db.
  }
  {
    ChorEnv.simplify.
    apply Var.Map.Proofs.partition_add_r; auto with var_db.
  }
Qed.
   
Lemma nilnostep : forall T cfg l C' T' cfg',
    ~ step Choreography.Empty T cfg l C' T' cfg'. 
Proof.
  intros T cfg l C' T' cfg' Hstep.
  inversion Hstep.
  inversion H.
Qed.

Lemma epr_partition : forall T1 Theta2 A B T cfg q1 q2 T' cfg' D,
  ChorEnv.epr A B T cfg = (q1, q2, T', cfg') ->
  D <> A -> D <> B ->
  (Var.Map.Partition (ChorEnv.find D T) (ChorEnv.find D T1) Theta2) ->
  (forall D0, D0 <> D -> Var.Map.Equal (ChorEnv.find D0 T1) (ChorEnv.find D0 T)) ->
  exists T1', ChorEnv.epr A B T1 cfg = (q1, q2, T1', cfg') /\
              Var.Map.Partition (ChorEnv.find D T') (ChorEnv.find D T1') Theta2 /\
              (forall D0, D0 <> D -> Var.Map.Equal (ChorEnv.find D0 T1') (ChorEnv.find D0 T')).
Proof.
  intros T1 Theta2 A B T cfg q1 q2 T' cfg' D Hepr HDA HDB Hpart Heq.
  unfold ChorEnv.epr in Hepr.
  destruct (Config.epr_cfg cfg) as [[idx1 idx2] cfg0] eqn:Hcfg0.
  unfold ChorEnv.epr. rewrite Hcfg0.
  inversion Hepr; subst; clear Hepr.
  eexists.
  split; [reflexivity | ].
  split.
  + ChorEnv.simplify.
  + intros D0 HD0.
    ChorEnv.simplify.
    { rewrite Heq; auto; try reflexivity. }
    { rewrite Heq; auto; try reflexivity. }
    { rewrite Heq; auto; try reflexivity. }
Qed.

(* Step_partition_pairs asserts that T1 differs from T1' by the same context that T2 differs from T2' *)
Definition Step_partition_pairs (T1 T1' T2 T2' : ChorEnv.t nat) :=
  forall A Theta,
    Var.Map.Partition (ChorEnv.find A T1) (ChorEnv.find A T1') Theta ->
    Var.Map.Partition (ChorEnv.find A T2) (ChorEnv.find A T2') Theta.

Lemma spps_on : forall A Theta1 Theta2 (T1 T2 T3 : ChorEnv.t nat),
    Step_partition_pairs T1 (Actor.Map.add A Theta2 T1) T2 T3 ->
    Var.Map.Partition (ChorEnv.find A T1) Theta1 Theta2 ->
    ChorEnv.Equal T3 (Actor.Map.add A (ChorEnv.find A T3) T2) /\
      Var.Map.Partition (ChorEnv.find A T2) Theta1 (ChorEnv.find A T3).
Proof.
  intros A Theta1 Theta2 T1 T2 T3 Hpairs Hpartition.
  unfold Step_partition_pairs in Hpairs.
  split.
  {
    intros A0.
    destruct (Actor.eq_dec A A0) as [Heq | Hneq].
    {
      rewrite <- Heq.
      rewrite HelperLemmas.find_add.
      Var.simplify.
    }
    {
      specialize (Hpairs A0 (Var.Map.empty nat)).
      rewrite HelperLemmas.find_ab_neq2 in Hpairs by congruence.
      rewrite HelperLemmas.find_ab_neq2 by congruence.
      assert (Hempty : Var.Map.Partition
        (ChorEnv.find A0 T1) (ChorEnv.find A0 T1) (Var.Map.empty nat)).
      { apply Var.Map.Proofs.partition_empty_r. }
      specialize (Hpairs Hempty).
      apply Var.Map.Proofs.partition_empty2_eq in Hpairs.
      rewrite Hpairs.
      Var.simplify.
    }
  }
  {
    specialize (Hpairs A Theta1).
    rewrite find_add in Hpairs.
    specialize (Hpairs
      (@Var.Map.Properties.Partition_sym _
        (ChorEnv.find A T1) Theta1 Theta2 Hpartition)).
    pose proof (@Var.Map.Properties.Partition_sym _
      (ChorEnv.find A T2) (ChorEnv.find A T3) Theta1 Hpairs).
    exact H.
  }
Qed.

(* Partition_except l T1 T2
  says that T1 and T2 are the same on all the actors in l, and T2 is a subset of T1 on all other actors
*)
(*Definition Partition_except l (T1 T2 : ChorEnv.t nat) :=
  (forall A,
    ~ Actor.FSet.In A (Label.actors l) ->
    exists Theta,
      Var.Map.Partition (ChorEnv.find A T1) (ChorEnv.find A T2) Theta) /\
    (forall A,
      Actor.FSet.In A (Label.actors l) ->
      Var.Map.Equal (ChorEnv.find A T1) (ChorEnv.find A T2)).
      *)
Definition Partition_except l (T T' : ChorEnv.t nat) :=
  exists T0, 
    ChorEnv.Partition T T' T0
    /\
    (forall B, Actor.FSet.In B (Label.actors l) ->
      Var.Map.Equal (T0!B) (Var.Map.empty _)).

(* Probably not needed *)
(*
Lemma ws_partition_except : forall l (T1 T2 : ChorEnv.t nat) cfg,
    ChorEnv.WellScoped T1 cfg ->
    Partition_except l T1 T2 ->
    ChorEnv.WellScoped T2 cfg.
Proof.
  intros l T1 T2 cfg Hws [Hpart Heq] A.
  specialize (Hws A).
  destruct Hws as [Hwf Hscope].
  split; auto.
  intros z Hz.
  apply Hscope.
  destruct (Actor.Map.FSetProofs.in_dec A (Label.actors l)) as [Hin | Hin].
  - rewrite Heq; auto.
  - destruct (Hpart A Hin) as [Theta Hpartition].
    Var.Map.Tactics.reflect_partition.
    rewrite Heq0.
    Var.simplify.
Qed.
*)


Lemma epr_part' : forall T1 A B T cfg q1 q2 T' cfg',
  ChorEnv.epr A B T cfg = (q1, q2, T', cfg') ->
  (*Partition_except (Label.EPR A B) T T1 ->*)
  ChorEnv.WellScoped T cfg ->
  exists T1', ChorEnv.epr A B T1 cfg = (q1, q2, T1', cfg') /\
              Step_partition_pairs T T1 T' T1'.
Proof.
  intros T1 A B T cfg q1 q2 T' cfg' Hepr (*[Hpart Heq]*) HWS.
  unfold ChorEnv.epr in *.
  destruct (Config.epr_cfg cfg) as [[idx1 idx2] cfg0] eqn:Hcfg.
  inversion Hepr; subst; clear Hepr.
  exists (ChorEnv.add B q2 q2 (ChorEnv.add A q1 q1 T1)).
  split; auto.
  intros D ThetaD HpartD.
  assert (Hin1 : ~ Var.Map.In q1 ThetaD).
  {
    assert (Hin : ~ Var.Map.In q1 (ChorEnv.find D T)).
      {
        intros Hin.
        eapply Config.wf_qrefs in Hin; eauto.
        inversion Hcfg; subst; clear Hcfg.
        lia.
      }
      intros HinD.
      apply Hin.
      Var.Map.Tactics.reflect_partition.
      rewrite Heq.
      Var.simplify.
  }
  assert (Hin2 : ~ Var.Map.In q2 ThetaD).
  {
    assert (Hin : ~ Var.Map.In q2 (ChorEnv.find D T)).
      {
        intros Hin.
        eapply Config.wf_qrefs in Hin; eauto.
        inversion Hcfg; subst; clear Hcfg.
        lia.
      }
      intros HinD.
      apply Hin.
      Var.Map.Tactics.reflect_partition.
      rewrite Heq.
      Var.simplify.
  }
  ChorEnv.simplify.
  + (* A = D *)
    apply Var.Map.Proofs.partition_add_l; auto.
    apply Var.Map.Proofs.partition_add_l; auto.

  + (* B = D *)
    apply Var.Map.Proofs.partition_add_l; auto.
  
  + (* D <> A, D <> B *)
    apply Var.Map.Proofs.partition_add_l; auto.
Qed.


Lemma partition_functional_2 : forall T (M M1 M2 M2' : Var.Map.t T),
  Var.Map.Partition M M1 M2 -> Var.Map.Partition M M1 M2' ->
  Var.Map.Equal M2 M2'.
Proof.
  intros T M M1 M2 M2' Hpart Hpart'.
  Var.Map.Tactics.reflect_partition.
  Var.reflect_find.
  specialize (Heq z).
  Var.simplify.
  destruct (Var.Map.find z M1) as [v | ] eqn:H1; auto.
  destruct (Var.Map.find z M2) as [v2 | ] eqn:H2.
  {
    exfalso.
    apply (Hdisj0 z).
    split; Var.solve.
  }
  destruct (Var.Map.find z M2') as [v' | ] eqn:H2'; auto.
  {
    exfalso.
    apply (Hdisj z).
    split; Var.solve.
  }
Qed.

Lemma concat_empty_id : forall {T} (m : Var.Map.t T),
  Var.Map.Equal (Var.Map.concat (Var.Map.empty _) m) m.
Proof.
  intros T m x.
  unfold Map.concat.
  Var.simplify.
Qed.
Hint Rewrite @concat_empty_id : var_db.
Lemma concat_id_empty : forall {T} (m : Var.Map.t T),
  Var.Map.Equal (Var.Map.concat m (Var.Map.empty _)) m.
Proof.
  intros T m.
  apply Var.Map.Reflection.reflect_map_concat_empty.
Qed.
Hint Rewrite @concat_id_empty : var_db.


Lemma delay_inversion_C : forall I1 I2 C T1 cfg1 l T2 cfg2,
    Insn.stepC I1 T1 cfg1 l I2 T2 cfg2 ->
    ChorEnv.WellScoped T1 cfg1 ->    
    forall G D T1',
      Partition_except l T1 T1' ->
      Choreography.WellTyped G D T1' (Choreography.Do I1 C) ->
      exists T2',
        Insn.stepC I1 T1' cfg1 l I2 T2' cfg2 /\
          Step_partition_pairs T1 T1' T2 T2'.
Proof.
  intros I1 I2 C T1 cfg1 l T2 cfg2 Hstep HWS.
  destruct Hstep; intros G D T1' [T0 [Hpart0 Hexcept]] HWT.
  - (* SendC: preserve the active actor's expression environment. *)
    inversion HWT; subst; clear HWT.
    eexists.
    split.
    + (* Rebuild SendC using Hsame and the original expression step. *)
      eapply Insn.SendC with (TA' := TA').
      * specialize (Hpart0 A).
        Var.Map.Tactics.reflect_partition.
        Var.Map.Tactics.rewrite_map (T!A).
        rewrite Hexcept in H.
        2:{ simpl; Actor.simplify. }


        simpl. Var.simplify.
      * reflexivity.
    + (* Transfer the environment partition to the stepped environments. *)
      unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      rewrite H0.
      ChorEnv.simplify.
      assert (Var.Map.Equal (T!D0) (T1'!D0)).
      {
        specialize (Hpart0 D0).
        Var.Map.Tactics.reflect_partition.
        Var.Map.Tactics.rewrite_map (T!D0).
        Var.Map.Tactics.rewrite_map (T1'!D0).
        rewrite (Hexcept D0) in Heq2; [ | simpl; Actor.simplify ].
        rewrite Heq2.
        Var.simplify.
      }
      Var.Map.Tactics.rewrite_map (T!D0).
      assert (Var.Map.Equal Theta0 (Var.Map.empty _)).
      {
        eapply partition_functional_2; eauto.
        apply Var.Map.Proofs.partition_empty_r.
      }
      Var.simplify.
      apply Var.Map.Proofs.partition_empty_r.

  - (* LetC: same active-actor argument; account for the bound variable. *)
    inversion HWT; subst; clear HWT.
    eexists.
    split.
    + (* Rebuild LetC and use the typed instruction premises. *)
      eapply Insn.LetC with (TA' := TA').
      * specialize (Hpart0 A).
        Var.Map.Tactics.reflect_partition.
        Var.Map.Tactics.rewrite_map (T!A).
        rewrite Hexcept in H.
        2:{ simpl; Actor.simplify. }
        Var.simplify.
      * intros D0. ChorEnv.simplify.
    + 
      unfold Step_partition_pairs.
      intros D0 Theta0 Hparts.
      rewrite H0 in *; clear T' H0.
      ChorEnv.simplify.
      assert (Var.Map.Equal (T!D0) (T1'!D0)).
      {
        specialize (Hpart0 D0).
        Var.Map.Tactics.reflect_partition.
        Var.Map.Tactics.rewrite_map (T!D0).
        Var.Map.Tactics.rewrite_map (T1'!D0).
        rewrite (Hexcept D0) in Heq2; [ | simpl; Actor.simplify ].
        rewrite Heq2.
        Var.simplify.
      }
      Var.Map.Tactics.rewrite_map (T!D0).
      assert (Var.Map.Equal Theta0 (Var.Map.empty _)).
      {
        eapply partition_functional_2; eauto.
        apply Var.Map.Proofs.partition_empty_r.
      }
      Var.simplify.
      apply Var.Map.Proofs.partition_empty_r.


  - 
    inversion HWT; subst; clear HWT.
    eexists.
    split.
    +
      eapply Insn.LetBangC with (TA' := TA').
      * specialize (Hpart0 A).
        Var.Map.Tactics.reflect_partition.
        Var.Map.Tactics.rewrite_map (T!A).
        rewrite Hexcept in H.
        2:{ simpl; Actor.simplify. }
        Var.simplify.
      * reflexivity.
    + (* Transfer the environment partition across the local update. *)
      unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      rewrite H0.
      ChorEnv.simplify.
      assert (Var.Map.Equal (T!D0) (T1'!D0)).
      {
        specialize (Hpart0 D0).
        Var.Map.Tactics.reflect_partition.
        Var.Map.Tactics.rewrite_map (T!D0).
        Var.Map.Tactics.rewrite_map (T1'!D0).
        rewrite (Hexcept D0) in Heq2; [ | simpl; Actor.simplify ].
        rewrite Heq2.
        Var.simplify.
      }
      Var.Map.Tactics.rewrite_map (T!D0).
      assert (Var.Map.Equal Theta0 (Var.Map.empty _)).
      {
        eapply partition_functional_2; eauto.
        apply Var.Map.Proofs.partition_empty_r.
      }
      Var.simplify.
      apply Var.Map.Proofs.partition_empty_r.

  - (* LetPairC: handle both bound variables in the typing premises. *)
    inversion HWT; subst; clear HWT.
    eexists.
    split.
    + (* Rebuild LetPairC and use the typed instruction premises. *)
      eapply Insn.LetPairC with (TA' := TA').
      * specialize (Hpart0 A).
        Var.Map.Tactics.reflect_partition.
        Var.Map.Tactics.rewrite_map (T!A).
        rewrite Hexcept in H.
        2:{ simpl; Actor.simplify. }
        Var.simplify.
      * intros D0. ChorEnv.simplify.
    + (* Transfer the environment partition across the local update. *)
      unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      rewrite H0.
      ChorEnv.simplify.
      assert (Var.Map.Equal (T!D0) (T1'!D0)).
      {
        specialize (Hpart0 D0).
        Var.Map.Tactics.reflect_partition.
        Var.Map.Tactics.rewrite_map (T!D0).
        Var.Map.Tactics.rewrite_map (T1'!D0).
        rewrite (Hexcept D0) in Heq2; [ | simpl; Actor.simplify ].
        rewrite Heq2.
        Var.simplify.
      }
      Var.Map.Tactics.rewrite_map (T!D0).
      assert (Var.Map.Equal Theta0 (Var.Map.empty _)).
      {
        eapply partition_functional_2; eauto.
        apply Var.Map.Proofs.partition_empty_r.
      }
      Var.simplify.
      apply Var.Map.Proofs.partition_empty_r.
Qed.


Lemma delay_inversion_B : forall C1 C2 T1 cfg1 l T2 cfg2,
    Choreography.stepB C1 T1 cfg1 l C2 T2 cfg2 ->
    ChorEnv.WellScoped T1 cfg1 ->    
    forall G D T1',
      Choreography.WellTyped G D T1' C1 ->
      exists T2',
        Choreography.stepB C1 T1' cfg1 l C2 T2' cfg2 /\
          Step_partition_pairs T1 T1' T2 T2'.
Proof.
  intros C1 C2 T1 cfg1 l T2 cfg2 Hstep HWS.
  induction Hstep; intros G D T1' HWT.
  - (* IfB: retain T1'; use environment equality and unchanged config. *)
    exists T1'; split.
    + (* Rebuild IfB for the restricted environment. *)
      econstructor; eauto; try reflexivity;
        try (intros; ChorEnv.simplify).
    + (* Transfer the partition through the environment equality. *)
      unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      unfold ChorEnv.Equal in H0.
      specialize (H0 D0).
      first [rewrite H0 | rewrite <- H0].
      exact Hparts.
  - (* SendB: preserve the environment; use the label's actor partition. *)
    exists T1'; split.
    + (* Rebuild SendB and retain the substitution result. *)
      eapply Choreography.SendB; eauto; reflexivity.
    + (* Transfer the partition through refs = refs'. *)
      unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      unfold ChorEnv.Equal in H0.
      specialize (H0 D0).
      first [rewrite H0 | rewrite <- H0].
      exact Hparts.
  - (* EPRB: adapt environment allocation using epr_part'. *)
    destruct (epr_part' T1' A B T cfg q1 q2 T0 cfg' H
     HWS) as [T1'' [Hepr' Hparts']].
    exists T1''; split.
    + econstructor; eauto; try reflexivity;
        try (intros; ChorEnv.simplify).
    + unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      unfold ChorEnv.Equal in H0.
      specialize (H0 D0).
      rewrite H0.
      apply Hparts'; exact Hparts.
  - (* EPRB': adapt reversed environment allocation using epr_part'. *)
    destruct (epr_part' T1' B A T cfg q2 q1 T0 cfg' H
      HWS) as [T1'' [Hepr' Hparts']].
    exists T1''; split.
    + econstructor; eauto; try reflexivity;
        try (intros; ChorEnv.simplify).
    + unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      unfold ChorEnv.Equal in H0.
      specialize (H0 D0).
      rewrite H0.
      apply Hparts'; exact Hparts.
  - (* LetB: preserve the environment and account for substitution. *)
    exists T1'; split.
    + (* Rebuild LetB under the restricted environment. *)
      econstructor; eauto; try reflexivity;
        try (intros; ChorEnv.simplify).
    + (* Transfer the partition through refs = refs'. *)
      unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      match goal with
      | Henv : ChorEnv.Equal _ _ |- _ =>
          unfold ChorEnv.Equal in Henv;
          specialize (Henv D0);
          first [rewrite Henv | rewrite <- Henv]
      end.
      exact Hparts.
  - (* LetBangB: preserve the environment and account for substitution. *)
    exists T1'; split.
    + (* Rebuild LetBangB under the restricted environment. *)
      econstructor; eauto; try reflexivity;
        try (intros; ChorEnv.simplify).
    + (* Transfer the partition through refs' = refs. *)
      unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      match goal with
      | Henv : ChorEnv.Equal _ _ |- _ =>
          unfold ChorEnv.Equal in Henv;
          specialize (Henv D0);
          first [rewrite Henv | rewrite <- Henv]
      end.
      exact Hparts.
  - (* LetPairB: preserve the environment and account for both substitutions. *)
    exists T1'; split.
    + (* Rebuild LetPairB under the restricted environment. *)
      econstructor; eauto; try reflexivity;
        try (intros; ChorEnv.simplify).
    + (* Transfer the partition through refs' = refs. *)
      unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      match goal with
      | Henv : ChorEnv.Equal _ _ |- _ =>
          unfold ChorEnv.Equal in Henv;
          specialize (Henv D0);
          first [rewrite Henv | rewrite <- Henv]
      end.
      exact Hparts.
Qed.



Lemma concat_inversion_eq : forall {X} (m m1 m2 : Var.Map.t X),
  Var.Map.Properties.Disjoint m m1 ->
  Var.Map.Properties.Disjoint m m2 ->
  Var.Map.Equal (Var.Map.concat m m1) (Var.Map.concat m m2) ->
  Var.Map.Equal m1 m2.
Proof.
  intros X m m1 m2 H1 H2 Heq.
  intros z.
  specialize (Heq z).
  repeat rewrite Map.Proofs.concat_find in Heq.
  destruct (Map.find z m) as [v | ] eqn:Hfind; auto.
  {
    destruct (Map.find z m1) as [v1 | ] eqn:Hfind1.
    { exfalso. apply (H1 z). Var.solve. }
    destruct (Map.find z m2) as [v2 | ] eqn:Hfind2.
    { exfalso. apply (H2 z). Var.solve. }
    auto.
  }
Qed.


(* TODO: move to Map.v *)
Lemma partition_sym : forall {T} (A B C : Var.Map.t T),
  Var.Map.Partition A B C -> Var.Map.Partition A C B.
Proof.
  intros.
  Var.Map.Tactics.reflect_partition.
  { apply Var.Map.Proofs.disjoint_sym; auto. }
  rewrite Var.Map.Proofs.concat_sym; auto.
  reflexivity.
Qed.


Lemma concat_disjoint_injective : forall {T} (M M1 M2 : Var.Map.t T),
    Var.Map.Properties.Disjoint M M1 ->
    Var.Map.Properties.Disjoint M M2 ->
    Var.Map.Equal (Var.Map.concat M M1) (Var.Map.concat M M2) ->
    Var.Map.Equal M1 M2.
Admitted.



Definition ChorEnv_map [T] (X : Actor.FSet.t) (f : Actor.t -> Var.Map.t T) : ChorEnv.t T :=
  let g := fun A M => Actor.Map.add A (f A) M in
  Actor.FSet.fold g X ChorEnv.empty.
Lemma ChorEnv_map_find_eq : forall [T] X (f : Actor.t -> Var.Map.t T) A,
  Actor.FSet.In A X ->
  Var.Map.Equal ((ChorEnv_map X f) ! A)
                (f A).
Proof.
  intros T X f A HA.
  unfold ChorEnv_map, ChorEnv.find, ChorEnv.empty.
  rewrite Actor.FSet.fold_1.
  assert (Hpreserve : forall ls (M : Actor.Map.t (Var.Map.t T)),
    ~ SetoidList.InA Logic.eq A ls ->
    Actor.Map.find A
      (List.fold_left (fun M B => Actor.Map.add B (f B) M) ls M) =
    Actor.Map.find A M).
  {
    intros ls.
    induction ls as [|B ls IH]; intros M Hnotin; simpl.
    - reflexivity.
    - assert (Hnotin' : ~ SetoidList.InA Logic.eq A ls).
      { intro Hin. apply Hnotin. apply SetoidList.InA_cons_tl; exact Hin. }
      assert (Hneq : A <> B).
      { intro Heq. apply Hnotin. subst B. constructor; reflexivity. }
      rewrite (IH (Actor.Map.add B (f B) M) Hnotin').
      rewrite Actor.Map.Properties.F.add_o.
      destruct (Actor.Map.E.eq_dec B A); [congruence | reflexivity].
  }
  assert (Hfind : forall ls,
    forall (M : Actor.Map.t (Var.Map.t T)),
    SetoidList.NoDupA Logic.eq ls ->
    SetoidList.InA Logic.eq A ls ->
    Actor.Map.find A
      (List.fold_left (fun M B => Actor.Map.add B (f B) M) ls M) =
    Some (f A)).
  {
    intros ls.
    induction ls as [|B ls IH]; intros M Hnodup Hin.
    - inversion Hin.
    - simpl.
      inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
      destruct (Actor.Map.E.eq_dec A B) as [Heq | Hneq].
      + subst B.
        assert (HnotinA : ~ SetoidList.InA Logic.eq A ls).
        { intros HinA. apply Hnotin. exact HinA. }
        rewrite (Hpreserve ls (Actor.Map.add A (f A) M) HnotinA).
        rewrite Actor.Map.Properties.F.add_o.
        destruct (Actor.Map.E.eq_dec A A); [reflexivity | congruence].
      + inversion Hin; subst; [congruence |].
        apply (IH (Actor.Map.add B (f B) M)); assumption.
  }
  setoid_rewrite (Hfind (Actor.FSet.elements X)
    (Actor.Map.empty (Var.Map.t T))
    (Actor.FSet.elements_3w X)
    (Actor.FSet.elements_1 HA)).
  reflexivity.
Qed.


Definition ChorEnv_concat {T} (m1 m2 : ChorEnv.t T) : ChorEnv.t T :=
  let X := Actor.FSet.union (Actor.Map.domain m1) (Actor.Map.domain m2) in
  ChorEnv_map X (fun A => Var.Map.concat (m1!A) (m2!A)).


Lemma ChorEnv_not_in_find : forall {T} (m : ChorEnv.t T) B,
  ~ Actor.FSet.In B (Actor.Map.domain m) ->
  Var.Map.Equal (m ! B) (Var.Map.empty _).
Proof.
  intros.
  unfold ChorEnv.find.
  rewrite Actor.Map.Proofs.domain_In in H.
  Actor.solve.
Qed.



Lemma ChorEnv_map_find_not_in : forall [T] X (f : Actor.t -> Var.Map.t T) A,
  ~ Actor.FSet.In A X ->
  Var.Map.Equal ((ChorEnv_map X f) ! A)
                (Var.Map.empty _).
Admitted.


Lemma ChorEnv_map_find : forall [T] X (f : Actor.t -> Var.Map.t T) A,
  Var.Map.Equal ((ChorEnv_map X f) ! A)
                (if Actor.Map.FSetProofs.in_dec A X then f A else Var.Map.empty _).
Proof.
  intros.
  destruct (Actor.Map.FSetProofs.in_dec A X) as [Hin | Hin].
  * apply ChorEnv_map_find_eq; auto.
  * apply ChorEnv_map_find_not_in; auto.
Qed.

Lemma ChorEnv_concat_find : forall {T} (m1 m2 : ChorEnv.t T) B,
  Var.Map.Equal (ChorEnv_concat m1 m2 ! B) (Var.Map.concat (m1!B) (m2!B)).
Proof.
  intros.
  unfold ChorEnv_concat.
  rewrite ChorEnv_map_find.
  destruct (Actor.Map.FSetProofs.in_dec B (Actor.FSet.union (Actor.Map.domain m1) (Actor.Map.domain m2)))
    as [Hin | Hin];
    try reflexivity.
  * Actor.simplify.
    repeat rewrite ChorEnv_not_in_find; auto.
    Var.simplify.
Qed.

Lemma delay_inversion_IfDelay : forall A l 
        e C1 C2 C C'
        cfg cfg'
        G
        T T' T'' T1' T2' T'0 T0' ThetaA
        D D' D'' DeltaA,
  ~ Actor.FSet.In A (Label.actors l) ->
  Actor.FSet.Empty (Actor.FSet.inter (Label.actors l) (Choreography.actors C1)) ->
  Actor.FSet.Empty (Actor.FSet.inter (Label.actors l) (Choreography.actors C2)) ->
  ChorEnv.WellScoped T cfg ->

  step C T'' cfg l C' T2' cfg' ->
  Step_partition_pairs T T'' T' T2' ->

  (*Partition_except l T T1' ->*)
  ChorEnv.Partition T T1' T0' ->
  (forall B, Actor.FSet.In B (Label.actors l) ->
      Var.Map.Empty (T0'!B)) ->

  Expr.WellTyped (G!A) DeltaA ThetaA e Expr.Typ.BIT ->
  WellTyped G D' T'0 C1 ->
  WellTyped G D' T'0 C2 ->

  ChorEnv.EmptyExcept (Actor.FSet.union (Choreography.actors C2) (Choreography.actors C1)) D' ->
  ChorEnv.EmptyExcept (Actor.FSet.union (Choreography.actors C2) (Choreography.actors C1)) T'0 ->
  WellTyped G D'' T'' C ->

  ChorEnv.PartitionList D [Actor.Map.singleton A DeltaA; D'; D''] ->
  ChorEnv.PartitionList T1' [Actor.Map.singleton A ThetaA; T'0; T''] ->

  exists T2'',
    step (Choreography.If A e C1 C2 C) T1' cfg
         l
         (Choreography.If A e C1 C2 C') T2'' cfg'
    /\
    Step_partition_pairs T T1' T' T2''.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
  intros H_in_A_l Hempty1 Hempty2 H_well_scoped Hstep
    H_partition_pairs HpartT HemptyT0'
    HWTe HWTC1 HWTC2 H_empty_except_D H_empty_except_T
    HWTC
    HpartD HpartT1'.


  (* T2'' := B ↦ Var.Map.concat  (T2'!B)
                 (Var.Map.concat (Actor.Map.singleton A ThetaA ! B)
                                (T'0!B))
  *)
  set (T2'' := ChorEnv_concat T2' (ChorEnv_concat (Actor.Map.singleton A ThetaA) T'0)).
      
  eexists T2''. split.

  2:{
    unfold Step_partition_pairs.
    intros B Theta HpartTB.
    (* Want: T'!B == ??!B ++ Theta 
    Know:
      HPartTB :  T!B == T1'!B ++ Theta
      HpartT1' : T1' == [A ↦ ThetaA] ++ T'0 ++ T''
      HpartT :     T == T1' ++ T0'

      so T1'!B ++ T0'!B == T1'!B ++ Theta
      so Theta == T0'!B
    *)
    assert (HTheta : Var.Map.Equal Theta (T0'!B)).
    {
      ChorEnv.specialize_partition B.
      Var.Map.Tactics.reflect_partition.
      Var.Map.Tactics.rewrite_map (T!B).
      eapply concat_disjoint_injective; [ | | eauto];
        Var.simplify.
    }
    
    rewrite HTheta in *; clear HTheta Theta.
    specialize (H_partition_pairs B).

   
      (*
      Know:
        H_partition_pairs : 
          ∀ Theta, T!B == T''!B ++ Theta ->
                  T'!B == T2'!B ++ Theta
      Know:
        T!B == T1'!B ++ T0'!B
            == (A ↦ ThetaA)!B ++ T'0!B ++ T''!B ++ T0'!B
      *)
      assert (Hpart0 :
        Var.Map.Partition (T!B) 
          (T''!B)
          (Var.Map.concat   (Actor.Map.singleton A ThetaA ! B) 
          (Var.Map.concat   (T'0!B)
                            (T0'!B)))).
      {
        ChorEnv.specialize_partition B.
        Var.Map.Tactics.reflect_partition.
        2:{
          Var.Map.Tactics.rewrite_map (T!B).
          Var.Map.Tactics.rewrite_map (T1'!B).
          Var.Map.Tactics.rewrite_map (M2!B).
          repeat rewrite Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym _ (T''!B)).
          repeat rewrite Var.Map.Proofs.concat_assoc.
          reflexivity.
          {
            Var.simplify.
          }
        }
        Var.Map.Tactics.rewrite_map (T!B).
        Var.Map.Tactics.rewrite_map (T1'!B).
        Var.Map.Tactics.rewrite_map (M2!B).
        Var.simplify.
        repeat split; auto;
          apply Var.Map.Proofs.disjoint_sym; auto.
      }
      pose proof (H_partition_pairs _ Hpart0) as H00.
      (* H00 :
        T'!B == T2'!B ++ (A ↦ ThetaA)!B ++ T'0!B ++ T0'!B *)

      unfold T2''.
      repeat rewrite ChorEnv_concat_find.
      
      ChorEnv.specialize_partition B.
      Var.Map.Tactics.reflect_partition.
      2:{
        Var.Map.Tactics.rewrite_map (T'!B).
        repeat rewrite Var.Map.Proofs.concat_assoc.
        reflexivity.
      }
      {
        Var.Map.Tactics.rewrite_map (M2!B).
        Var.Map.Tactics.rewrite_map (T1'!B).
        Var.simplify.
      }
  }


  apply IfDelay.
    2:{
      intros Z.
      Actor.simplify.
      intros [H0 [H1 | [H2 | H3]]]; subst.
      { apply (H_in_A_l); auto. }
      { apply (Hempty1 Z). Actor.simplify. }
      { apply (Hempty2 Z). Actor.simplify. }
    }

    assert (Hpart0 :
        Var.Map.Partition (T!A) 
          (T''!A)
          (Var.Map.concat   ThetaA
          (Var.Map.concat   (T'0!A)
                            (T0'!A)))).
      {
        ChorEnv.specialize_partition A.
        Var.Map.Tactics.reflect_partition.
        2:{
          Var.Map.Tactics.rewrite_map (T!A).
          Var.Map.Tactics.rewrite_map (T1'!A).
          Var.Map.Tactics.rewrite_map (M2!A).
          repeat rewrite Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym _ (T''!A)).
          repeat rewrite Var.Map.Proofs.concat_assoc.
          Var.simplify.
          {
            Var.simplify.
          }
        }
        Var.Map.Tactics.rewrite_map (T1'!A).
        Var.Map.Tactics.rewrite_map (M2!A).
        Var.simplify.
        repeat split; auto;
          apply Var.Map.Proofs.disjoint_sym; auto.
      }
      pose proof (H_partition_pairs _ _ Hpart0) as H00.
      (* H00 : T'!A == T2'!A ++ ThetaA ++ T'0!A ++ T0'!A *)


    eapply Weakening.cfg_weakening
      with (A0 := A)
        (Theta := Var.Map.concat ThetaA (T'0!A));
        eauto.
    + admit (* true *).
    + ChorEnv.specialize_partition A.
      Var.Map.Tactics.reflect_partition.
      2:{
        Var.Map.Tactics.rewrite_map (T1'!A).
        Var.Map.Tactics.rewrite_map (M2!A).
        repeat rewrite Var.Map.Proofs.concat_assoc.
        Var.simplify.
      }
      {
        Var.Map.Tactics.rewrite_map (T1'!A).
        Var.Map.Tactics.rewrite_map (M2!A).
        Var.simplify.
      }
      
    + unfold T2'' in *. repeat rewrite ChorEnv_concat_find.
        clear T2''.
      ChorEnv.specialize_partition A.
      apply partition_sym.
      Var.simplify.
      
    + intros B0 HB0.
      ChorEnv.specialize_partition B0.
      Var.Map.Tactics.reflect_partition.
      Var.Map.Tactics.rewrite_map (T1'!B0).
      Var.Map.Tactics.rewrite_map (M2!B0).
      unfold Actor.Map.singleton. ChorEnv.simplify.

      (* We don't know that B0 ∉ C1 ∪ C2 ... 
         I think we might need a stronger version of the weakening lemma?
      *)
      admit.

    + intros B0 HB0.
      ChorEnv.specialize_partition B0.
      Var.Map.Tactics.reflect_partition.
      unfold T2'' in *. repeat rewrite ChorEnv_concat_find.
        clear T2''.
      Var.Map.Tactics.rewrite_map (T1'!B0).
      Var.Map.Tactics.rewrite_map (M2!B0).
      unfold Actor.Map.singleton. ChorEnv.simplify.

      (* We don't know that B0 ∉ C1 ∪ C2 ... 
         I think we might need a stronger version of the weakening lemma?
      *)
      admit.

Admitted.


Lemma partition_except_transitivity : forall l T T1 T1',
    Partition_except l T T1 ->
    Partition_except l T1 T1' ->
    Partition_except l T T1'.
Proof.
  intros ? ? ? ? [T0 [H1 H2]] [T0' [H3 H4]].
  exists (ChorEnv_concat T0 T0').
  split.
  * intros A.
    rewrite ChorEnv_concat_find.
    specialize (H1 A).
    specialize (H3 A).
    Var.Map.Tactics.reflect_partition.
    2:{
      Var.Map.Tactics.rewrite_map (T ! A).
      Var.Map.Tactics.rewrite_map (T1 ! A).
      repeat rewrite <- Var.Map.Proofs.concat_assoc.
      rewrite (Var.Map.Proofs.concat_sym (T0' ! A));
        [ try reflexivity | Var.simplify ].
    }
    Var.Map.Tactics.rewrite_map (T1 ! A).
    Var.simplify.
    
  * intros B HB.
    rewrite ChorEnv_concat_find.
    rewrite (H2 B); auto.
    rewrite (H4 B); auto.
    Var.simplify.
    
Qed.


(*
Lemma partition_except_implies : forall l T T',
  Partition_except l T T' ->
  exists T0, 
    ChorEnv.Partition T T' T0
    /\
    (forall B, Actor.FSet.In B (Label.actors l) ->
      Var.Map.Empty (T0!B)).
Proof.
  intros l T T' [Hpart1 Hpart2].
  exists (ChorEnv_map (Actor.Map.domain T) (fun B => ))
*)

Lemma delay_inversion_IfDelay_exact :
  forall A e C1 C2 C T cfg C' T' cfg' l,
    (ChorEnv.WellScoped T cfg ->
     forall G D T1',
       Partition_except l T T1' ->
       WellTyped G D T1' C ->
       exists T2',
         step C T1' cfg l C' T2' cfg' /\
         Step_partition_pairs T T1' T' T2') ->
    Actor.FSet.Empty (Actor.FSet.inter
      (Label.actors l)
      (Actor.FSet.add A
        (Actor.FSet.union (Choreography.actors C1)
          (Choreography.actors C2)))) ->
    ChorEnv.WellScoped T cfg ->
    forall G D T1',
      Partition_except l T T1' ->
      WellTyped G D T1' (Choreography.If A e C1 C2 C) ->
      exists T2',
        step (Choreography.If A e C1 C2 C) T1' cfg l
          (Choreography.If A e C1 C2 C') T2' cfg' /\
        Step_partition_pairs T T1' T' T2'.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? IH Hempty HWS ? ? ? Hpart HWT.
  inversion HWT; subst; clear HWT.
  assert (HA : ~ Actor.FSet.In A (Label.actors l)).
  { intros ?. apply (Hempty A). Actor.simplify. }
  edestruct IH as [T2' [Hstep IH']];
    [auto | | eauto | ].
  
  2:{

    destruct Hpart as [? [Hpart1 Hpart2]].
    eapply delay_inversion_IfDelay; auto; eauto.
    { 
      intros Z. specialize (Hempty Z).
      Actor.simplify.
    }
    { 
      intros Z. specialize (Hempty Z).
      Actor.simplify.
    }
    {
      intros. rewrite Hpart2; auto.
      Var.simplify.
    }
    
  }

  (* Hypothesis: Partition_except l T T1' 
     says that T and T1' are equal on everything in l,
     and that T1' ⊆ T for everything not in l.
     WTS: Partition_except l T T'' 
      i.e. that T and T'' are equal on everything in l,
      and that T'' ⊆ T for everything not in l.

      We know that T1' == [A ↦ ThetaA] ++ T'0 ++ T''
      The only trick is to show that for things in l,
      (A ↦ ThetaA) ++ T'0 is empty.
     *)


    eapply partition_except_transitivity; eauto.
    exists (ChorEnv_concat (Actor.Map.singleton A ThetaA) T'0).
    split.
    + intros B.
      ChorEnv.specialize_partition B.
      Var.Map.Tactics.reflect_partition'.
      Var.Map.Tactics.rewrite_map (T1'!B).
      Var.Map.Tactics.rewrite_map (M2!B).
      apply partition_sym.
      repeat rewrite ChorEnv_concat_find.
      Var.Map.Tactics.reflect_partition.
      2:{
        repeat rewrite Var.Map.Proofs.concat_assoc.
        reflexivity.
      }
      Var.simplify.
      

    + intros B HB.
      repeat rewrite ChorEnv_concat_find.
      unfold Actor.Map.singleton.
      ChorEnv.simplify.
      apply Var.Map.Proofs.empty_map_equal.
      match goal with
      | [ H : ChorEnv.EmptyExcept _ T'0 |- _ ] =>
        apply H
      end.
      intros HB'. apply (Hempty B).
      Actor.simplify.
Qed.

Lemma concat_idempotent : forall {T} (m1 m2 : Var.Map.t T),
  (forall x, Var.Map.In x m1 -> Var.Map.find x m1 = Var.Map.find x m2) ->
  Var.Map.Equal (Var.Map.concat m1 m2) m2.
Admitted.

Lemma delay_inversion : forall C1 T1 cfg1 l C2 T2 cfg2,
    step C1 T1 cfg1 l C2 T2 cfg2 ->
    ChorEnv.WellScoped T1 cfg1 ->    
    forall G D T1',
      Partition_except l T1 T1' ->
      WellTyped G D T1' C1 ->
      exists T2',
        step C1 T1' cfg1 l C2 T2' cfg2 /\
          Step_partition_pairs T1 T1' T2 T2'.
(* Proof.
  intros C1 C2 T1 cfg1 l T2 cfg2 Hstep.
  induction Hstep.
  - intros HWS G D T1' HPex HWT.
    destruct (delay_inversion_C _ _ _ _ _ _ _ _ H HWS G D T1'
                HPex HWT) as [T2' [Hstep' Hparts]].
    exists T2'; split; [econstructor; eauto | exact Hparts].
  - intros HWS G D T1' HPex HWT.
    destruct HPex as [_ Hsame].
    assert (HAin : Actor.FSet.In A (Label.actors (Label.Loc A))).
    { unfold Label.actors; Actor.simplify. }
    assert (Hactive : Var.Map.Equal (ChorEnv.find A T)
                       (ChorEnv.find A T1')).
    { apply Hsame; exact HAin. }
    exists (Actor.Map.add A TA' T1'); split.
    + eapply IfC.
      * rewrite <- Hactive; exact H.
      * intros B0; ChorEnv.simplify.
    + unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      unfold ChorEnv.Equal in H0.
      specialize (H0 D0).
      rewrite H0.
      Actor.Map.Tactics.compare D0 A.
      * assert (Htheta : Var.Map.Equal Theta0 (Var.Map.empty nat)).
        {
          eapply partition_functional_2.
          - rewrite Hactive in Hparts; exact Hparts.
          - apply Var.Map.Proofs.partition_empty_r.
        }
        rewrite Htheta.
        ChorEnv.simplify.
        apply Var.Map.Proofs.partition_empty_r.
      * repeat rewrite find_ab_neq2 by auto.
        exact Hparts.
  - intros HWS G D T1' HPex HWT.
    destruct (delay_inversion_B _ _ _ _ _ _ _ H HWS G D T1'
                HPex HWT) as [T2' [Hstep' Hparts]].
    exists T2'; split; [econstructor; eauto | exact Hparts].

    (* Case Delay *)
  - intros HWS G D T1' HPex HWT.
    inversion HWT; subst.
    
      
      + (* I = EPR *)
        apply IHHstep in H3; auto.
        destruct H3 as [T2' [IHstep IHpart]].
        eexists.
        split; eauto.
        apply Delay; auto.

      + (* I = Send *)
        destruct HPex as [HPpart HPeq].

        assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
        { intros Hin. apply (H A). simpl. Actor.simplify. }
        apply HPpart in Hin.
        destruct Hin as [ThetaA HpartA].

        apply IHHstep in H4; auto.
        2:{
          split.
          {
            intros D0 HD0.
            apply HPpart in HD0.
            destruct HD0 as [ThetaD0 Hpart0].
            Actor.Map.Tactics.compare D0 A.
            {
              ChorEnv.simplify.
              assert (Heq : Var.Map.Equal (ChorEnv.find D0 T) (Var.Map.concat (Var.Map.concat ThetaA1 ThetaA2) ThetaD0)).
              {
                Var.Map.Tactics.reflect_partition. rewrite Heq. rewrite Heq1. reflexivity.
              }
              assert (Hdisj : Var.Map.Properties.Disjoint ThetaA1 ThetaD0).
              {
                Var.Map.Tactics.reflect_partition.
                rewrite Heq2 in *.
                Var.simplify.
              }

              
              exists (Var.Map.concat ThetaD0 ThetaA1).
              rewrite Heq.
              Var.Map.Tactics.reflect_partition;
                rewrite Heq2 in *;
                Var.simplify.
              {
                split; auto. apply Var.Map.Proofs.disjoint_sym; auto.
              }
              {
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- (Var.Map.Proofs.concat_assoc).
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaD0);
                  auto.
                reflexivity.
              }
            }
            { (* D0 <> A *)
              exists ThetaD0.
              ChorEnv.simplify.
            }
          }
          {
            intros D0 HD0.
            assert (D0 <> A).
            { inversion 1; subst. apply (H A). simpl. Actor.simplify. }
            ChorEnv.simplify.
          }
        }
        
        destruct H4 as [T2' [IHstep IHpart]].

        Var.Map.Tactics.reflect_partition.
        rewrite Heq0 in *.
        ChorEnv.simplify.

        
        eexists.
        split.
        { 
          apply Delay; eauto.
          (* Know: C / (T1',A[ThetaA2]) -l-> C' / T2' *)
          (* A ∉ l *)
          (* WTS exists T2'', C / T1' -l-> C' / ??? *)
          (* Because A ∉ l, we know exists ThetaA, T[A] == T1'[A]+ThetaA *)

          (* cfg_weakening says that because
             T1'[A] == ThetaA1 ++ ThetaA2 == ThetaA1 ++ (T1',A[ThetaA2])[A],
             and C / (T1',A[ThetaA2]) -l-> C' / T2',
             then whenever ???[A] = ThetaA1 ++ T2'[A],
             then we can conclude that C / T1' -l-> C' / ???
          *)
          eapply Weakening.cfg_weakening with (A0 := A)
                                     (T1 := Actor.Map.add A ThetaA2 T1')
                                     (T2' := Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
            eauto;
            intros; ChorEnv.simplify.
          { inversion HWT; subst. eapply WellTyped_WellFormed; eauto. }
          {
            rewrite Heq0.
            Var.Map.Tactics.reflect_partition; [ | reflexivity ]; auto.
          }
          {
            unfold Step_partition_pairs in IHpart.
            specialize (IHpart A).

            (* ALERT *)
            assert (Var.Map.Partition (ChorEnv.find A T') (ChorEnv.find A T2') (Var.Map.concat ThetaA ThetaA1)).
            {
              (* ALERT KEY!!! *)
              apply IHpart.
              ChorEnv.simplify.

              rewrite Heq.
              { (*associativity and symmetry *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }
            ChorEnv.simplify.
          }
        }
        { (* Step_partition_pairs *)
          intros D0 ThetaD0 HpartD0.
          unfold Step_partition_pairs in IHpart.
          Actor.Map.Tactics.compare D0 A.
          { (* D0 = A *)
            assert (HeqAD : Var.Map.Equal ThetaD0 ThetaA).
            {
              eapply partition_functional_2; eauto.
              rewrite Heq0 in *; Var.simplify.
            }
            rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.

            assert (HpartD0 : Var.Map.Partition (ChorEnv.find D0 T') (ChorEnv.find D0 T2')
                                (Var.Map.concat ThetaA1 ThetaA)).
            {
              apply IHpart.
              ChorEnv.simplify.
              rewrite Heq.
              { (* associativity and commutativity *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }

            ChorEnv.simplify.
            {
              rewrite Heq2.
              (*commutativity and associativity*)
                rewrite (Var.Map.Proofs.concat_sym); auto.
                2:{ Var.simplify. }
                repeat rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA); auto.
                2:{ auto with extra_var_db. }
                reflexivity.
            }
            
          }
          { (* D0 <> A *)
            ChorEnv.simplify.
            apply IHpart.
            ChorEnv.simplify.
          }

        }

      + (* I = LetBang *)
        assert (Actor.FSet.In A (Insn.actors (Insn.LetBang A x e))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.

        assert (Partition_except l T (Actor.Map.add A ThetaA2 T1')) as HPex'.
        {
          unfold Partition_except in HPex.
          destruct HPex as [HPexA HPexB].
          
          unfold Partition_except.
          split.
          {
            intros.
            assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
            tauto.
            {
              rewrite <- HAeqA0 in *.
              rewrite find_add; auto.

              destruct (HPexA A H0) as [Theta HPexAninl].

              exists (Var.Map.concat Theta ThetaA1).

              destruct
                (partitioning
                   (ChorEnv.find A T) ThetaA1 Theta (ChorEnv.find A T1') ThetaA2
                   (@Var.Map.Properties.Partition_sym _
                      (ChorEnv.find A T) (ChorEnv.find A T1') Theta HPexAninl)
                   H8) as [HPartA [HPartB [HPartC HPartD]]].

              apply
                (@Var.Map.Properties.Partition_sym _
                   (ChorEnv.find A T) (Var.Map.concat Theta ThetaA1) ThetaA2 HPartC).
            }
            {
              destruct (HPexA A0 H0) as [Theta HPexAninl].
              rewrite find_ab_neq2; eauto.
            }
          }
          {
            intros.
            specialize (HPexB A0 H0).
            pose proof (members_dj A0 A
                          (Label.actors l)
                          (Insn.actors (Insn.LetBang A x e)) H H0 HAinI).
            rewrite find_ab_neq2; auto.
          }
        }

        specialize (IHHstep HWS
                      (ChorEnv.add A x tau G)
                      (Actor.Map.add A DeltaA2 D)
                      (Actor.Map.add A ThetaA2 T1')
                      HPex' H3).

        destruct IHHstep as [T2 [IHHstepA IHHstepB]].

        pose proof IHHstepB as HSPP.
        pose proof IHHstepB as HSPP2.
        unfold Step_partition_pairs in IHHstepB.
        unfold Partition_except in HPex'.
        destruct HPex' as [HPex'A HPex'B].

        destruct (HPex'A A (inter_nin A (Label.actors l)
                              (Insn.actors (Insn.LetBang A x e)) H HAinI)) as [ThetaEx1 Hpart1].

        rewrite find_add in Hpart1.
        specialize (IHHstepB A ThetaEx1).
        rewrite find_add in IHHstepB.
        specialize (IHHstepB Hpart1).

        specialize (HSPP A ThetaEx1).
        rewrite find_add in HSPP.
        specialize (HSPP Hpart1).

        destruct HPex as [HPexA HPexB].
        specialize (HPexA A (inter_nin A (Label.actors l)
                               (Insn.actors (Insn.LetBang A x e)) H HAinI)) as [ThetaEx2 Hpart2].

        pose proof Hpart1 as HACCUMULATE.

        destruct (Var.Map.Proofs.partition_concat (ChorEnv.find A T) (ChorEnv.find A T1') ThetaEx2) as [Hpc2 _].
        destruct (Hpc2 Hpart2) as [Hdj2 Haccume2]; clear Hpc2.
        destruct (Var.Map.Proofs.partition_concat (ChorEnv.find A T1') ThetaA1 ThetaA2) as [Hpc3 _].
        destruct (Hpc3 H8) as [Hdj3 Haccume3]; clear Hpc3.

        rewrite Haccume3 in Haccume2.
        rewrite Haccume2 in HACCUMULATE.
        rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2 Hdj3) in HACCUMULATE.
        rewrite <- Var.Map.Proofs.concat_assoc in HACCUMULATE.
        rewrite Haccume3 in Hdj2.
                 
        pose proof
          (Var.Map.Proofs.disjoint_sym (Var.Map.concat ThetaA1 ThetaA2) ThetaEx2 Hdj2) as Hdj4.
        rewrite Var.Map.Proofs.concat_disjoint in Hdj4.
        destruct Hdj4 as [Hgoal1 Hgoal2].

        assert (Var.Map.Properties.Disjoint (Var.Map.concat ThetaA1 ThetaEx2) ThetaA2) as Hnomono1.
        {
          apply dj_concat_dj.
          apply (Var.Map.Proofs.disjoint_sym ThetaEx2 ThetaA1 Hgoal1).
          apply (Var.Map.Proofs.disjoint_sym ThetaEx2 ThetaA2 Hgoal2).
          auto.
        }

        pose proof (concat_partition ThetaA2 (Var.Map.concat ThetaA1 ThetaEx2)
                      (Var.Map.Proofs.disjoint_sym (Var.Map.concat ThetaA1 ThetaEx2)
                         ThetaA2 Hnomono1)) as Hnomono2.

        pose proof (partition_functional_2 nat
                      (Var.Map.concat ThetaA2 (Var.Map.concat ThetaA1 ThetaEx2))
                      ThetaA2 ThetaEx1 (Var.Map.concat ThetaA1 ThetaEx2)
                      HACCUMULATE Hnomono2) as Hnomono3.

        rewrite Hnomono3 in HSPP.
        
        destruct (Var.Map.Proofs.partition_concat
                    (ChorEnv.find A T') (ChorEnv.find A T2) (Var.Map.concat ThetaA1 ThetaEx2)) as [Hpc1 _].
        destruct (Hpc1 HSPP) as [Hdj1 Haccume1]; clear Hpc1.

        rewrite Var.Map.Proofs.concat_disjoint in Hdj1.
        destruct Hdj1 as [Hnomono4 _].
        apply Var.Map.Proofs.disjoint_sym in Hnomono4; auto.

        pose proof (concat_partition ThetaA1 (ChorEnv.find A T2) Hnomono4) as Hcrux.
        
        assert (Heq : forall B0, B0 <> A -> Var.Map.Equal (ChorEnv.find B0 T1') (ChorEnv.find B0 (Actor.Map.add A ThetaA2 T1'))).
        { intros B0 HB0. ChorEnv.simplify. }
        assert (Heq' : forall B0, B0 <> A -> Var.Map.Equal (ChorEnv.find B0 (Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2)) T2)) (ChorEnv.find B0 T2)).
        { intros B0 HB0. ChorEnv.simplify. }
        assert (HWF : Choreography.WellFormed C).
        { inversion HWT; subst. eapply WellTyped_WellFormed; eauto. }

        pose proof (cfg_weakening
                      C (Actor.Map.add A ThetaA2 T1') cfg l C' T2 cfg'
                      IHHstepA
                      HWF
                      T1'
                      (Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2)) T2)
                      ThetaA1 A) as Hsw.
        
        rewrite find_add in Hsw; auto.
        rewrite find_add in Hsw; auto.

        specialize (Hsw H8 Hcrux Heq Heq').

        exists (Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2)) T2).
        split.
        {
          apply Delay.
          { auto. }
          { auto. }
        }
        {          
          unfold Step_partition_pairs.
          intros A0 ThetaEx0 Hspps.
          assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
          tauto.
          {
            rewrite <- HAeqA0 in *.
            rewrite find_add; auto.

            unfold Step_partition_pairs in HSPP2.

            specialize (HSPP2 A).

            assert (Var.Map.Partition
                      (ChorEnv.find A T)
                      (ChorEnv.find A (Actor.Map.add A ThetaA2 T1'))
                      (Var.Map.concat ThetaEx0 ThetaA1)) as Hcrux2.
            {
              rewrite find_add; auto.

              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A T) (ChorEnv.find A T1') ThetaEx0 Hspps) as Hspps_sym.

              pose proof (partitioning
                            (ChorEnv.find A T) ThetaA1 ThetaEx0 (ChorEnv.find A T1') ThetaA2
                            Hspps_sym H8) as [HpA [HpB [HpC HpD]]].

              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A T) (Var.Map.concat ThetaEx0 ThetaA1) ThetaA2
                            HpC) as HpC_sym.
              auto.
            }
            specialize (HSPP2 (Var.Map.concat ThetaEx0 ThetaA1) Hcrux2).
            rewrite find_add in Hcrux2.

            assert (Var.Map.Properties.Disjoint ThetaEx0 ThetaA1).
            {
              destruct (Var.Map.Proofs.partition_concat
                          (ChorEnv.find A T) (ChorEnv.find A T1') ThetaEx0) as [Hpc _].
              destruct (Hpc Hspps) as [HpcA _].
              pose proof (@Var.Map.Properties.Disjoint_sym _
                            (ChorEnv.find A T1') ThetaEx0 HpcA) as HpcA_sym.
              apply (partition_dj ThetaEx0 (ChorEnv.find A T1') ThetaA1 ThetaA2 HpcA_sym H8).
            }

            destruct (Var.Map.Proofs.partition_concat
                        (ChorEnv.find A T') (ChorEnv.find A T2)
                        (Var.Map.concat ThetaEx0 ThetaA1)) as [Hpc _].
            destruct (Hpc HSPP2) as [HpcA _].
            
            apply (partition_concat_assoc
                     (ChorEnv.find A T') (ChorEnv.find A T2)
                     ThetaEx0 ThetaA1 HpcA H0 HSPP2).
          }
          {
            rewrite find_ab_neq2; auto.
            unfold Step_partition_pairs in HSPP2.
            specialize (HSPP2 A0).
            rewrite find_ab_neq2 in HSPP2; auto.
          }
        }

      + (* I = Let *)
        destruct HPex as [HPpart HPeq].

        assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
        { intros Hin. apply (H A). simpl. Actor.simplify. }
        apply HPpart in Hin.
        destruct Hin as [ThetaA HpartA].

        apply IHHstep in H3; auto.
        2:{
          split.
          {
            intros D0 HD0.
            apply HPpart in HD0.
            destruct HD0 as [ThetaD0 Hpart0].
            Actor.Map.Tactics.compare D0 A.
            {
              ChorEnv.simplify.
              assert (Heq : Var.Map.Equal (ChorEnv.find D0 T) (Var.Map.concat (Var.Map.concat ThetaA1 ThetaA2) ThetaD0)).
              {
                Var.Map.Tactics.reflect_partition. rewrite Heq. rewrite Heq1. reflexivity.
              }
              assert (Hdisj : Var.Map.Properties.Disjoint ThetaA1 ThetaD0).
              {
                Var.Map.Tactics.reflect_partition.
                rewrite Heq2 in *.
                Var.simplify.
              }

              
              exists (Var.Map.concat ThetaD0 ThetaA1).
              rewrite Heq.
              Var.Map.Tactics.reflect_partition;
                rewrite Heq2 in *;
                Var.simplify.
              {
                split; auto. apply Var.Map.Proofs.disjoint_sym; auto.
              }
              {
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- (Var.Map.Proofs.concat_assoc).
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaD0);
                  auto.
                reflexivity.
              }
            }
            { (* D0 <> A *)
              exists ThetaD0.
              ChorEnv.simplify.
            }
          }
          {
            intros D0 HD0.
            assert (D0 <> A).
            { inversion 1; subst. apply (H A). simpl. Actor.simplify. }
            ChorEnv.simplify.
          }
        }
        
        destruct H3 as [T2' [IHstep IHpart]].

        Var.Map.Tactics.reflect_partition.
        rewrite Heq0 in *.
        ChorEnv.simplify.

        
        eexists.
        split.
        { 
          apply Delay; eauto.
          (* Know: C / (T1',A[ThetaA2]) -l-> C' / T2' *)
          (* A ∉ l *)
          (* WTS exists T2'', C / T1' -l-> C' / ??? *)
          (* Because A ∉ l, we know exists ThetaA, T[A] == T1'[A]+ThetaA *)

          (* cfg_weakening says that because
             T1'[A] == ThetaA1 ++ ThetaA2 == ThetaA1 ++ (T1',A[ThetaA2])[A],
             and C / (T1',A[ThetaA2]) -l-> C' / T2',
             then whenever ???[A] = ThetaA1 ++ T2'[A],
             then we can conclude that C / T1' -l-> C' / ???
          *)
          eapply cfg_weakening with (A0 := A)
                                     (T1 := Actor.Map.add A ThetaA2 T1')
                                     (T2' := Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
            eauto;
            intros; ChorEnv.simplify.
          { inversion HWT; subst. eapply WellTyped_WellFormed; eauto. }
          { rewrite Heq0. ChorEnv.simplify.
            Var.Map.Tactics.reflect_partition; [ | reflexivity ]; auto.
          }
          {
            unfold Step_partition_pairs in IHpart.
            specialize (IHpart A).

            (* ALERT *)
            assert (Var.Map.Partition (ChorEnv.find A T') (ChorEnv.find A T2') (Var.Map.concat ThetaA ThetaA1)).
            {
              (* ALERT KEY!!! *)
              apply IHpart.
              ChorEnv.simplify.

              rewrite Heq.
              { (*associativity and symmetry *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }
            ChorEnv.simplify.
          }
        }
        { (* Step_partition_pairs *)
          intros D0 ThetaD0 HpartD0.
          unfold Step_partition_pairs in IHpart.
          Actor.Map.Tactics.compare D0 A.
          { (* D0 = A *)
            assert (HeqAD : Var.Map.Equal ThetaD0 ThetaA).
            {
              eapply partition_functional_2; eauto.
              rewrite Heq0 in *; Var.simplify.
            }
            rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.

            assert (HpartD0 : Var.Map.Partition
                                (ChorEnv.find D0 T') (ChorEnv.find D0 T2') (Var.Map.concat ThetaA1 ThetaA)).
            {
              apply IHpart.
              ChorEnv.simplify.
              rewrite Heq.
              { (* associativity and commutativity *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }

            ChorEnv.simplify.
            {
              rewrite Heq2.
              (*commutativity and associativity*)
                rewrite (Var.Map.Proofs.concat_sym); auto.
                2:{ Var.simplify. }
                repeat rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA); auto.
                2:{ auto with extra_var_db. }
                reflexivity.
            }
            
          }
          { (* D0 <> A *)
            ChorEnv.simplify.
            apply IHpart.
            ChorEnv.simplify.
          }

        }

      + (* I = LetPair *)
        destruct HPex as [HPpart HPeq].

        assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
        { intros Hin. apply (H A). simpl. Actor.simplify. }
        apply HPpart in Hin.
        destruct Hin as [ThetaA HpartA].

        apply IHHstep in H3; auto.
        2:{
          split.
          {
            intros D0 HD0.
            apply HPpart in HD0.
            destruct HD0 as [ThetaD0 Hpart0].
            Actor.Map.Tactics.compare D0 A.
            {
              ChorEnv.simplify.
              assert (Heq : Var.Map.Equal (ChorEnv.find D0 T) (Var.Map.concat (Var.Map.concat ThetaA1 ThetaA2) ThetaD0)).
              {
                Var.Map.Tactics.reflect_partition. rewrite Heq. rewrite Heq1. reflexivity.
              }
              assert (Hdisj : Var.Map.Properties.Disjoint ThetaA1 ThetaD0).
              {
                Var.Map.Tactics.reflect_partition.
                rewrite Heq2 in *.
                Var.simplify.
              }

              
              exists (Var.Map.concat ThetaD0 ThetaA1).
              rewrite Heq.
              Var.Map.Tactics.reflect_partition;
                rewrite Heq2 in *;
                Var.simplify.
              {
                split; auto. apply Var.Map.Proofs.disjoint_sym; auto.
              }
              {
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- (Var.Map.Proofs.concat_assoc).
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaD0);
                  auto.
                reflexivity.
              }
            }
            { (* D0 <> A *)
              exists ThetaD0.
              ChorEnv.simplify.
            }
          }
          {
            intros D0 HD0.
            assert (D0 <> A).
            { inversion 1; subst. apply (H A). simpl. Actor.simplify. }
            ChorEnv.simplify.
          }
        }
        
        destruct H3 as [T2' [IHstep IHpart]].

        Var.Map.Tactics.reflect_partition.
        rewrite Heq0 in *.
        ChorEnv.simplify.

        
        eexists.
        split.
        { 
          apply Delay; eauto.
          (* Know: C / (T1',A[ThetaA2]) -l-> C' / T2' *)
          (* A ∉ l *)
          (* WTS exists T2'', C / T1' -l-> C' / ??? *)
          (* Because A ∉ l, we know exists ThetaA, T[A] == T1'[A]+ThetaA *)

          (* cfg_weakening says that because
             T1'[A] == ThetaA1 ++ ThetaA2 == ThetaA1 ++ (T1',A[ThetaA2])[A],
             and C / (T1',A[ThetaA2]) -l-> C' / T2',
             then whenever ???[A] = ThetaA1 ++ T2'[A],
             then we can conclude that C / T1' -l-> C' / ???
          *)
          eapply cfg_weakening with (A0 := A)
                                     (T1 := Actor.Map.add A ThetaA2 T1')
                                     (T2' := Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
            eauto;
            intros; ChorEnv.simplify.

          { inversion HWT; subst. eapply WellTyped_WellFormed; eauto. }
          { rewrite Heq0.
            Var.Map.Tactics.reflect_partition; [ | reflexivity ]; auto.
          }
          {
            unfold Step_partition_pairs in IHpart.
            specialize (IHpart A).

            (* ALERT *)
            assert (Var.Map.Partition (ChorEnv.find A T') (ChorEnv.find A T2') (Var.Map.concat ThetaA ThetaA1)).
            {
              (* ALERT KEY!!! *)
              apply IHpart.
              ChorEnv.simplify.

              rewrite Heq.
              { (*associativity and symmetry *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }
            ChorEnv.simplify.
          }
        }
        { (* Step_partition_pairs *)
          intros D0 ThetaD0 HpartD0.
          unfold Step_partition_pairs in IHpart.
          Actor.Map.Tactics.compare D0 A.
          { (* D0 = A *)
            assert (HeqAD : Var.Map.Equal ThetaD0 ThetaA).
            {
              eapply partition_functional_2; eauto.
              rewrite Heq0 in *; Var.simplify.
            }
            rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.

            assert (HpartD0 : Var.Map.Partition
                                (ChorEnv.find D0 T') (ChorEnv.find D0 T2') (Var.Map.concat ThetaA1 ThetaA)).
            {
              apply IHpart.
              ChorEnv.simplify.
              rewrite Heq.
              { (* associativity and commutativity *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }

            ChorEnv.simplify.
            {
              rewrite Heq2.
              (*commutativity and associativity*)
                rewrite (Var.Map.Proofs.concat_sym); auto.
                2:{ Var.simplify. }
                repeat rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA); auto.
                2:{ auto with extra_var_db. }
                reflexivity.
            }
            
          }
          { (* D0 <> A *)
            ChorEnv.simplify.
            apply IHpart.
            ChorEnv.simplify.
          }
        }

    - (* IfDelay plan:
         Invert HWT to obtain the continuation typing under
         Actor.Map.add A ThetaA3 T1'. The IfDelay disjointness premise
         gives A not in Label.actors l. Extend HPex to this actor-specific
         environment by composing its partition at A with the If typing
         partitions; other actors keep their existing partitions.
         Apply IHHstep to the continuation. Then use cfg_weakening to add
         ThetaA1 and ThetaA2 back at A, producing the continuation step
         required by IfDelay. Extend Step_partition_pairs with the same
         context at A; use the induction result for other actors.
       *)
      assert (HA : ~ Actor.FSet.In A (Label.actors l)).
      { intros Hin. apply (H A). Actor.simplify. }
      assert (H1 : Actor.FSet.Empty (Actor.FSet.inter (Label.actors l) (Choreography.actors C1))).
      { intros A0 Hin. apply (H A0). Actor.simplify. }
      assert (H2 : Actor.FSet.Empty (Actor.FSet.inter (Label.actors l) (Choreography.actors C2))).
      { intros A0 Hin. apply (H A0). Actor.simplify. }
      rename H into Hin.

      intros HWS G D T1' Hpart HWT.
      inversion HWT; subst; clear HWT.
        rename H6 into HWTe, H7 into HWTC1, H8 into HWTC2, H12 into HWTC,
          H13 into HpartD, H14 into HpartD', H15 into HpartT, H16 into HpartT'.


      destruct Hpart as [Hpart1 Hpart2].

      destruct (IHHstep HWS G (Actor.Map.add A DeltaA3 D) (Actor.Map.add A ThetaA3 T1')) as [T2' [IHstep IHpart]]; auto.
      { (* partition_except case *)
        split.
        + intros A0 HA0.
          specialize (Hpart1 A0 HA0); destruct Hpart1 as [ThetaA1' Hpart1].
          Actor.Map.Tactics.compare A A0.
          { (* A = A0 *)
            exists (Var.Map.concat ThetaA1 (Var.Map.concat ThetaA2 ThetaA1')). rewrite find_add.
            Var.Map.Tactics.reflect_partition.
            { rewrite Heq in Hdisj3.
              Var.simplify.
              repeat split; auto;
              apply Var.Map.Proofs.disjoint_sym; auto.
            }
            
            rewrite Heq1.
            rewrite Heq.
            repeat rewrite Var.Map.Proofs.concat_assoc.
            apply Var.Map.Proofs.concatProper;
              try reflexivity.
            rewrite Var.Map.Proofs.concat_sym at 1;
              [ | Var.simplify ].
            repeat rewrite <- Var.Map.Proofs.concat_assoc.
            reflexivity.
          }
          { (* A <> A0 *)
            eexists.
            ChorEnv.simplify.
            eauto.
          }

        + intros A0 HA0.
          Actor.Map.Tactics.compare A A0.
          ChorEnv.simplify.
      }


      (* inductive case *)

      specialize (Hpart1 A HA); destruct Hpart1 as [ThetaA1' Hpart1].
      (* Hpart1 : T[A] = T1'[A] ++ ThetaA1' *)
      
      assert (IHpart' : Var.Map.Partition
        (ChorEnv.find A T')
        (ChorEnv.find A T2') 
        (Var.Map.concat ThetaA1 (Var.Map.concat ThetaA2 ThetaA1'))).
      {
        apply IHpart; clear IHpart.
        rewrite find_add.
        Var.Map.Tactics.reflect_partition.
        {
          rewrite Heq in Hdisj3.
          Var.simplify.
          repeat split; auto;
          apply Var.Map.Proofs.disjoint_sym; auto.
        }
        match goal with
        | [ Heq : Var.Map.Equal (ChorEnv.find A T) _ |- _ ] =>
          rewrite Heq
        end.
        match goal with
        | [ Heq : Var.Map.Equal (ChorEnv.find A T1') _ |- _ ] =>
          rewrite Heq
        end.
        repeat rewrite Var.Map.Proofs.concat_assoc.
        apply Var.Map.Proofs.concatProper;
            [ | reflexivity].
        rewrite Var.Map.Proofs.concat_sym with (m2 := ThetaA3).
        repeat rewrite Var.Map.Proofs.concat_assoc.
        reflexivity.
        Var.simplify.
      }

      
      (*eexists. (* T2' *)*)
      (*T2' = T2'[A ↦ ThetaA1 ++ ThetaA2 ++ T2'[A]]*)
      exists (Actor.Map.add A (Var.Map.concat (Var.Map.concat ThetaA1 ThetaA2) (ChorEnv.find A T2')) T2').
      split.
      2:{
        unfold Step_partition_pairs in *.
        intros A0 Theta HpartA0.
        Actor.Map.Tactics.compare A0 A.
        + (* A = A0 *)
          rewrite find_add.
          (* Heq3 : T[A0] == ThetaA1 ++ ThetaA2 ++ ThetaA3 ++ ThetaA1' *)
          (* Heq0 : T'[A0] == T2'[A0] ++ ThetaA1 ++ ThetaA2 ++ ThetaA1' *)
          (* Heq : T[A0] == ThetaA1 ++ ThetaA2 ++ ThetaA3 ++ Theta *)
          assert (HTheta : Var.Map.Equal Theta ThetaA1').
          { (* concat_inversion_eq *)
            Var.Map.Tactics.reflect_partition.
            rewrite Heq3 in *.
            apply concat_inversion_eq with (m := ChorEnv.find A0 T1'); auto.
            symmetry; auto.
          }
          rewrite HTheta in *; clear Theta HTheta.
          
          Var.Map.Tactics.reflect_partition.
          { match goal with
            | [ H : Var.Map.Equal ?A ?B, H' : Var.Map.Properties.Disjoint ?A _ |- _ ] => rewrite H in *
            | [ H : Var.Map.Equal ?A ?B, H' : Var.Map.Properties.Disjoint _ ?A |- _ ] => rewrite H in *
            end.
            Var.simplify.
          }
          {
            repeat match goal with
            | [ H : Var.Map.Equal ?A ?B, H' : Var.Map.Properties.Disjoint ?A _ |- _ ] => rewrite H in *; clear H
            | [ H : Var.Map.Equal ?A ?B, H' : Var.Map.Properties.Disjoint _ ?A |- _ ] => rewrite H in *; clear H
            | [ H : Var.Map.Equal ?A ?B |- Var.Map.Equal ?A _ ] => rewrite H in *; clear H
            end.
            repeat rewrite Var.Map.Proofs.concat_assoc.
            apply Var.Map.Proofs.concatProper;
              [ | reflexivity].
            rewrite (Var.Map.Proofs.concat_sym _ (ChorEnv.find A0 T2')); [ | Var.simplify].
            repeat rewrite Var.Map.Proofs.concat_assoc.
            reflexivity.
          }

        + (* A <> A0 *)
          ChorEnv.simplify.
          apply IHpart.
          ChorEnv.simplify.
      }
      apply IfDelay; eauto.


          (* cfg_weakening says that because
             T1'[A] == ThetaA1 ++ ThetaA2 == ThetaA1 ++ (T1',A[ThetaA2])[A],
             and C / (T1',A[ThetaA3]) -l-> C' / T2',
             then whenever ???[A] = ThetaA3 ++ T2'[A],
             then we can conclude that C / T1' -l-> C' / ???
          *)
          eapply Weakening.cfg_weakening with (A0 := A)
              (Theta := Var.Map.concat ThetaA1 ThetaA2); eauto.
          { eapply WellTyped_WellFormed; eauto. }
          3:{ intros ? ?. ChorEnv.simplify. }

          (* T1'[A] == Theta ++ Theta3 *)
          (* Because T1'[A] == ThetaA1 ++ ThetaA'
                            == ThetaA1 ++ ThetaA2 ++ ThetaA3 
             Therefore Theta = ThetaA1 ++ ThetaA2
            *)
          {
            ChorEnv.simplify. 
            Var.Map.Tactics.reflect_partition.
            rewrite Heq0.
            repeat rewrite Var.Map.Proofs.concat_assoc.
            reflexivity.
          }

          2:{ intros. ChorEnv.simplify. }

          rewrite find_add.
          Var.Map.Tactics.reflect_partition; [ | reflexivity].
          Var.simplify.
Qed. *)
Proof.
  intros C1 T1 cfg1 l C2 T2 cfg2 Hstep.
  induction Hstep.
  - (* StepC: delegate to delay_inversion_C. *)
    intros HWS G D T1' Hpart HWT.
    destruct (delay_inversion_C _ _ _ _ _ _ _ _ H HWS G D T1'
      Hpart HWT) as [T2' [Hstep' Hparts]].
    exists T2'; split; [econstructor; eauto | exact Hparts].
  - (* IfC: preserve the active actor's environment update. *)
    intros HWS G D T1' Hpart HWT.
    destruct Hpart as [T0 [Hpart Hsame]].
    assert (HAin : Actor.FSet.In A (Label.actors (Label.Loc A))).
    { unfold Label.actors; Actor.simplify. }
    assert (Hactive : Var.Map.Equal (ChorEnv.find A T)
                       (ChorEnv.find A T1')).
    { 
      ChorEnv.specialize_partition A.
      Var.Map.Tactics.reflect_partition'.
      Var.Map.Tactics.rewrite_map (T!A).
      rewrite Hsame.
      2:{ simpl; Actor.simplify. }
      autorewrite with var_db.
      reflexivity.
    }
    exists (Actor.Map.add A TA' T1'); split.
    + eapply IfC.
      * rewrite <- Hactive; exact H.
      * intros B0; ChorEnv.simplify.
    + unfold Step_partition_pairs; intros D0 Theta0 Hparts.
      unfold ChorEnv.Equal in H0.
      specialize (H0 D0).
      rewrite H0.
      Actor.Map.Tactics.compare D0 A.
      * assert (Htheta : Var.Map.Equal Theta0 (Var.Map.empty nat)).
        {
          eapply partition_functional_2.
          - rewrite Hactive in Hparts; exact Hparts.
          - apply Var.Map.Proofs.partition_empty_r.
        }
        rewrite Htheta.
        ChorEnv.simplify.
        apply Var.Map.Proofs.partition_empty_r.
      * repeat rewrite find_ab_neq2 by auto.
        exact Hparts.
  - (* StepB: delegate to delay_inversion_B. *)
    intros HWS G D T1' Hpart HWT.
    destruct (delay_inversion_B _ _ _ _ _ _ _ H HWS G D T1'
      HWT) as [T2' [Hstep' Hparts]].
    exists T2'; split; [econstructor; eauto | exact Hparts].
  - (* Delay: invert typing, then handle each instruction form. *)
    intros HWS G D T1' Hpart HWT.
    inversion HWT; subst.
    + (* EPR continuation. *)
      apply IHHstep in H3; auto.
      destruct H3 as [T2' [IHstep IHpart]].
      eexists.
      split; eauto.
      apply Delay; auto.
    + (* Send continuation. *)

      destruct Hpart as [T0 [Hpart Hsame]].
      assert (HAin : Actor.FSet.In A (Label.actors (Label.Loc A))).
      { unfold Label.actors; Actor.simplify. }

      assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
      { intros Hin. apply (H A). simpl. Actor.simplify. }
      Var.Map.Tactics.reflect_partition.

      apply IHHstep in H4; auto.
      2:{
        
        exists (ChorEnv_concat (Actor.Map.singleton A ThetaA1) T0).
        (* T == T1' ++ T0 *)
        split.
        2:{
          intros B0 HB0.
          repeat rewrite ChorEnv_concat_find.
          unfold Actor.Map.singleton.
          ChorEnv.simplify.
        }
        {
          intros D0.
          rewrite ChorEnv_concat_find.
          unfold Actor.Map.singleton.

          ChorEnv.specialize_partition D0.
          Var.Map.Tactics.reflect_partition'.
          Var.Map.Tactics.rewrite_map (T!D0).

          Actor.Map.Tactics.compare A D0.
              {
                Var.Map.Tactics.rewrite_map (T1'!A).
                repeat rewrite find_add.
                Var.Map.Tactics.reflect_partition.
                {
                  Var.simplify. split; auto.
                  apply Var.Map.Proofs.disjoint_sym; auto.
                }
                repeat rewrite Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); [ reflexivity | auto ].
                
              }
              {
                autorewrite with var_db.
                Actor.simplify.
                autorewrite with var_db.
                Var.Map.Tactics.reflect_partition; [ | reflexivity].
                Var.simplify.
              }

        }

      }

      destruct H4 as [T2' [IHstep IHpart]].
      Var.Map.Tactics.reflect_partition.
      
      eexists.
      split.
      {
        apply Delay; eauto.
        eapply Weakening.cfg_weakening with (A0 := A)
          (T1 := Actor.Map.add A ThetaA2 T1')
          (T2' := Actor.Map.add A
            (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
          eauto; intros; ChorEnv.simplify.
        { inversion HWT; subst.
          eapply WellTyped_WellFormed; eauto.
        }
        {
          Var.Map.Tactics.rewrite_map (T1' ! A).
          Var.Map.Tactics.reflect_partition; [| reflexivity]; auto.
        }
        {
          unfold Step_partition_pairs in IHpart.
          specialize (IHpart A).
          assert (Var.Map.Partition (ChorEnv.find A T')
            (ChorEnv.find A T2') (Var.Map.concat (T0!A) ThetaA1)).
          {
            apply IHpart.
            autorewrite with var_db.
            Actor.simplify.
            specialize (Hpart A).
            Var.Map.Tactics.reflect_partition'.
            Var.Map.Tactics.rewrite_map (T!A).
            Var.Map.Tactics.rewrite_map (T1'!A).
            apply partition_sym.

            Var.Map.Tactics.reflect_partition.
            { Var.simplify. }
            repeat rewrite (Var.Map.Proofs.concat_sym _ (T0!A)).
            2:{ Var.simplify. }
            repeat rewrite Var.Map.Proofs.concat_assoc.
            reflexivity.
          }
          Var.Map.Tactics.reflect_partition;
            [ Var.simplify | reflexivity].

        }
      }
      {
        intros D0 ThetaD0 HpartD0.
        unfold Step_partition_pairs in IHpart.
        Actor.Map.Tactics.compare D0 A.
        - assert (HeqAD : Var.Map.Equal ThetaD0 (T0!D0)).
          {
            eapply partition_functional_2; eauto.
          }
          rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.
          assert (HpartD0 : Var.Map.Partition
            (ChorEnv.find D0 T') (ChorEnv.find D0 T2')
            (Var.Map.concat ThetaA1 (T0!D0))).
          {
            apply IHpart.
            autorewrite with var_db. Actor.simplify.
            specialize (Hpart D0).
            Var.Map.Tactics.reflect_partition'.
            Var.Map.Tactics.rewrite_map (T!D0).
            Var.Map.Tactics.rewrite_map (T1'!D0).
            
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
              auto.
            repeat rewrite <- Var.Map.Proofs.concat_assoc.
            Var.Map.Tactics.reflect_partition;
              [Var.simplify | reflexivity].
            split; auto. apply Var.Map.Proofs.disjoint_sym; auto.
          }

          rewrite find_add.
          specialize (Hpart D0).
          Var.Map.Tactics.reflect_partition'.
          Var.Map.Tactics.rewrite_map (T'!D0).
          repeat rewrite Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym ThetaA1); auto.
          2:{ Var.simplify. }
          Var.Map.Tactics.reflect_partition;
            [ | reflexivity].
          {
            Var.Map.Tactics.rewrite_map (T1'!D0).
            Var.simplify.
          }
          
        - Var.simplify. Actor.simplify.
          apply IHpart.
          Var.simplify. Actor.simplify.
      }
    + (* LetBang continuation. *)

    inversion HWT; subst; clear HWT.
    destruct Hpart as [T0' [Hpart Hempty]].

    (* Step 1 *)
    set (T1'' := Actor.Map.add A ThetaA2 T1').
    assert (Hpart' : Partition_except l T T1'').
    {
      set (T0'' := Actor.Map.add A (Var.Map.concat ThetaA1 (T0'!A)) T0').
      exists T0''.
      
      split.
      2:{
        intros B HB.
        unfold T0''.
        autorewrite with var_db.
        Actor.simplify.
        subst.
        exfalso.
        apply (H A).
        simpl; Actor.simplify.
      }

      intros B.
      Actor.Map.Tactics.compare A B.
      2:{ (* A <> B *)
        unfold T1'', T0''.
        autorewrite with var_db.
        Actor.simplify.
        subst; contradiction.
      }
      { (* A = B *)
        unfold T1'', T0''.
        repeat rewrite find_add.
        specialize (Hpart A).
        Var.Map.Tactics.reflect_partition'.
        Var.Map.Tactics.rewrite_map (T!A).
        rewrite Heq1 in *.
        
        Var.Map.Tactics.reflect_partition.
        {
          Var.simplify.
          split; auto.
          apply Var.Map.Proofs.disjoint_sym; auto.
        }
        {
          repeat rewrite Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym ThetaA1);
            auto.
          reflexivity.
        }
      }
      
    }


    edestruct IHHstep
      with (T1' := T1'')
      as [T2 [HS HP]]; auto; eauto.

    (* Step 2 *)
    set (T2' := (Actor.Map.add A (Var.Map.concat ThetaA1 (T2!A)) T2)).
    exists T2'.

    (* Step 3 *)

    (* T!A == T1'!A ++ T0'!A 
           == ThetaA1 ++ ThetaA2 ++ T0'!A

    OTOH,
      T1''!A ++ ThetaA1 ++ T2!A
          == ThetaA2 ++ ThetaA1 ++ T0'!A
    *)
    assert (HTA : Var.Map.Partition (T!A) (T1''!A) 
      (Var.Map.concat ThetaA1 (T0'!A))).
    {
      ChorEnv.specialize_partition A.
      Var.Map.Tactics.reflect_partition'.
      unfold T1''. rewrite find_add.
      Var.Map.Tactics.rewrite_map (T!A).
      rewrite Heq1 in *.
      
      Var.Map.Tactics.reflect_partition.
      { Var.simplify. split; auto.
        apply Var.Map.Proofs.disjoint_sym; auto.
      }
      repeat rewrite Var.Map.Proofs.concat_assoc.
      rewrite (Var.Map.Proofs.concat_sym ThetaA1); auto.
      reflexivity.
    }

    assert (Hdisj : Var.Map.Properties.Disjoint ThetaA1 (T2!A)).
    {
      apply HP in HTA.
      Var.Map.Tactics.reflect_partition'.
      Var.simplify.
    }

    split.

    * (* Step 4 *)

      apply Delay; auto.
      apply Weakening.cfg_weakening
        with (T1 := T1'')
             (T1' := T2)
             (T2 := T1')
             (T2' := T2')
             (A0 := A)
             (Theta := ThetaA1);
        auto.
      { eapply WellTyped_WellFormed; eauto. }
      {
        unfold T1''.
        rewrite find_add.
        auto.
      }
      {
        unfold T2'.
        rewrite find_add.
        Var.Map.Tactics.reflect_partition;
          [Var.simplify | reflexivity].
      }
      { (* B <> A *)
        intros B0 HB0.
        unfold T1''.
        autorewrite with var_db.
        Actor.simplify.
      }
      { (* B <> A *)
        intros B0 HB0.
        unfold T2'.
        autorewrite with var_db.
        Actor.simplify.
      }

    * (* Step 5 *)
      intros B Theta HpartB.
      Actor.Map.Tactics.compare A B.

      2:{ (* A <> B *)
        specialize (Hpart B).
        unfold T2'.
        autorewrite with var_db.
        Actor.simplify; subst; try contradiction.
        apply (HP B).
        unfold T1''.
        autorewrite with var_db.
        Actor.simplify;
          subst; try contradiction.
      }

      { (* A = B *)
        (* Claim: T!A == ThetaA2 ++ (ThetaA1 ++ Theta)*)
        set (Theta' := Var.Map.concat ThetaA1 Theta).
        assert (HTA' : Var.Map.Partition
          (T!A) ThetaA2 Theta').
        {
          specialize (Hpart A).
          Var.Map.Tactics.reflect_partition'.
          Var.Map.Tactics.rewrite_map (T!A).
          rewrite Heq3 in *.
          unfold Theta' in *.
          Var.Map.Tactics.reflect_partition.
          { Var.simplify.
            split; auto.
            apply Var.Map.Proofs.disjoint_sym; auto.
          }
          repeat rewrite Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym ThetaA1); auto.
          reflexivity.
        }
        

        specialize (HP A Theta').
        unfold T1'' in HP.
        rewrite find_add in HP.
        pose proof (HP HTA') as HP'.

        Var.Map.Tactics.reflect_partition'.
        Var.Map.Tactics.rewrite_map (T'!A).

        unfold T2', Theta' in *.
        rewrite find_add.

        assert (Var.Map.Properties.Disjoint (T1'!A) Theta).
        {
          Var.Map.Tactics.reflect_partition.
          Var.simplify.
        }
        Var.Map.Tactics.reflect_partition'.

        match goal with
        | [ H : Var.Map.Equal (T1'!A) (Var.Map.concat ThetaA1 ThetaA2) |- _ ] =>
          rewrite H in *
        end.

        (*
        assert (Disjoint (T2!A) ThetaA1)
        assert (Disjoint ThetaA1 Theta)
        assert (Disjoint (T2!A) Theta).
        *)

        Var.Map.Tactics.reflect_partition.
        { Var.simplify. }
        repeat rewrite Var.Map.Proofs.concat_assoc.
        rewrite (Var.Map.Proofs.concat_sym _ ThetaA1); [ reflexivity | ].
        Var.simplify.

      }
    





    (*
      assert (Actor.FSet.In A (Insn.actors (Insn.LetBang A x e))) as HAinI.
      { unfold Insn.actors. Actor.simplify. }
      assert (Partition_except l T (Actor.Map.add A ThetaA2 T1')) as HPex'.
      {
        unfold Partition_except in Hpart.
        destruct Hpart as [T0 [HPexA HPexB]].
        unfold Partition_except.
        
        exists (ChorEnv_concat (Actor.Map.singleton A ThetaA1) T0).
        (* T == T1' ++ T0 *)
        split.
        2:{
          intros B0 HB0.
          repeat rewrite ChorEnv_concat_find.
          unfold Actor.Map.singleton.
          autorewrite with var_db.
          Actor.Map.Tactics.compare A B0.
          {
            exfalso.
            apply (H A).
            simpl; Actor.simplify.
          }
          Actor.simplify.
          Var.simplify.
        }
        {
          intros D0.
          rewrite ChorEnv_concat_find.
          unfold Actor.Map.singleton.
          autorewrite with var_db.

          ChorEnv.specialize_partition D0.
          Var.Map.Tactics.reflect_partition'.
          Var.Map.Tactics.rewrite_map (T!D0).

          Actor.Map.Tactics.compare A D0.
              {
                Var.Map.Tactics.rewrite_map (T1'!A).
                Actor.simplify.
                Var.Map.Tactics.reflect_partition.
                {
                  Var.simplify. split; auto.
                  apply Var.Map.Proofs.disjoint_sym; auto.
                }
                repeat rewrite Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); [ reflexivity | auto ].
                
              }
              {
                autorewrite with var_db.
                Actor.simplify.
                autorewrite with var_db.
                Var.Map.Tactics.reflect_partition; [ | reflexivity].
                Var.simplify.
              }

        }
      }


      specialize (IHHstep HWS (ChorEnv.add A x tau G)
        (Actor.Map.add A DeltaA2 D) (Actor.Map.add A ThetaA2 T1')
        HPex' H3).
      destruct IHHstep as [T2 [IHHstepA IHHstepB]].
      (*pose proof IHHstepB as HSPP.
      pose proof IHHstepB as HSPP2.*)
      unfold Step_partition_pairs in IHHstepB.
      destruct HPex' as [T0 [HPex'A Hpex'B]].
      destruct Hpart as [T0' [Hpart0 Hpart0']].
      (* T == T1' ++ T0' *)

      (*
      exists (Actor.Map.add A
        (Var.Map.concat ThetaA1 (T2!A)) T2).
        *)
        
      eexists.
      split.
      2:{
        intros B ThetaB HpartB.
        ChorEnv.specialize_partition B.
        Var.Map.Tactics.reflect_partition'.
        Search T. (* Heq, Heq3, Heq0 *)
        assert (HThetaB : Var.Map.Equal ThetaB (T0'!B)).
        { 
          Var.Map.Tactics.rewrite_map (T!B).
          eapply concat_disjoint_injective; [ | | eauto ];
            Var.simplify.
        }
        rewrite HThetaB in *; clear ThetaB HThetaB.


        clear Heq3.
        (*
          T1'!A == ThetaA1 ++ ThetaA2

          Heq : T!B == T1'!B ++ T0'!B
          Heq0 : T!B == (T1',A ↦ ThetaA2)!B ++ T0!B
        *)
        
        assert (H000 : Var.Map.Partition (T!B) (Actor.Map.add A ThetaA2 T1' ! B) (T0!B)). admit.
        apply IHHstepB in H000.

        Var.Map.Tactics.reflect_partition'.
        rewrite Heq3 at 1.
        
        rewrite Heq in Heq0.
        (* T1'!B ++ T0' == (T1',A ↦ ThetaA2)!B ++ T0!B *)
        Search T0.


        Actor.Map.Tactics.compare A B.
        { (* B = A *)
          rewrite find_add.
          assert (H0 : Map.Partition (T!A) ThetaA2 ((Actor.Map.add A (Var.Map.concat ThetaA1 (T2!A)) T2) !A)).
          admit.
          apply HSPP in H0.
          rewrite find_add in H0.
          Var.Map.Tactics.reflect_partition'.
          assert (Var.Map.Equal (T2!A) (Var.Map.empty _)).
          {
            intros y. Var.simplify.
            destruct (Map.find y (T2!A)) eqn:Hfind; auto.
            {
              exfalso.
              match goal with
              | [ H : Var.Map.Properties.Disjoint (T2!A) (T2!A) |- _ ] =>
                apply (H y)
              end.
              Var.solve.
            }
          }
          Var.Map.Tactics.rewrite_map (T'!A).
          Var.Map.Tactics.rewrite_map (T2!A).
          Var.simplify.
          Search T.
          
        }
        { (* B <> A *)
          autorewrite with var_db.
          Actor.simplify.
          apply IHHstepB.
          autorewrite with var_db.
          Actor.simplify.
        }
        Var.Map.reflect_partition'.
        apply IHHstepB.
        Search T'.
        (* Know:
            T!B == T1'!B ++ ThetaB
          Also:
            IHHstepB : T'!B == T2!B ++ Theta0
              where T!B == (T1',A ↦ ThetaA2)!B ++ Theta0
        *)
        assert (HThetaB : Var.Map.Equal ThetaB _).

      }

      specialize (HSPP _ Hpart1).
      destruct Hpart as [HPexA HPexB].
      specialize (HPexA A
        (inter_nin A (Label.actors l)
          (Insn.actors (Insn.LetBang A x e)) H HAinI))
        as [ThetaEx2 Hpart2].
      pose proof Hpart1 as HACCUMULATE.
      destruct (Var.Map.Proofs.partition_concat
        (ChorEnv.find A T) (ChorEnv.find A T1') ThetaEx2)
        as [Hpc2 _].
      destruct (Hpc2 Hpart2) as [Hdj2 Haccume2]; clear Hpc2.
      destruct (Var.Map.Proofs.partition_concat
        (ChorEnv.find A T1') ThetaA1 ThetaA2) as [Hpc3 _].
      destruct (Hpc3 H8) as [Hdj3 Haccume3]; clear Hpc3.
      rewrite Haccume3 in Haccume2.
      rewrite Haccume2 in HACCUMULATE.
      rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2 Hdj3)
        in HACCUMULATE.
      rewrite <- Var.Map.Proofs.concat_assoc in HACCUMULATE.
      rewrite Haccume3 in Hdj2.
      pose proof
        (Var.Map.Proofs.disjoint_sym
          (Var.Map.concat ThetaA1 ThetaA2) ThetaEx2 Hdj2) as Hdj4.
      rewrite Var.Map.Proofs.concat_disjoint in Hdj4.
      destruct Hdj4 as [Hgoal1 Hgoal2].
      assert (Var.Map.Properties.Disjoint
        (Var.Map.concat ThetaA1 ThetaEx2) ThetaA2) as Hnomono1.
      {
        apply dj_concat_dj.
        apply (Var.Map.Proofs.disjoint_sym ThetaEx2 ThetaA1 Hgoal1).
        apply (Var.Map.Proofs.disjoint_sym ThetaEx2 ThetaA2 Hgoal2).
        auto.
      }
      pose proof (concat_partition ThetaA2
        (Var.Map.concat ThetaA1 ThetaEx2)
        (Var.Map.Proofs.disjoint_sym
          (Var.Map.concat ThetaA1 ThetaEx2) ThetaA2 Hnomono1))
        as Hnomono2.
      pose proof (partition_functional_2 nat
        (Var.Map.concat ThetaA2 (Var.Map.concat ThetaA1 ThetaEx2))
        ThetaA2 ThetaEx1 (Var.Map.concat ThetaA1 ThetaEx2)
        HACCUMULATE Hnomono2) as Hnomono3.
      rewrite Hnomono3 in HSPP.
      destruct (Var.Map.Proofs.partition_concat
        (ChorEnv.find A T') (ChorEnv.find A T2)
        (Var.Map.concat ThetaA1 ThetaEx2)) as [Hpc1 _].
      destruct (Hpc1 HSPP) as [Hdj1 Haccume1]; clear Hpc1.
      rewrite Var.Map.Proofs.concat_disjoint in Hdj1.
      destruct Hdj1 as [Hnomono4 _].
      apply Var.Map.Proofs.disjoint_sym in Hnomono4; auto.
      pose proof (concat_partition ThetaA1 (ChorEnv.find A T2)
        Hnomono4) as Hcrux.
      assert (Heq : forall B0, B0 <> A ->
        Var.Map.Equal (ChorEnv.find B0 T1')
          (ChorEnv.find B0 (Actor.Map.add A ThetaA2 T1'))).
      { intros B0 HB0. ChorEnv.simplify. }
      assert (Heq' : forall B0, B0 <> A ->
        Var.Map.Equal
          (ChorEnv.find B0
            (Actor.Map.add A
              (Var.Map.concat ThetaA1 (ChorEnv.find A T2)) T2))
          (ChorEnv.find B0 T2)).
      { intros B0 HB0. ChorEnv.simplify. }
      assert (HWF : Choreography.WellFormed C).
      { inversion HWT; subst. eapply WellTyped_WellFormed; eauto. }
      pose proof (cfg_weakening C
        (Actor.Map.add A ThetaA2 T1') cfg l C' T2 cfg'
        IHHstepA HWF T1'
        (Actor.Map.add A
          (Var.Map.concat ThetaA1 (ChorEnv.find A T2)) T2)
        ThetaA1 A) as Hsw.
      rewrite find_add in Hsw; auto.
      rewrite find_add in Hsw; auto.
      specialize (Hsw H8 Hcrux Heq Heq').
      exists (Actor.Map.add A
        (Var.Map.concat ThetaA1 (ChorEnv.find A T2)) T2).
      split.
      {
        apply Delay; auto.
      }
      {
        unfold Step_partition_pairs.
        intros A0 ThetaEx0 Hspps.
        destruct (Actor.eq_dec A A0) as [HAeqA0 | HneqA0].
        - rewrite <- HAeqA0 in *.
          rewrite find_add; auto.
          unfold Step_partition_pairs in HSPP2.
          specialize (HSPP2 A).
          assert (Var.Map.Partition
            (ChorEnv.find A T)
            (ChorEnv.find A (Actor.Map.add A ThetaA2 T1'))
            (Var.Map.concat ThetaEx0 ThetaA1)) as Hcrux2.
          {
            rewrite find_add; auto.
            pose proof (@Var.Map.Properties.Partition_sym _
              (ChorEnv.find A T) (ChorEnv.find A T1') ThetaEx0 Hspps)
              as Hspps_sym.
            pose proof (partitioning (ChorEnv.find A T) ThetaA1
              ThetaEx0 (ChorEnv.find A T1') ThetaA2 Hspps_sym H8)
              as [HpA [HpB [HpC HpD]]].
            pose proof (@Var.Map.Properties.Partition_sym _
              (ChorEnv.find A T)
              (Var.Map.concat ThetaEx0 ThetaA1) ThetaA2 HpC)
              as HpC_sym.
            exact HpC_sym.
          }
          specialize (HSPP2 (Var.Map.concat ThetaEx0 ThetaA1) Hcrux2).
          rewrite find_add in Hcrux2.
          assert (Var.Map.Properties.Disjoint ThetaEx0 ThetaA1).
          {
            destruct (Var.Map.Proofs.partition_concat
              (ChorEnv.find A T) (ChorEnv.find A T1') ThetaEx0)
              as [Hpc _].
            destruct (Hpc Hspps) as [HpcA _].
            pose proof (@Var.Map.Properties.Disjoint_sym _
              (ChorEnv.find A T1') ThetaEx0 HpcA) as HpcA_sym.
            apply (partition_dj ThetaEx0 (ChorEnv.find A T1')
              ThetaA1 ThetaA2 HpcA_sym H8).
          }
          destruct (Var.Map.Proofs.partition_concat
            (ChorEnv.find A T') (ChorEnv.find A T2)
            (Var.Map.concat ThetaEx0 ThetaA1)) as [Hpc _].
          destruct (Hpc HSPP2) as [HpcA _].
          apply (partition_concat_assoc (ChorEnv.find A T')
            (ChorEnv.find A T2) ThetaEx0 ThetaA1 HpcA H0 HSPP2).
        - rewrite find_ab_neq2; auto.
          unfold Step_partition_pairs in HSPP2.
          specialize (HSPP2 A0).
          rewrite find_ab_neq2 in HSPP2; auto.
      }

      *)
    + (* Let continuation. *)
      destruct Hpart as [T0 [Hpart Hsame]].
      assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
      { intros Hin. apply (H A). simpl. Actor.simplify. }
      Var.Map.Tactics.reflect_partition.

      apply IHHstep in H3; auto.
      2:{
        exists (ChorEnv_concat (Actor.Map.singleton A ThetaA1) T0).
        split.
        2:{
          intros B0 HB0.
          repeat rewrite ChorEnv_concat_find.
          unfold Actor.Map.singleton.
          ChorEnv.simplify.
        }
        {
          intros D0.
          rewrite ChorEnv_concat_find.
          unfold Actor.Map.singleton.
          ChorEnv.specialize_partition D0.
          Var.Map.Tactics.reflect_partition'.
          Var.Map.Tactics.rewrite_map (T!D0).
          Actor.Map.Tactics.compare A D0.
          {
            Var.Map.Tactics.rewrite_map (T1'!A).
            repeat rewrite find_add.
            Var.Map.Tactics.reflect_partition.
            {
              Var.simplify. split; auto.
              apply Var.Map.Proofs.disjoint_sym; auto.
            }
            repeat rewrite Var.Map.Proofs.concat_assoc.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
              [ reflexivity | auto ].
          }
          {
            autorewrite with var_db.
            Actor.simplify.
            autorewrite with var_db.
            Var.Map.Tactics.reflect_partition; [ | reflexivity].
            Var.simplify.
          }
        }
      }

      destruct H3 as [T2' [IHstep IHpart]].
      Var.Map.Tactics.reflect_partition.

      eexists.
      split.
      {
        apply Delay; eauto.
        eapply Weakening.cfg_weakening with (A0 := A)
          (T1 := Actor.Map.add A ThetaA2 T1')
          (T2' := Actor.Map.add A
            (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
          eauto; intros; ChorEnv.simplify.
        { inversion HWT; subst.
          eapply WellTyped_WellFormed; eauto.
        }
        {
          Var.Map.Tactics.rewrite_map (T1' ! A).
          Var.Map.Tactics.reflect_partition; [| reflexivity]; auto.
        }
        {
          unfold Step_partition_pairs in IHpart.
          specialize (IHpart A).
          assert (Var.Map.Partition (ChorEnv.find A T')
            (ChorEnv.find A T2') (Var.Map.concat (T0!A) ThetaA1)).
          {
            apply IHpart.
            autorewrite with var_db.
            Actor.simplify.
            specialize (Hpart A).
            Var.Map.Tactics.reflect_partition'.
            Var.Map.Tactics.rewrite_map (T!A).
            Var.Map.Tactics.rewrite_map (T1'!A).
            apply partition_sym.
            Var.Map.Tactics.reflect_partition.
            { Var.simplify. }
            repeat rewrite (Var.Map.Proofs.concat_sym _ (T0!A)).
            2:{ Var.simplify. }
            repeat rewrite Var.Map.Proofs.concat_assoc.
            reflexivity.
          }
          Var.Map.Tactics.reflect_partition;
            [ Var.simplify | reflexivity].
        }
      }
      {
        intros D0 ThetaD0 HpartD0.
        unfold Step_partition_pairs in IHpart.
        Actor.Map.Tactics.compare D0 A.
        - assert (HeqAD : Var.Map.Equal ThetaD0 (T0!D0)).
          {
            eapply partition_functional_2; eauto.
          }
          rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.
          assert (HpartD0 : Var.Map.Partition
            (ChorEnv.find D0 T') (ChorEnv.find D0 T2')
            (Var.Map.concat ThetaA1 (T0!D0))).
          {
            apply IHpart.
            autorewrite with var_db. Actor.simplify.
            specialize (Hpart D0).
            Var.Map.Tactics.reflect_partition'.
            Var.Map.Tactics.rewrite_map (T!D0).
            Var.Map.Tactics.rewrite_map (T1'!D0).
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
              auto.
            repeat rewrite <- Var.Map.Proofs.concat_assoc.
            Var.Map.Tactics.reflect_partition;
              [Var.simplify | reflexivity].
            split; auto. apply Var.Map.Proofs.disjoint_sym; auto.
          }
          rewrite find_add.
          specialize (Hpart D0).
          Var.Map.Tactics.reflect_partition'.
          Var.Map.Tactics.rewrite_map (T'!D0).
          repeat rewrite Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym ThetaA1); auto.
          2:{ Var.simplify. }
          Var.Map.Tactics.reflect_partition;
            [ | reflexivity].
          {
            Var.Map.Tactics.rewrite_map (T1'!D0).
            Var.simplify.
          }
        - Var.simplify. Actor.simplify.
          apply IHpart.
          Var.simplify. Actor.simplify.
      }
(* Legacy Let continuation proof, kept for reference.
      destruct Hpart as [HPpart HPeq].
      assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
      { intros Hin. apply (H A). simpl. Actor.simplify. }
      apply HPpart in Hin.
      destruct Hin as [ThetaA HpartA].
      apply IHHstep in H3; auto.
      2:{
        split.
        - intros D0 HD0.
          apply HPpart in HD0.
          destruct HD0 as [ThetaD0 Hpart0].
          Actor.Map.Tactics.compare D0 A.
          + ChorEnv.simplify.
            assert (Heq : Var.Map.Equal (ChorEnv.find D0 T)
              (Var.Map.concat (Var.Map.concat ThetaA1 ThetaA2)
                ThetaD0)).
            {
              Var.Map.Tactics.reflect_partition.
              rewrite Heq. rewrite Heq1. reflexivity.
            }
            assert (Hdisj : Var.Map.Properties.Disjoint ThetaA1
              ThetaD0).
            {
              Var.Map.Tactics.reflect_partition.
              rewrite Heq2 in *.
              Var.simplify.
            }
            exists (Var.Map.concat ThetaD0 ThetaA1).
            rewrite Heq.
            Var.Map.Tactics.reflect_partition;
              rewrite Heq2 in *;
              Var.simplify.
            {
              split; auto.
              apply Var.Map.Proofs.disjoint_sym; auto.
            }
            {
              rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
                auto.
              rewrite <- (Var.Map.Proofs.concat_assoc).
              rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaD0);
                auto.
              reflexivity.
            }
          + exists ThetaD0.
            ChorEnv.simplify.
        - intros D0 HD0.
          assert (D0 <> A).
          { inversion 1; subst. apply (H A). simpl. Actor.simplify. }
          ChorEnv.simplify.
      }
      destruct H3 as [T2' [IHstep IHpart]].
      Var.Map.Tactics.reflect_partition.
      rewrite Heq0 in *.
      ChorEnv.simplify.
      eexists.
      split.
      {
        apply Delay; eauto.
        eapply Weakening.cfg_weakening with (A0 := A)
          (T1 := Actor.Map.add A ThetaA2 T1')
          (T2' := Actor.Map.add A
            (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
          eauto; intros; ChorEnv.simplify.
        { inversion HWT; subst.
          eapply WellTyped_WellFormed; eauto. }
        {
          rewrite Heq0.
          Var.Map.Tactics.reflect_partition; [| reflexivity]; auto.
        }
        {
          unfold Step_partition_pairs in IHpart.
          specialize (IHpart A).
          assert (Var.Map.Partition (ChorEnv.find A T')
            (ChorEnv.find A T2') (Var.Map.concat ThetaA ThetaA1)).
          {
            apply IHpart.
            ChorEnv.simplify.
            rewrite Heq.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
              auto.
            rewrite <- Var.Map.Proofs.concat_assoc.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA);
              auto.
            reflexivity.
          }
          ChorEnv.simplify.
        }
      }
      {
        intros D0 ThetaD0 HpartD0.
        unfold Step_partition_pairs in IHpart.
        Actor.Map.Tactics.compare D0 A.
        - assert (HeqAD : Var.Map.Equal ThetaD0 ThetaA).
          {
            eapply partition_functional_2; eauto.
            rewrite Heq0 in *; Var.simplify.
          }
          rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.
          assert (HpartD0 : Var.Map.Partition
            (ChorEnv.find D0 T') (ChorEnv.find D0 T2')
            (Var.Map.concat ThetaA1 ThetaA)).
          {
            apply IHpart.
            ChorEnv.simplify.
            rewrite Heq.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
              auto.
            rewrite <- Var.Map.Proofs.concat_assoc.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA);
              auto.
            reflexivity.
          }
          ChorEnv.simplify.
          rewrite Heq2.
          rewrite (Var.Map.Proofs.concat_sym); auto.
          2:{ Var.simplify. }
          repeat rewrite <- Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym ThetaA); auto.
          2:{ auto with extra_var_db. }
          reflexivity.
        - ChorEnv.simplify.
          apply IHpart.
          ChorEnv.simplify.
      }
*)
    + (* LetPair continuation. *)
      destruct Hpart as [T0 [Hpart Hsame]].
      assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
      { intros Hin. apply (H A). simpl. Actor.simplify. }
      Var.Map.Tactics.reflect_partition.

      apply IHHstep in H3; auto.
      2:{
        exists (ChorEnv_concat (Actor.Map.singleton A ThetaA1) T0).
        split.
        2:{
          intros B0 HB0.
          repeat rewrite ChorEnv_concat_find.
          unfold Actor.Map.singleton.
          ChorEnv.simplify.
        }
        {
          intros D0.
          rewrite ChorEnv_concat_find.
          unfold Actor.Map.singleton.
          ChorEnv.specialize_partition D0.
          Var.Map.Tactics.reflect_partition'.
          Var.Map.Tactics.rewrite_map (T!D0).
          Actor.Map.Tactics.compare A D0.
          {
            Var.Map.Tactics.rewrite_map (T1'!A).
            repeat rewrite find_add.
            Var.Map.Tactics.reflect_partition.
            {
              Var.simplify. split; auto.
              apply Var.Map.Proofs.disjoint_sym; auto.
            }
            repeat rewrite Var.Map.Proofs.concat_assoc.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
              [ reflexivity | auto ].
          }
          {
            autorewrite with var_db.
            Actor.simplify.
            autorewrite with var_db.
            Var.Map.Tactics.reflect_partition; [ | reflexivity].
            Var.simplify.
          }
        }
      }

      destruct H3 as [T2' [IHstep IHpart]].
      Var.Map.Tactics.reflect_partition.

      eexists.
      split.
      {
        apply Delay; eauto.
        eapply Weakening.cfg_weakening with (A0 := A)
          (T1 := Actor.Map.add A ThetaA2 T1')
          (T2' := Actor.Map.add A
            (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
          eauto; intros; ChorEnv.simplify.
        { inversion HWT; subst.
          eapply WellTyped_WellFormed; eauto.
        }
        {
          Var.Map.Tactics.rewrite_map (T1' ! A).
          Var.Map.Tactics.reflect_partition; [| reflexivity]; auto.
        }
        {
          unfold Step_partition_pairs in IHpart.
          specialize (IHpart A).
          assert (Var.Map.Partition (ChorEnv.find A T')
            (ChorEnv.find A T2') (Var.Map.concat (T0!A) ThetaA1)).
          {
            apply IHpart.
            autorewrite with var_db.
            Actor.simplify.
            specialize (Hpart A).
            Var.Map.Tactics.reflect_partition'.
            Var.Map.Tactics.rewrite_map (T!A).
            Var.Map.Tactics.rewrite_map (T1'!A).
            apply partition_sym.
            Var.Map.Tactics.reflect_partition.
            { Var.simplify. }
            repeat rewrite (Var.Map.Proofs.concat_sym _ (T0!A)).
            2:{ Var.simplify. }
            repeat rewrite Var.Map.Proofs.concat_assoc.
            reflexivity.
          }
          Var.Map.Tactics.reflect_partition;
            [ Var.simplify | reflexivity].
        }
      }
      {
        intros D0 ThetaD0 HpartD0.
        unfold Step_partition_pairs in IHpart.
        Actor.Map.Tactics.compare D0 A.
        - assert (HeqAD : Var.Map.Equal ThetaD0 (T0!D0)).
          {
            eapply partition_functional_2; eauto.
          }
          rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.
          assert (HpartD0 : Var.Map.Partition
            (ChorEnv.find D0 T') (ChorEnv.find D0 T2')
            (Var.Map.concat ThetaA1 (T0!D0))).
          {
            apply IHpart.
            autorewrite with var_db. Actor.simplify.
            specialize (Hpart D0).
            Var.Map.Tactics.reflect_partition'.
            Var.Map.Tactics.rewrite_map (T!D0).
            Var.Map.Tactics.rewrite_map (T1'!D0).
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
              auto.
            repeat rewrite <- Var.Map.Proofs.concat_assoc.
            Var.Map.Tactics.reflect_partition;
              [Var.simplify | reflexivity].
            split; auto. apply Var.Map.Proofs.disjoint_sym; auto.
          }
          rewrite find_add.
          specialize (Hpart D0).
          Var.Map.Tactics.reflect_partition'.
          Var.Map.Tactics.rewrite_map (T'!D0).
          repeat rewrite Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym ThetaA1); auto.
          2:{ Var.simplify. }
          Var.Map.Tactics.reflect_partition;
            [ | reflexivity].
          {
            Var.Map.Tactics.rewrite_map (T1'!D0).
            Var.simplify.
          }
        - Var.simplify. Actor.simplify.
          apply IHpart.
          Var.simplify. Actor.simplify.
      }
(* Legacy LetPair continuation proof, kept for reference.
      destruct Hpart as [HPpart HPeq].
      assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
      { intros Hin. apply (H A). simpl. Actor.simplify. }
      apply HPpart in Hin.
      destruct Hin as [ThetaA HpartA].
      apply IHHstep in H3; auto.
      2:{
        split.
        - intros D0 HD0.
          apply HPpart in HD0.
          destruct HD0 as [ThetaD0 Hpart0].
          Actor.Map.Tactics.compare D0 A.
          + ChorEnv.simplify.
            assert (Heq : Var.Map.Equal (ChorEnv.find D0 T)
              (Var.Map.concat (Var.Map.concat ThetaA1 ThetaA2)
                ThetaD0)).
            {
              Var.Map.Tactics.reflect_partition.
              rewrite Heq. rewrite Heq1. reflexivity.
            }
            assert (Hdisj : Var.Map.Properties.Disjoint ThetaA1
              ThetaD0).
            {
              Var.Map.Tactics.reflect_partition.
              rewrite Heq2 in *.
              Var.simplify.
            }
            exists (Var.Map.concat ThetaD0 ThetaA1).
            rewrite Heq.
            Var.Map.Tactics.reflect_partition;
              rewrite Heq2 in *;
              Var.simplify.
            {
              split; auto.
              apply Var.Map.Proofs.disjoint_sym; auto.
            }
            {
              rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
                auto.
              rewrite <- (Var.Map.Proofs.concat_assoc).
              rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaD0);
                auto.
              reflexivity.
            }
          + exists ThetaD0.
            ChorEnv.simplify.
        - intros D0 HD0.
          assert (D0 <> A).
          { inversion 1; subst. apply (H A). simpl. Actor.simplify. }
          ChorEnv.simplify.
      }
      destruct H3 as [T2' [IHstep IHpart]].
      Var.Map.Tactics.reflect_partition.
      rewrite Heq0 in *.
      ChorEnv.simplify.
      eexists.
      split.
      {
        apply Delay; eauto.
        eapply Weakening.cfg_weakening with (A0 := A)
          (T1 := Actor.Map.add A ThetaA2 T1')
          (T2' := Actor.Map.add A
            (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
          eauto; intros; ChorEnv.simplify.
        { inversion HWT; subst.
          eapply WellTyped_WellFormed; eauto. }
        {
          rewrite Heq0.
          ChorEnv.simplify.
          Var.Map.Tactics.reflect_partition; [| reflexivity]; auto.
        }
        {
          unfold Step_partition_pairs in IHpart.
          specialize (IHpart A).
          assert (Var.Map.Partition (ChorEnv.find A T')
            (ChorEnv.find A T2') (Var.Map.concat ThetaA ThetaA1)).
          {
            apply IHpart.
            ChorEnv.simplify.
            rewrite Heq.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
              auto.
            rewrite <- Var.Map.Proofs.concat_assoc.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA);
              auto.
            reflexivity.
          }
          ChorEnv.simplify.
        }
      }
      {
        intros D0 ThetaD0 HpartD0.
        unfold Step_partition_pairs in IHpart.
        Actor.Map.Tactics.compare D0 A.
        - assert (HeqAD : Var.Map.Equal ThetaD0 ThetaA).
          {
            eapply partition_functional_2; eauto.
            rewrite Heq0 in *; Var.simplify.
          }
          rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.
          assert (HpartD0 : Var.Map.Partition
            (ChorEnv.find D0 T') (ChorEnv.find D0 T2')
            (Var.Map.concat ThetaA1 ThetaA)).
          {
            apply IHpart.
            ChorEnv.simplify.
            rewrite Heq.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2);
              auto.
            rewrite <- Var.Map.Proofs.concat_assoc.
            rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA);
              auto.
            reflexivity.
          }
          ChorEnv.simplify.
          rewrite Heq2.
          rewrite (Var.Map.Proofs.concat_sym); auto.
          2:{ Var.simplify. }
          repeat rewrite <- Var.Map.Proofs.concat_assoc.
          rewrite (Var.Map.Proofs.concat_sym ThetaA); auto.
          2:{ auto with extra_var_db. }
          reflexivity.
        - ChorEnv.simplify.
          apply IHpart.
          ChorEnv.simplify.
      }
*)
  - (* IfDelay: invert typing, restrict continuation environment,
       then weaken back and preserve the partition relation. *)
    eapply delay_inversion_IfDelay_exact; auto.
Qed.


Lemma WellTyped_preservation_stepC : forall G D T1 I C,
  WellTyped G D T1 (Choreography.Do I C) ->
  forall cfg1 l I' T2 cfg2,
    Insn.stepC I T1 cfg1 l I' T2 cfg2 ->
    ChorEnv.WellScoped T1 cfg1 ->
    (forall A, Actor.FSet.In A (Label.actors l) ->
      Var.Map.Empty (ChorEnv.find A G) /\
      Var.Map.Empty (ChorEnv.find A D)) ->
    WellTyped G D T2 (Choreography.Do I' C).
  (* Proof outline: Invert the instruction step and typing derivation. For each
     instruction constructor, use expression-step inversion and expression
     preservation, then rebuild the choreography typing rule with its context
     partitions. The continuation C remains unchanged. *)
Proof.
  intros G D T1 I C HWT cfg1 l I' T2 cfg2 Hstep Hscoped Hemptiness.
  inversion HWT; subst; clear HWT;
    inversion Hstep; subst; clear Hstep.
  - (* Send with SendC: preserve expression typing and rebuild Send. *)
      unfold  ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      {
        unfold Label.actors.
        Actor.simplify.
      }
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      Var.simplify.
      rewrite HAGempty, HADempty in *.
      Var.simplify.

      rename H14 into Hstep',
             H15 into HT2.
      eapply Expr.Preservation.step_inversion
          in Hstep'; eauto.
      destruct Hstep' as [ThetaA1' [Hstep' Hpart']].

      eapply Send 
          with (DeltaA1 := ChorEnv.find A D)
               (ThetaA1 := ThetaA1')
               (ThetaA2 := ThetaA2)
               (DeltaA2 := Var.Map.empty _);
          auto.
      {
        rewrite HAGempty, HADempty.
        eapply Expr.Preservation.WellTyped_preservation; eauto;
          Var.simplify.
        { eapply ChorEnv.ws_partition; eauto. }
      }
      {
        rewrite ChorEnv.ce_add_empty; auto.
        rewrite HT2.
        rewrite ChorEnv.addadd2.
        auto.
      }
      { auto with var_db. }
      { rewrite HT2. rewrite find_add. auto. } 

  - (* LetBang with LetBangC: preserve expression typing and rebuild LetBang. *)
      unfold  ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      {
        unfold Label.actors.
        Actor.simplify.
      }
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      Var.simplify.
      rewrite HAGempty, HADempty in *.
      Var.simplify.

      rename H12 into Hstep',
             H13 into HT2.
      eapply Expr.Preservation.step_inversion
          in Hstep'; eauto.
      destruct Hstep' as [ThetaA1' [Hstep' Hpart']].

      eapply LetBang 
          with (DeltaA1 := ChorEnv.find A D)
               (ThetaA1 := ThetaA1')
               (ThetaA2 := ThetaA2)
               (DeltaA2 := Var.Map.empty _);
          auto.
      {
        rewrite HAGempty, HADempty.
        eapply Expr.Preservation.WellTyped_preservation; eauto;
          Var.simplify.
        { eapply ChorEnv.ws_partition; eauto. }
      }
      {
        rewrite ChorEnv.ce_add_empty; auto.
        rewrite HT2.
        rewrite ChorEnv.addadd2.
        auto.
      }
      { auto with var_db. }
      { rewrite HT2. rewrite find_add. auto. } 

  - (* Let with LetC: preserve expression typing and rebuild LetIn. *)
      unfold  ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      {
        unfold Label.actors.
        Actor.simplify.
      }
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      Var.simplify.
      rewrite HAGempty, HADempty in *.
      Var.simplify.

      rename H13 into Hstep',
             H14 into HT2.
      eapply Expr.Preservation.step_inversion
          in Hstep'; eauto.
      destruct Hstep' as [ThetaA1' [Hstep' Hpart']].

      eapply LetIn
          with (DeltaA1 := ChorEnv.find A D)
               (ThetaA1 := ThetaA1')
               (ThetaA2 := ThetaA2)
               (DeltaA2 := Var.Map.empty _);
          auto.
      {
        rewrite HAGempty, HADempty.
        eapply Expr.Preservation.WellTyped_preservation; eauto;
          Var.simplify.
        { eapply ChorEnv.ws_partition; eauto. }
      }
      {
        rewrite HT2.
        rewrite ChorEnv.addadd2.
        auto.
      }
      { auto with var_db. }
      { rewrite HT2. rewrite find_add. auto. }
      { Var.simplify. } 

  - (* LetPair with LetPairC: preserve expression typing and rebuild LetPair. *)
    unfold  ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      {
        unfold Label.actors.
        Actor.simplify.
      }
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      Var.simplify.
      rewrite HAGempty, HADempty in *.
      Var.simplify.

      rename H16 into Hstep',
             H17 into HT2.
      eapply Expr.Preservation.step_inversion
          in Hstep'; eauto.
      destruct Hstep' as [ThetaA1' [Hstep' Hpart']].

      eapply LetPair
          with (DeltaA1 := ChorEnv.find A D)
               (ThetaA1 := ThetaA1')
               (ThetaA2 := ThetaA2)
               (DeltaA2 := Var.Map.empty _);
          auto.
      {
        rewrite HAGempty, HADempty.
        eapply Expr.Preservation.WellTyped_preservation; eauto;
          Var.simplify.
        { eapply ChorEnv.ws_partition; eauto. }
      }
      {
        rewrite HT2.
        rewrite ChorEnv.addadd2.
        auto.
      }
      { auto with var_db. }
      { rewrite HT2. rewrite find_add. auto. }
      { Var.simplify. } 
      { Var.simplify. } 
Qed.


Lemma WellTyped_seq_if : forall G D T A b C1 C2 C,
  WellTyped G D T (Choreography.If A (Expr.Bit b) C1 C2 C) ->
  Var.Map.Empty (ChorEnv.find A G) ->
  Var.Map.Empty (ChorEnv.find A D) ->
  WellTyped G D T
    (Choreography.seq (if b then C1 else C2) C).
(* Proof outline: Invert If typing and select the premise for branch b. Use
   the partitions of A's quantum resources and empty classical contexts to
   compose the selected branch with continuation C. Establish composition by
   induction on the branch typing derivation, using seq's recursive cases. *)
Admitted.

Lemma WellTyped_preservation_seq :
  forall G D1 T1 C1,
  WellTyped G D1 T1 C1 ->
  forall D D2 T T2 C2,
  WellTyped G D2 T2 C2 ->
  
  ChorEnv.Partition D D1 D2 ->
  ChorEnv.Partition T T1 T2 ->

  WellTyped G D T (Choreography.seq C1 C2).
Proof.
  intros ? ? ? ? HWT1.
  induction HWT1; intros ? ? ? ? ? HWT2 HpartD HpartT;
    simpl.
  * assert (HD : ChorEnv.Equal D0 D2).
    {
      intros A.
      specialize (H A).
      specialize (HpartD A).
      Var.Map.Tactics.reflect_partition.
      Var.Map.Tactics.rewrite_map (D0!A).
      Var.Map.Tactics.rewrite_map (D!A).
      Var.simplify.
    }
    assert (HT : ChorEnv.Equal T0 T2).
    {
      intros A.
      specialize (H0 A).
      specialize (HpartT A).
      Var.Map.Tactics.reflect_partition.
      Var.Map.Tactics.rewrite_map (T0!A).
      Var.Map.Tactics.rewrite_map (T!A).
      Var.simplify.
    }
    rewrite HD, HT. auto.
  * constructor; auto.
    2:{
      ChorEnv.specialize_partition A.
      Var.Map.Tactics.reflect_partition.
      Var.Map.Tactics.rewrite_map (D0!A).
      Var.simplify. split; auto.
      admit (*?*).
    }
    2:{
      ChorEnv.specialize_partition B.
      Var.Map.Tactics.reflect_partition.
      Var.Map.Tactics.rewrite_map (D0!B).
      Var.simplify. split; auto.
      admit (*?*).
    }
    { eapply IHHWT1; eauto.
      admit.
      admit.
    } 
Abort.

Lemma WellTyped_preservation_stepB : forall G D T C,
  WellTyped G D T C ->
  forall cfg1 l C' T' cfg2,
    Choreography.stepB C T cfg1 l C' T' cfg2 ->
    ChorEnv.WellScoped T cfg1 ->
    (forall A, Actor.FSet.In A (Label.actors l) ->
      Var.Map.Empty (ChorEnv.find A G) /\
      Var.Map.Empty (ChorEnv.find A D)) ->
    WellTyped G D T' C'.
(* Proof outline: Invert the beta step and typing derivation. Use substitution
   preservation for Send and let cases, and EPR inversion plus linear
   substitution for EPR. For IfB, apply WellTyped_seq_if to the selected
   branch and continuation. Rewrite environment equalities where needed. *)
Proof.
  intros G D T C HWT cfg1 l C' T' cfg2 Hstep Hscoped Hdisj.
  inversion Hstep; subst; clear Hstep;
    inversion HWT; subst; clear HWT.
  * rewrite H0; clear T' H0.
    (*eapply WellTyped_preservation_seq; eauto.
    destruct b; eauto.*)

Admitted.


(** Preservation *)
Theorem WellTyped_preservation : forall G D T1 C1,
    WellTyped G D T1 C1 ->
    forall cfg1 l C2 T2 cfg2,
      step C1 T1 cfg1 l C2 T2 cfg2 ->
      ChorEnv.WellScoped T1 cfg1 ->
        (forall A, Actor.FSet.In A (Label.actors l) ->
                   Var.Map.Empty (ChorEnv.find A G) /\  Var.Map.Empty (ChorEnv.find A D)) ->   
        WellTyped G D T2 C2.
Proof.
  (*
  intros G D T1 C1 HWT.
  intros cfg1 l C2 T2 cfg2 Hstep.
  revert G D HWT.
  induction Hstep;
    intros G D HWT Hscoped Hdisj.
  * (* stepC *)
    eapply WellTyped_preservation_stepC; eauto.
  * (* IfC *)
      inversion HWT; subst; clear HWT.
      unfold  ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      destruct (Hdisj A) as [HAGempty HADempty].
      { simpl. Actor.simplify. }
      
      Var.simplify.
      (*rewrite HAGempty, HADempty in *.
      Var.simplify.*)

      rename H into Hstep',
             H0 into HT2,
             H13 into HD,
             H14 into HT.
      specialize (HD A).
      specialize (HT A).
      rewrite HT2 in *; clear T' HT2.
      rewrite HADempty in *; rewrite HAGempty in *.
      Var.simplify.

      eapply Expr.Preservation.step_inversion
          in Hstep'; auto.
      2:{ eauto. }
      2:{ eauto with var_db. }
      destruct Hstep' as [ThetaA1' [Hstep' Hpart']].

      (* e/∅ → e'/ΘA1'.
         So there's no guarantee that e' doesn't use qubits. *)

      eapply If;
        try rewrite HAGempty in *;
        try rewrite HADempty in *;
        try rewrite HT2 in *;
        eauto.
      (*
          with  (DeltaA1 := Var.Map.empty _)
                (ThetaA1 := ThetaA1')
                (DeltaA2 := Var.Map.empty _)
                (ThetaA2 := ThetaA2)
                (DeltaA3 := Var.Map.empty _)
                (ThetaA3 := ThetaA3);
          try rewrite HAGempty in *;
          try rewrite HADempty in *;
          try rewrite HT2 in *;
          eauto.*)
      {
        eapply Expr.Preservation.WellTyped_preservation; 
          eauto;
          Var.simplify.
        
        { eapply ChorEnv.ws_partition; eauto. }
      }
      {
        rewrite ChorEnv.addadd2.
        rewrite ChorEnv.ce_add_empty; auto.
      }
      {
        rewrite ChorEnv.addadd2.
        rewrite ChorEnv.ce_add_empty; auto.
      }
      {
        rewrite ChorEnv.addadd2.
        rewrite ChorEnv.ce_add_empty; auto.
      }
      { auto with var_db. }
      { auto with var_db. }
      { Var.simplify. Actor.simplify. } 
  
  * (* stepB *)
    eapply WellTyped_preservation_stepB; eauto.

  * (* Delay *) admit.
  * (* IfDelay *) admit.
Admitted.
*)

(*Proof.
  intros G D T1 C1 HWT.
  induction HWT.

  (* Case Nil *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.
    apply nilnostep in HStep.
    contradiction.

  (* Case EPR *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case EPRB *) 
    + assert (Actor.FSet.In A (Label.actors (Label.EPR A B))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      assert (Actor.FSet.In B (Label.actors (Label.EPR A B))) as HBinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      destruct (Hemptiness B HBinl) as [HBGempty HBDempty].
      
      destruct (epr_inversion A B T cfg1 q1 q2 T0 cfg2 H H13 Hscoped) as [HeprA HeprB].
      destruct HeprA as [idx1 [idx2]].
      destruct H2 as [HeprAA HeprAB].
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q1 idx1 (Var.Map.empty _))
                    q1 idx1 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q1 idx1)) as Hq1ty.
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q2 idx2 (Var.Map.empty _))
                    q2 idx2 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q2 idx2)) as Hq2ty.
      
      rewrite rem_empty2 in HWT; auto.
      rewrite rem_empty2 in HWT; auto.
      rewrite HeprB in HWT.
      
      pose proof (wt_subst_lin
                    C
                    (Var.Map.add q2 idx2 (Var.Map.empty nat))
                    (ChorEnv.find B T)
                    Expr.Typ.QUBIT
                    G
                    (ChorEnv.add A x Expr.Typ.QUBIT D)
                    (Actor.Map.add A (ChorEnv.find A T) T0)
                    B y
                    (Expr.QRef q2)
                    Hq2ty HWT) as HwtCAx.
      
      rewrite find_ab_neq1 in HwtCAx; auto.
      rewrite find_ab_neq2 in HwtCAx; auto.
      
      assert (~ Var.Map.In x (ChorEnv.find A G)) as HxninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      assert (~ Var.Map.In y (ChorEnv.find B G)) as HyninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find B G) HBGempty).
      Var.simplify.
      
      specialize (HwtCAx
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find B T0)
                       (ChorEnv.find B T)
                       (Var.Map.add q2 idx2 (Var.Map.empty nat))
                       HeprAB)
                    HyninG H1).
      
      pose proof (wt_subst_lin
                    (Choreography.subst B y (Expr.QRef q2) C)
                    (Var.Map.add q1 idx1 (Var.Map.empty nat))
                    (ChorEnv.find A T)
                    Expr.Typ.QUBIT
                    G
                    D
                    T0
                    A x
                    (Expr.QRef q1)
                    Hq1ty HwtCAx) as HwtCBy.
      
      rewrite H14.
      apply (HwtCBy
               (@Var.Map.Properties.Partition_sym _
                  (ChorEnv.find A T0)
                  (ChorEnv.find A T)
                  (Var.Map.add q1 idx1 (Var.Map.empty nat))
                  HeprAA)
               HxninG H0).
      
      rewrite find_ab_neq3; auto.

    (* Case EPRB' *) 
    + assert (Actor.FSet.In A (Label.actors (Label.EPR B A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      assert (Actor.FSet.In B (Label.actors (Label.EPR B A))) as HBinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      destruct (Hemptiness B HBinl) as [HBGempty HBDempty].

      assert (B <> A) as HBneA; auto.
      destruct (epr_inversion B A T cfg1 q2 q1 T0 cfg2 HBneA H13 Hscoped) as [HeprA HeprB].
      destruct HeprA as [idx1 [idx2]].
      destruct H2 as [HeprAA HeprAB].
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q1 idx2 (Var.Map.empty _))
                    q1 idx2 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q1 idx2)) as Hq1ty.
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q2 idx1 (Var.Map.empty _))
                    q2 idx1 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q2 idx1)) as Hq2ty.
      
      rewrite rem_empty2 in HWT; auto.
      rewrite rem_empty2 in HWT; auto.
      rewrite HeprB in HWT.
      rewrite addadd4 in HWT; auto.
      
      pose proof (wt_subst_lin
                    C
                    (Var.Map.add q2 idx1 (Var.Map.empty nat))
                    (ChorEnv.find B T)
                    Expr.Typ.QUBIT
                    G
                    (ChorEnv.add A x Expr.Typ.QUBIT D)
                    (Actor.Map.add A (ChorEnv.find A T) T0)
                    B y
                    (Expr.QRef q2)
                    Hq2ty HWT) as HwtCBy.
      
      rewrite find_ab_neq1 in HwtCBy; auto.
      rewrite find_ab_neq2 in HwtCBy; auto.
      
      assert (~ Var.Map.In x (ChorEnv.find A G)) as HxninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      assert (~ Var.Map.In y (ChorEnv.find B G)) as HyninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find B G) HBGempty).
      Var.simplify.
      
      specialize (HwtCBy
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find B T0)
                       (ChorEnv.find B T)
                       (Var.Map.add q2 idx1 (Var.Map.empty nat))
                       HeprAA)
                    HyninG H1).
      
      pose proof (wt_subst_lin
                    (Choreography.subst B y (Expr.QRef q2) C)
                    (Var.Map.add q1 idx2 (Var.Map.empty nat))
                    (ChorEnv.find A T)
                    Expr.Typ.QUBIT
                    G
                    D
                    T0
                    A x
                    (Expr.QRef q1)
                    Hq1ty HwtCBy) as HwtCAx.
      
      rewrite H14.
      apply (HwtCAx
               (@Var.Map.Properties.Partition_sym _
                  (ChorEnv.find A T0)
                  (ChorEnv.find A T)
                  (Var.Map.add q1 idx2 (Var.Map.empty nat))
                  HeprAB)
               HxninG H0).
      
      rewrite find_ab_neq3; auto.

    (* Case Delay/EPR *) 
    + assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (ChorEnv.find A0 (ChorEnv.remove B y (ChorEnv.remove A x G))) /\
                   Var.Map.Empty (ChorEnv.find A0
                                    (ChorEnv.add B y Expr.Typ.QUBIT (ChorEnv.add A x Expr.Qubit D)))) as Hih.
      {
        intros A0 HA0inl.
        
        assert (Actor.FSet.In A (Insn.actors (Insn.EPR A x B y))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        assert (Actor.FSet.In B (Insn.actors (Insn.EPR A x B y))) as HBinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.EPR A x B y))
                      H11 HA0inl HAinI).
        
        pose proof (members_dj A0 B
                      (Label.actors l)
                      (Insn.actors (Insn.EPR A x B y))
                      H11 HA0inl HBinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        {
          rewrite find_ab_neq3; auto.
          rewrite find_ab_neq3; auto.
        }
        {
          rewrite find_ab_neq1; auto.
          rewrite find_ab_neq1; auto.                    
        }
      }

      specialize (IHHWT cfg1 l C' T2 cfg2 H4 Hscoped Hih).

      apply EPR.
      { auto. }
      { auto. }
      { auto. }
      { auto. }

  (* Case Send *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.
   
    (* Case SendC *)
    + unfold  ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in H1.
      
      assert (Var.Map.Empty (Var.Map.M.empty Expr.Typ.t)) as Hee.
      Var.simplify.
      
      pose proof (empty_partition (Var.Map.M.empty Expr.Typ.t) DeltaA1 DeltaA2 Hee H1) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H0.
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H0.
      

      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H14
                    ThetaA1 ThetaA2 (Expr.Typ.BANG tau) Hscoped H0 H2) as Hsi.
      
      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].
      
      eapply Send.
      { auto. }
      { 
        eapply Expr.WellTyped_preservation.
        { rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty); eauto. }
        { rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty); Var.simplify. }
        { Var.simplify. }
        { apply (ChorEnv.ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H2). }
        { eauto. }
      }
      {
        rewrite H15.
        rewrite ChorEnv.addadd2.
        eauto.
      }
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty).
        rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H1.
        auto.
      }
      {
        rewrite H15.
        rewrite find_add; auto.
      }
   
    (* Case SendB *)
    + rewrite <- H15 in *.

      assert (Actor.FSet.In A (Label.actors (Label.Send A v B))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      assert (Actor.FSet.In B (Label.actors (Label.Send A v B))) as HBinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      destruct (Hemptiness B HBinl) as [HBGempty HBDempty].
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H0.
      destruct (bangty_inversion (Var.Map.empty Expr.Typ.t) DeltaA1 ThetaA1 v tau H0)
        as [HbangA [HbangB HbangC]].
      rewrite HbangB in *.
      rewrite HbangC in *.

      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in H1.
      pose proof (@Var.Map.Properties.Partition_sym _
                    (Var.Map.empty Expr.Typ.t) (Var.Map.empty Expr.Typ.t) DeltaA2 H1) as Hpart.
      pose proof (empty_partition
                    (Var.Map.empty Expr.Typ.t) DeltaA2 (Var.Map.empty Expr.Typ.t)
                    empty_map_empty Hpart) as Hep.
      eapply wt_subst_bang; eauto.
      
      rewrite <- (lopsided_partition (ChorEnv.find A T) ThetaA2 H2) in HWT.
      rewrite ChorEnv.find_add_env in HWT; auto.
      rewrite empty_to_empty in HWT; auto.
   
    (* Case Delay/Send *)
    + assert (Partition_except l T (Actor.Map.add A ThetaA2 T)) as Hpart.
      {
        unfold Partition_except.
        split.
        {
          intros.
          assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
          tauto.
          {
            rewrite <- HAeqA0 in *.
            exists ThetaA1.
            rewrite find_add.
            pose proof (@Var.Map.Properties.Partition_sym _
                          (ChorEnv.find A T) ThetaA1 ThetaA2 H2); auto.
          }
          {
            exists (Var.Map.empty _).
            rewrite find_ab_neq2; auto.
            apply Var.Map.Proofs.partition_empty_r.
          }
        }
        {
          intros.

          assert (Actor.FSet.In A (Insn.actors (Insn.Send A e B y))) as HAinI.
          unfold Insn.actors.
          Actor.simplify.
          
          pose proof (members_dj A0 A
                        (Label.actors l)
                        (Insn.actors (Insn.Send A e B y)) H12 H3 HAinI).
          
          rewrite find_ab_neq2; auto.
          Var.simplify.
        }
      }
      
      pose proof (delay_inversion
                    C T cfg1 l C' T2 cfg2 H5 Hscoped
                    (ChorEnv.add B y tau G)
                    (Actor.Map.add A DeltaA2 D)
                    (Actor.Map.add A ThetaA2 T)
                    Hpart HWT) as Hsi.
      
      destruct Hsi as [T2' [HsiA HsiB]].
      
      specialize (IHHWT cfg1 l C' T2' cfg2 HsiA).
      
      pose proof (ChorEnv.ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H2)) as Hwspe.
      
      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (elt:=Expr.Typ.t) (ChorEnv.find A0 (ChorEnv.add B y tau G)) /\
                   Var.Map.Empty (elt:=Expr.Typ.t) (ChorEnv.find A0 (Actor.Map.add A DeltaA2 D))) as Hih.
      {
        intros A0 HA0inl.

        assert (Actor.FSet.In A (Insn.actors (Insn.Send A e B y))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        assert (Actor.FSet.In B (Insn.actors (Insn.Send A e B y))) as HBinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.Send A e B y))
                      H12 HA0inl HAinI).
        
        pose proof (members_dj A0 B
                      (Label.actors l)
                      (Insn.actors (Insn.Send A e B y))
                      H12 HA0inl HBinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        { rewrite find_ab_neq1; auto. }
        { rewrite find_ab_neq2; auto. }
      }

      specialize (IHHWT Hwspe Hih).
      destruct (spps_on A ThetaA1 ThetaA2 T T2 T2' HsiB H2) as [HsppsonA HsppsonB].

      eapply Send.
      { auto. }
      { eauto. }
      {
        assert (WellTyped
                  (ChorEnv.add B y tau G)
                  (Actor.Map.add A DeltaA2 D)
                  (Actor.Map.add A (ChorEnv.find A T2') T2) C').
        {
          rewrite HsppsonA in IHHWT; auto.
        }
        eauto.
      }
      { auto. }
      { auto. }
      
  (* Case LetBang *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case LetBangC *)
    + unfold  ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
      
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in *.    
      
      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H12 
                    ThetaA1 ThetaA2 (Expr.Typ.BANG tau) Hscoped H H1) as Hsi.
      
      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].
      
      eapply LetBang; auto.
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
        eapply Expr.preservation.
        { eauto. }
        { apply (ChorEnv.ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1). }
        { eauto. }
      }
      {
        rewrite H13.
        rewrite ChorEnv.addadd2.
        eauto.
      }
      { auto. }
      { 
        rewrite H13.
        rewrite find_add; auto.
      }
      
    (* Case LetBangB *)
    + assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
      
      rewrite H13 in *.
      
      destruct (bangty_inversion (Var.Map.empty Expr.Typ.t) DeltaA1 ThetaA1 e0 tau H)
        as [HbangA [HbangB HbangC]].
      rewrite HbangB in *.
      rewrite HbangC in *.
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in H0.
      pose proof (@Var.Map.Properties.Partition_sym _
                    (Var.Map.empty Expr.Typ.t) (Var.Map.empty Expr.Typ.t) DeltaA2 H0) as Hpart.
      pose proof (empty_partition
                    (Var.Map.empty Expr.Typ.t) DeltaA2 (Var.Map.empty Expr.Typ.t)
                    empty_map_empty Hpart) as Hep.
      
      rewrite empty_to_empty in HWT; auto.
      rewrite <- (lopsided_partition (ChorEnv.find A T) ThetaA2 H1) in HWT.
      rewrite ChorEnv.find_add_env in HWT; auto.
      
      eapply wt_subst_bang; eauto.

    (* Case Delay/LetBang *)
    + assert (Partition_except l T (Actor.Map.add A ThetaA2 T)) as Hpart.
      {
        unfold Partition_except.
        split.
        {
          intros.
          assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
          tauto.
          {
            rewrite <- HAeqA0 in *.
            exists ThetaA1.
            rewrite find_add.
            pose proof (@Var.Map.Properties.Partition_sym _
                          (ChorEnv.find A T) ThetaA1 ThetaA2 H1); auto.
          }
          {
            exists (Var.Map.empty _).
            rewrite find_ab_neq2; auto.
            apply Var.Map.Proofs.partition_empty_r.
          }
        }
        {
          intros.

          assert (Actor.FSet.In A (Insn.actors (Insn.LetBang A x e))) as HAinI.
          unfold Insn.actors.
          Actor.simplify.
          
          pose proof (members_dj A0 A
                        (Label.actors l)
                        (Insn.actors (Insn.LetBang A x e)) H11 H2 HAinI).
          
          rewrite find_ab_neq2; auto.
          Var.simplify.
        }
      }
      
      pose proof (delay_inversion
                    C T cfg1 l C' T2 cfg2 H4 Hscoped
                    (ChorEnv.add A x tau G)
                    (Actor.Map.add A DeltaA2 D)
                    (Actor.Map.add A ThetaA2 T)
                    Hpart HWT) as Hsi.
      
      destruct Hsi as [T2' [HsiA HsiB]].
      
      specialize (IHHWT cfg1 l C' T2' cfg2 HsiA).
      
      pose proof (ChorEnv.ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H1)) as Hwspe.
      
      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (elt:=Expr.Typ.t) (ChorEnv.find A0 (ChorEnv.add A x tau G)) /\
                   Var.Map.Empty (elt:=Expr.Typ.t) (ChorEnv.find A0 (Actor.Map.add A DeltaA2 D))) as Hih.
      {
        intros A0 HA0inl.

        assert (Actor.FSet.In A (Insn.actors (Insn.LetBang A x e))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.LetBang A x e))
                      H11 HA0inl HAinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        { rewrite find_ab_neq1; auto. }
        { rewrite find_ab_neq2; auto. }
      }

      specialize (IHHWT Hwspe Hih).
      destruct (spps_on A ThetaA1 ThetaA2 T T2 T2' HsiB H1) as [HsppsonA HsppsonB].

      eapply LetBang.
      { eauto. }
      {
        assert (WellTyped
                  (ChorEnv.add A x tau G)
                  (Actor.Map.add A DeltaA2 D)
                  (Actor.Map.add A (ChorEnv.find A T2') T2) C').
        {
          rewrite HsppsonA in IHHWT; auto.
        }
        eauto.
      }
      { auto. }
      { auto. }
      
  (* Case LetIn *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case LetC *)
    + unfold  ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).

      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].

      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
    
      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H13 
                    ThetaA1 ThetaA2 tau Hscoped H H1) as Hsi.

      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].

      eapply LetIn; eauto.
      { 
        eapply Expr.WellTyped_preservation.
        {
          rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp).
          rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
          eauto.
        }
        { auto. }
        { auto. }
        { apply (ChorEnv.ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1). }
        { eauto. }
      }
      {
        instantiate (1 := ThetaA2).
        rewrite H14.
        rewrite ChorEnv.addadd2.
        auto.
      }
      {
        rewrite H14.
        rewrite find_add; auto.
      }

    (* Case LetC *) 
    + assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      
      eapply wt_subst_lin with (ThetaA2 := ThetaA2).
      {
        rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H.
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
        eauto.
      }
      {
        rewrite <- H15.
        rewrite rem_empty2 in HWT; auto.
        unfold ChorEnv.add.
        Var.simplify.
      }
      {
        rewrite <- H15; auto.
      }
      { 
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
        Var.simplify.
      }
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty).
        Var.simplify.
      }

    (* Case Delay/Let *)
    + assert (Partition_except l T (Actor.Map.add A ThetaA2 T)) as Hpart.
      {
        unfold Partition_except.
        split.
        {
          intros.
          assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
          tauto.
          {
            rewrite <- HAeqA0 in *.
            exists ThetaA1.
            rewrite find_add.
            pose proof (@Var.Map.Properties.Partition_sym _
                          (ChorEnv.find A T) ThetaA1 ThetaA2 H1); auto.
          }
          {
            exists (Var.Map.empty _).
            rewrite find_ab_neq2; auto.
            apply Var.Map.Proofs.partition_empty_r.
          }
        }
        {
          intros.

          assert (Actor.FSet.In A (Insn.actors (Insn.Let A x e))) as HAinI.
          unfold Insn.actors.
          Actor.simplify.
          
          pose proof (members_dj A0 A
                        (Label.actors l)
                        (Insn.actors (Insn.LetBang A x e)) H12 H3 HAinI).
          
          rewrite find_ab_neq2; auto.
          Var.simplify.
        }
      }
      
      pose proof (delay_inversion
                    C T cfg1 l C' T2 cfg2 H5 Hscoped
                    (ChorEnv.remove A x G)
                    (Actor.Map.add A (Var.Map.add x tau DeltaA2) D)
                    (Actor.Map.add A ThetaA2 T)
                    Hpart HWT) as Hsi.
      
      destruct Hsi as [T2' [HsiA HsiB]].
      
      specialize (IHHWT cfg1 l C' T2' cfg2 HsiA).
      
      pose proof (ChorEnv.ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H1)) as Hwspe.
      
      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (ChorEnv.find A0 (ChorEnv.remove A x G)) /\
                   Var.Map.Empty (ChorEnv.find A0
                                    (Actor.Map.add A (Var.Map.add x tau DeltaA2) D))) as Hih.
      {
        intros A0 HA0inl.
        assert (Actor.FSet.In A (Insn.actors (Insn.Let A x e))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.Let A x e))
                      H12 HA0inl HAinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        { rewrite find_ab_neq3; auto. }
        { rewrite find_ab_neq2; auto. }
      }
      
      specialize (IHHWT Hwspe Hih).
      destruct (spps_on A ThetaA1 ThetaA2 T T2 T2' HsiB H1) as [HsppsonA HsppsonB].

      eapply LetIn.
      { eauto. }
      {
        assert (WellTyped
                  (ChorEnv.remove A x G)
                  (Actor.Map.add A (Var.Map.add x tau DeltaA2) D)
                  (Actor.Map.add A (ChorEnv.find A T2') T2) C').
        {
          rewrite HsppsonA in IHHWT; auto.
        }
        eauto.
      }
      { auto. }
      { auto. }
      { auto. }
      
  (* Case LetPair *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case LetPairC *)
    + unfold  ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
      
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in *.    
      
      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H16 
                    ThetaA1 ThetaA2 (Expr.Typ.Tensor tau1 tau2) Hscoped H H1) as Hsi.
      
      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].
      
      eapply LetPair; auto.
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty); auto.
        eapply Expr.preservation.
        { eauto. }
        { apply (ChorEnv.ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1). }
        { eauto. }
      }
      {
        rewrite H17.
        rewrite ChorEnv.addadd2.
        eauto.
      }
      { auto. }
      { 
        rewrite H17.
        rewrite find_add; auto.
      }
      { auto. }
      { auto. }

    (* Case LetPairB *)
    + assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      rewrite H19 in *.
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp1.
      pose proof (empty_partition (ChorEnv.find A D) DeltaA2 DeltaA1 HADempty
                    (@Var.Map.Properties.Partition_sym _  (ChorEnv.find A D) DeltaA1 DeltaA2 H0)) as Hdp2.
      
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA2 Hdp2) in H0.  
       
      inversion H; subst.
      pose proof (empty_partition DeltaA1 Delta1 Delta2 Hdp1 H14) as Hdpd1.
      pose proof (empty_partition DeltaA1 Delta2 Delta1 Hdp1
                    (@Var.Map.Properties.Partition_sym _ DeltaA1 Delta1 Delta2 H14)) as Hdpd2.
      
      rewrite (Var.Map.Proofs.empty_map_equal Delta1 Hdpd1) in H12.    
      rewrite (Var.Map.Proofs.empty_map_equal Delta2 Hdpd2) in H13.
      
      rewrite rem_empty2 in HWT; auto.
      rewrite rem_empty2 in HWT; auto.
      rewrite addadd8 in HWT.
      rewrite addadd8 in HWT.
      rewrite empty_to_empty in HWT.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H12.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H13.
      
      pose proof wt_subst_lin as Hwtslinx2.
      
      specialize (Hwtslinx2 C Theta2 ThetaA2 tau2
                    G
                    (ChorEnv.add A x1 tau1 D)
                    (Actor.Map.add A (Var.Map.concat ThetaA2 Theta2) T)
                    A x2 v2 H13).
      
      rewrite ChorEnv.addadd2 in Hwtslinx2; auto.
      rewrite find_add in Hwtslinx2; auto.
      
      destruct (partitioning
                  (ChorEnv.find A T) Theta1 ThetaA2 ThetaA1 Theta2
                  (@Var.Map.Properties.Partition_sym _ (ChorEnv.find A T)
                     ThetaA1 ThetaA2 H1) H15)
        as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
      
      assert (~ Var.Map.In x1 (ChorEnv.find A G)) as Hx1ninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      assert (~ Var.Map.In x2 (ChorEnv.find A G)) as Hx2ninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      
      rewrite addadd9 in HWT; auto.
      
      specialize (Hwtslinx2 HWT
                    (@Var.Map.Properties.Partition_sym _ (Var.Map.concat ThetaA2 Theta2)
                       ThetaA2 Theta2 HPartitionB)
                    Hx2ninG).
      
      rewrite find_add_map in Hwtslinx2; auto.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in Hwtslinx2; auto.
      
      assert (x2 <> x1) as Hx2nex1; auto.
      assert (~ Var.Map.In x1 (Var.Map.empty Expr.Typ.t)) as Hx1niemp.
      Var.simplify.
      assert (~ Var.Map.In x2 (Var.Map.empty Expr.Typ.t)) as Hx2niemp.
      Var.simplify.
      
      pose proof (nin_mapl (Var.Map.empty _) x2 x1 tau1 Hx2nex1 Hx2niemp).
      specialize (Hwtslinx2 (nin_mapl (Var.Map.empty _) x2 x1 tau1 Hx2nex1 Hx2niemp)).
      
      pose proof wt_subst_lin as Hwtslinx1.
      
      specialize (Hwtslinx1
                    (Choreography.subst A x2 v2 C)
                    Theta1
                    (Var.Map.concat ThetaA2 Theta2)
                    tau1
                    G
                    D
                    T
                    A x1 v1 H12 Hwtslinx2
                    HPartitionD Hx1ninG).
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in Hwtslinx1; auto.
      { Var.simplify. }
      { auto. }
      { rewrite rem_empty2; auto. }        
   
    (* Case Delay/Let *)
    + assert (Partition_except l T (Actor.Map.add A ThetaA2 T)) as Hpart.
      {
        unfold Partition_except.
        split.
        {
          intros.
          assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
          tauto.
          {
            rewrite <- HAeqA0 in *.
            exists ThetaA1.
            rewrite find_add.
            pose proof (@Var.Map.Properties.Partition_sym _
                          (ChorEnv.find A T) ThetaA1 ThetaA2 H1); auto.
          }
          {
            exists (Var.Map.empty _).
            rewrite find_ab_neq2; auto.
            apply Var.Map.Proofs.partition_empty_r.
          }
        }
        {
          intros.

          assert (Actor.FSet.In A (Insn.actors (Insn.LetPair A x1 x2 e))) as HAinI.
          unfold Insn.actors.
          Actor.simplify.
          
          pose proof (members_dj A0 A
                        (Label.actors l)
                        (Insn.actors (Insn.LetPair A x1 x2 e)) H14 H5 HAinI).
          
          rewrite find_ab_neq2; auto.
          Var.simplify.
        }
      }
      
      pose proof (delay_inversion
                    C T cfg1 l C' T2 cfg2 H7 Hscoped
                    (ChorEnv.remove A x1 (ChorEnv.remove A x2 G))
                    (Actor.Map.add A (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D)
                    (Actor.Map.add A ThetaA2 T)
                    Hpart HWT) as Hsi.
      
      destruct Hsi as [T2' [HsiA HsiB]].
      
      specialize (IHHWT cfg1 l C' T2' cfg2 HsiA).
      
      pose proof (ChorEnv.ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H1)) as Hwspe.
      
      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (ChorEnv.find A0
                                  (ChorEnv.remove A x1 (ChorEnv.remove A x2 G))) /\
                   Var.Map.Empty (ChorEnv.find A0
                                    (Actor.Map.add A
                                       (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D))) as Hih.
      {
        intros A0 HA0inl.
        assert (Actor.FSet.In A (Insn.actors (Insn.LetPair A x1 x2 e ))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.LetPair A x1 x2 e))
                      H14 HA0inl HAinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        {
          rewrite find_ab_neq3; auto.
          rewrite find_ab_neq3; auto.
        }
        { rewrite find_ab_neq2; auto. }
      }

      specialize (IHHWT Hwspe Hih).
      destruct (spps_on A ThetaA1 ThetaA2 T T2 T2' HsiB H1) as [HsppsonA HsppsonB].

      eapply LetPair.
      { eauto. }
      {
        assert (WellTyped
                  (ChorEnv.remove A x1 (ChorEnv.remove A x2 G))
                  (Actor.Map.add A (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D)
                  (Actor.Map.add A (ChorEnv.find A T2') T2) C').
        {
          rewrite HsppsonA in IHHWT; auto.
        }
        eauto.
      }
      { auto. }
      { auto. }
      { auto. }
      { auto. }
      { auto. }
    Qed.*)
     (* Proof sketch: Induct on the typing derivation, then invert the step. Use
       preservation helpers for stepC and stepB. Handle IfC directly. Lift Delay
       and IfDelay with delay_inversion and the induction hypotheses. Leave
       substitution, partition, and branch-composition details for later. *)
  Admitted.

Lemma preservation : forall G D T1 C1,
    WellTyped G D T1 C1 ->
    forall cfg1 l C2 T2 cfg2, 
      step C1 T1 cfg1 l C2 T2 cfg2 ->
      ChorEnv.WellScoped T1 cfg1 ->
        (forall A, Actor.FSet.In A (Label.actors l) ->
                   Var.Map.Empty (ChorEnv.find A G) /\  Var.Map.Empty (ChorEnv.find A D)) ->   
        WellTyped G D T2 C2 /\ ChorEnv.WellScoped T2 cfg2.
Proof.
  intros.
  split.
  * eapply WellTyped_preservation; eauto.
  * eapply WellScoped_preservation; eauto.
    eapply WellTyped_WellFormed; eauto.
Qed. 
