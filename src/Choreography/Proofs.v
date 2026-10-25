From Qoreo.Base Require Import Var.
From Qoreo.Expr Require Expr BaseProofs.
From Qoreo.Choreography Require Import Choreography BaseProofs Progress Preservation.

Theorem safety : forall C Theta ρ C' Theta' ρ' tau,
  Choreography.multi_step C Theta ρ C' Theta' ρ' ->
  WellTyped (Actor.Map.empty _) (Actor.Map.empty _) Theta C tau ->
  ChorEnv.WellScoped Theta ρ ->

  Choreography.Val C'
  \/
  exists l C'' Theta'' ρ'',
    Choreography.step C' Theta' ρ' l C'' Theta'' ρ''.
Proof.
  intros C ? ? C' ? ? ? Hstep.
  induction Hstep; intros HWT HWS; auto.
  * eapply progress in HWT; eauto; Actor.simplify.
    { intros B. ChorEnv.simplify. }
    { intros B. ChorEnv.simplify. }

  * eapply IHHstep.
    + eapply WellTyped_preservation; eauto.
      intros. split; ChorEnv.simplify.
    + eapply WellScoped_preservation; eauto.
Qed. 
