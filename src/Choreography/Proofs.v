Theorem safety : forall C Theta ρ C' Theta' ρ',
  multi_step C Theta ρ C' Theta' ρ' ->
  WellTyped (Actor.Map.empty _) (Actor.Map.empty _) Theta C ->
  ChorEnv.WellScoped Theta ρ ->

  C' = [] \/ exists l C'' Theta'' ρ'', Choreography.step C' Theta' ρ' l C'' Theta'' ρ''.
Proof.
  intros C ? ? C' ? ? Hstep.
  induction Hstep; intros HWT HWS; auto.
  * eapply progress in HWT; eauto; Actor.simplify.
  * eapply IHHstep.
    + eapply WellTyped_preservation; eauto.
      intros. split; ChorEnv.simplify.
    + eapply WellScoped_preservation; eauto.
      eapply WellTyped_WellFormed; eauto.
Qed. 
