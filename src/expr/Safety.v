From Qoreo.Expr Require Import BaseProofs.
From Qoreo.Expr Require Preservation Progress.

Theorem safety : forall e Θ cfg e' Θ' cfg',
  multi_step e Θ cfg e' Θ' cfg' ->
  forall τ,
  WellTyped (Var.Map.empty _) (Var.Map.empty _) Θ e τ ->
  Config.WellScoped Θ cfg ->
  Val e' \/ can_step e' Θ' cfg'.
Proof.
  intros ? ? ? ? ? ? Hstep.
  induction Hstep; intros τ HWT HWS.
  * unfold can_step. eapply Progress.progress; eauto; Var.simplify.
  * eapply Preservation.preservation in H; eauto.
    destruct H as [HWT' HWS'].
    eapply IHHstep; eauto.
Qed.