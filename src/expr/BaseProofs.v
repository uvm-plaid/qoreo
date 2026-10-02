(**
  In this module:

    Rewriting is valid (proper) under the step relation and typing judgment

    `step_dim_monotic` - taking a step  never decreases the size of the underlying quantum state. This is implementation-dependent, but is useful for showing that concurrency in the choreographies can never lead to conflicts.

    wt_disjoint - the variables occuring in a well-typed expression typing judgment are disjoint

  *)


From Stdlib Require Export FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Export Matrix Pad Quantum.
From Qoreo Require Export Base Expr.Expr.
Export Var.Map.Tactics.


Open Scope qoreo.

(******************************)
(** * Step Relation is Proper *)
(******************************)


Lemma step_proper : forall e refs cfg e' refs' cfg',
  step e refs cfg e' refs' cfg' ->
  forall refs0 refs0',
    Var.Map.Equal refs refs0 ->
    Var.Map.Equal refs' refs0' ->
    step e refs0 cfg e' refs0' cfg'.
Proof.
  intros ? ? ? ? ? ? Hstep.
  induction Hstep; intros refs_ refs_' Hrefs Hrefs';
  try (econstructor; eauto; Var.simplify; fail).
  * (* NewB *)
    inversion H; subst; clear H.
    econstructor.
    { reflexivity. }
    Var.simplify.

  * (* MeasB *)
    match goal with
    | [ H : _ = Config.measure _ _ _ _ |- _ ] =>
      inversion H; subst; clear H
    end.
    econstructor.
    2:{
     unfold Config.measure.
     replace (Config.find x refs_) with (Config.find x refs); auto.
     { rewrite Hrefs; auto. }
    }
    all:Var.simplify.
Qed.

Global Instance stepProper : Proper (eq ==> Var.Map.Equal ==> eq ==> eq ==> Var.Map.Equal ==> eq ==> iff) step.
Proof.
  intros e1 e2 He refs1 refs2 Hrefs cfg1 cfg2 Hcfg
         e1' e2' He' refs1' refs2' Hrefs' cfg1' cfg2' Hcfg';
    subst; split; intros;
    eapply step_proper; eauto;
    symmetry; auto.
Qed.



(********************************)
(** * Typing Relation is Proper *)
(********************************)



(* The stronger statement would be 
to define alpha equivalence for Expr.tessions
and then to prove this with respect to
    Var.Map.Equiv alpha_equiv
*)

Lemma WellTyped_context_equal :
  forall Γ Δ Θ e τ,
    WellTyped Γ Δ Θ e τ ->
  forall Γ' Δ' Θ',
    Var.Map.Equal Γ Γ' ->
    Var.Map.Equal Δ Δ' ->
    Var.Map.Equal Θ Θ' ->
    WellTyped Γ' Δ' Θ' e τ.
Proof.
  intros Γ Δ Θ e τ He.
  induction He; intros Γ0 Δ0 Θ0 HΓ HΔ HΘ;
    try (
      econstructor;
      try apply IHHe;
      try apply IHHe1;
      try apply IHHe2;
      try apply IHHe3;
      try rewrite <- HΔ;
      try rewrite <- HΓ;
      try rewrite <- HΘ;
      try reflexivity;
      eauto;
      fail).
Qed.


Global Instance WellTypedProper : Proper (Var.Map.Equal ==> Var.Map.Equal ==> Var.Map.Equal ==> eq ==> eq ==> iff) WellTyped.
Proof.
  intros Γ1 Γ2 HΓ
    Δ1 Δ2 HΔ
    Θ1 Θ2 HΘ
    e1 e2 He
    τ1 τ2 Hτ; subst.
  split; intros; eapply WellTyped_context_equal; eauto;
    try (symmetry; auto).
Qed.

(*********************************)
(** * Step relation is monotonic *)
(*********************************)

Close Scope R_scope.
(* This is implementation dependent *)
Lemma step_dim_monotonic : forall e Θ ρ e' Θ' ρ',
  step e Θ ρ e' Θ' ρ' ->
  Config.dim ρ <= Config.dim ρ'.
Proof.
  intros.
  induction H; auto.
  * inversion H; subst; simpl; auto.
  * inversion H0; subst; simpl; auto.
  * subst; simpl; auto.
  * subst; simpl; auto.
Qed.

(************************************************)
(* Well-typed judgments have disjoint variables *)
(************************************************)

Lemma wt_disjoint' : forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->
  forall z, Var.Map.In z Γ -> Var.Map.In z Δ -> False.
Proof.
  intros ? ? ? ? ? HWT.
  induction HWT;
    intros z HΓ HΔ;
    reflect_partition;
    Var.simplify.
  * compare x z; tauto.
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    compare x z.
    apply (IHHWT2 z); autorewrite with var_db;
      tauto.
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    compare x z.
    apply (IHHWT2 z); autorewrite with var_db;
      intuition.
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    { apply (IHHWT2 z); auto. }
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    { apply (IHHWT2 z); auto. }
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    compare x1 z.
    compare x2 z.
    apply (IHHWT2 z); autorewrite with var_db;
      tauto.
  * apply (IHHWT z); auto.
  * apply (IHHWT z); auto.
  * apply (IHHWT z); auto.
  * compare x z.
    apply (IHHWT z); autorewrite with var_db; tauto.
  * destruct HΔ as [HΔ1 | HΔ2].
    { apply (IHHWT1 z); auto. }
    { apply (IHHWT2 z); auto. }
Qed.


Lemma wt_disjoint : forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->
  Var.Map.Properties.Disjoint Γ Δ.
Proof.
  intros ? ? ? ? ? HWT z [HΓ HΔ].
  eapply wt_disjoint'; eauto.
Qed.
