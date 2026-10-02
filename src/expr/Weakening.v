(**
    Weakening.v 

    weakening1 - weakening of a single non-linear variable

    weakening_gen - weakening of possibly multiple non-linear variables

    weakening - weakening of all non-linear variables

*)

From Qoreo.Expr Require Import BaseProofs.


(** Weakening of a single non-linear varialbe *)
Lemma weakening1 : forall e Γ Δ Θ τ,
  WellTyped Γ Δ Θ e τ ->
  forall z τ0,
  ~ Var.Map.In z Γ ->
  ~ Var.Map.In z Δ ->
  WellTyped (Var.Map.add z τ0 Γ) Δ Θ e τ.
Proof.
  intros ? ? ? ? ? HWT;
    induction HWT;
    intros z α HΓ HΔ;
    try (econstructor;
          eauto; fail).
      (*reflect_partition;
      Var.simplify.*)
  * constructor; Var.simplify.
  * apply WTCVar; Var.simplify.
    compare x z; auto.
    {
      exfalso.
       Var.solve.
    }
   * (* LetIn *)
    econstructor; eauto.
    + reflect_partition. Var.simplify.
    + reflect_partition. Var.simplify.
      eapply IHHWT2; auto; Var.simplify.

  * (* LetBang *)
    econstructor; eauto.
    + reflect_partition. Var.simplify.
    + reflect_partition. Var.simplify.
      compare x z.
      { Var.simplify. }
      {
        rewrite Var.Map.Proofs.add_neq_sym; auto.
        eapply IHHWT2; auto.
        Var.simplify.
      }

  * (* If *)
    econstructor; eauto;
      reflect_partition; Var.simplify.
  * (* Pair *)
    econstructor; eauto;
      reflect_partition; Var.simplify.
  * (* LetPair *)
    econstructor; eauto;
      reflect_partition; Var.simplify.
    eapply IHHWT2; auto;
      Var.simplify.
    
  * (* Lambda *)
    econstructor; auto.
    Var.simplify.
    apply IHHWT; auto;
      Var.simplify.

  * (* Fix *)
    econstructor; auto.
    Var.simplify.
    compare f z.
    {
      rewrite (Var.Map.Proofs.add_neq_sym _ f x); auto.
      Var.simplify.
      rewrite (Var.Map.Proofs.add_neq_sym _ x f); auto.
    }
    compare x z.
    { Var.simplify. }
    rewrite (Var.Map.Proofs.add_neq_sym _ x z); auto.
    rewrite (Var.Map.Proofs.add_neq_sym _ f z); auto.
    eapply IHHWT;
      Var.simplify.

  * (* Apply *) 
    econstructor; eauto;
      reflect_partition; Var.simplify.
Qed.


(** Weakening of possibly multiple non-linear variables *)
Lemma weakening_gen : forall Γ0,
  forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->
  forall Γ',
  Var.Map.Partition Γ' Γ Γ0 ->
  Var.Map.Properties.Disjoint Γ0 Δ ->
  WellTyped Γ' Δ Θ e τ.
Proof.
  intros Γ0.
  induction Γ0 using Var.Map.Properties.map_induction;
  intros ? ? ? ? ? HWT Γ' Hsub Hdisj.
  
  * Var.simplify. 

  * reflect_partition. Var.simplify.
    setoid_replace (Var.Map.concat Γ (Var.Map.add x e Γ0_1))
      with (Var.Map.add x e (Var.Map.concat Γ Γ0_1)).
    2:{ Var.solve. }
    
    apply weakening1; auto.
    2:{ Var.simplify. }
    eapply IHΓ0_1; eauto.
    { Var.simplify. }
Qed.

Lemma weakening : forall Γ Δ Θ e τ,
  WellTyped (Var.Map.empty _) Δ Θ e τ ->
  Var.Map.Properties.Disjoint Γ Δ ->
  WellTyped Γ Δ Θ e τ.
Proof.
  intros Γ Δ Θ e τ HWT.
  eapply weakening_gen; eauto with var_db.
Qed.
#[global] Hint Resolve weakening : var_db.