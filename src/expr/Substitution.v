(** Substitution

    subst_not_in - substituting a value for a variable
    not in e has no effect.

    wt_subst_bang - substituting a non-linear variable is well-typed

    wt_subst - substituting a linear variable is well-typed

    wt_subst2 - substituting two linear variables is well-typed

*)

From Qoreo.Expr Require Import BaseProofs Weakening.

(** ** Substitution lemma *)

(* Substitution for x is the identity if x does not occur free in e *)
Lemma subst_not_in : forall e x v Γ Δ Θ τ,
  WellTyped Γ Δ Θ e τ ->
  ~ Var.Map.In x Γ ->
  ~ Var.Map.In x Δ ->
  subst x v e = e.
Proof.
  intros e; induction e; intros y v ? ? ? ? Hwt HΓ HΔ;
    simpl; try rename t0 into x;
    inversion Hwt; subst; clear Hwt;
    auto;
    try (
      try (erewrite IHe; eauto);
      try (erewrite IHe1; eauto);
      try (erewrite IHe2; eauto);
      try (erewrite IHe3; eauto);
      fail).
  * Var.simplify.
  * Var.simplify. Var.solve.
  * (*LetIn*)
    reflect_partition.
    erewrite IHe1; eauto; Var.simplify.
    erewrite IHe2; eauto; Var.simplify.
  * reflect_partition.
    erewrite IHe1; eauto; Var.simplify.
    erewrite IHe2; eauto; Var.simplify.
  * reflect_partition. 
    erewrite IHe1; eauto; Var.simplify.
    erewrite IHe2; eauto; Var.simplify.
    erewrite IHe3; eauto; Var.simplify.

  * reflect_partition. 
    erewrite IHe1; eauto; Var.simplify.
    erewrite IHe2; eauto; Var.simplify.
  * (* LetPair *)
    rename t into z.
    reflect_partition.
    erewrite IHe1; eauto; Var.simplify.
    erewrite IHe2; eauto. Var.simplify.
    Var.solve.
  * Var.simplify.
    erewrite IHe; eauto; Var.simplify.
  * rename x into f, t into x.
    Var.simplify.
    erewrite IHe; eauto; [Var.solve | Var.simplify].
  * (* App *)
    reflect_partition. 
    erewrite IHe1; eauto; Var.simplify.
    erewrite IHe2; eauto; Var.simplify.
Qed.

(** Substitution for non-linear variables *)
Lemma wt_subst_bang : forall e τ Γ Δ Θ x v τ',
  WellTyped (Var.Map.empty _) (Var.Map.empty _) (Var.Map.empty _) v τ ->
  WellTyped (Var.Map.add x τ Γ) Δ Θ e τ' ->
  WellTyped Γ Δ Θ (subst x v e) τ'.
Proof.
  intros ? ? ? ? ? ? ? ? Hv He.
  assert (Hdisj : Var.Map.Properties.Disjoint (Var.Map.add x τ Γ) Δ).
  { eapply wt_disjoint; eauto. }
  Var.simplify.
  dependent induction e;
    simpl;
    try rename t into y;
    inversion He; subst; clear He.

  *  (* linear variable *)
    Var.simplify.
    apply WTQVar; auto;
      Var.simplify.
  * (* non-linear variable *)
      compare x y.
      { (* x=y *)
        Var.simplify.
        replace τ' with τ in * by intuition.
        apply weakening; auto.
      }
      { (* x <> y *)
        apply WTCVar; auto with var_db.
        Var.simplify.
      }

  * (* LetIn *)
    compare x y; Var.simplify.
    + (* x = y *)
      eapply (WTLetIn Δ1 Δ2 Θ1 Θ2); eauto.
      reflect_partition. Var.simplify.
      eapply IHe1; eauto.
    + (* x <> y *)
      eapply (WTLetIn Δ1 Δ2 Θ1 Θ2); eauto;
        reflect_partition; Var.simplify.
      { eapply IHe1; eauto. }
      eapply IHe2; eauto.
      2:{ Var.simplify. }
      Var.reflect_find. intuition.
      Var.reflect_find.
      intros [[? ?] ?]. apply (H0 z); split; auto.

  * (* Bang *)
    econstructor; auto with var_db.
    eapply IHe; eauto with var_db.

  * (* LetBang *)
    compare x y; Var.simplify.
    + (* x = y *)
      econstructor; eauto.
      reflect_partition. Var.simplify.
      eapply IHe1; eauto; Var.simplify.
    + (* x <> y *)
      econstructor; eauto; reflect_partition; Var.simplify; eauto.
      eapply IHe2; eauto.
      2:{ Var.solve. }
      rewrite Var.Map.MProofs.Proofs.add_neq_sym; auto.

  * econstructor; eauto.
  * econstructor; eauto;
    reflect_partition; Var.simplify; eauto.
  * econstructor; eauto;
    reflect_partition; Var.simplify; eauto.

  * (* LetPair *) rename y into y1, t0 into y2.
    eapply (WTLetPair Δ1 Δ2 Θ1 Θ2); eauto.
    {
      reflect_partition.
      eapply IHe1; eauto; Var.simplify.
    }

    reflect_partition. Var.simplify.
    eapply IHe2; eauto.
    2:{ Var.simplify. }
    Var.reflect_find. intuition.
    Var.reflect_find. intuition.
    match goal with
    | [ H : Var.Map.Properties.Disjoint Γ Δ2 |- _ ] =>
      apply (H z); auto
    end.
  * (* Meas *)
    econstructor; eauto.
  * (* QRef *) 
    econstructor; eauto.
  * (* New *) econstructor; eauto.
  * (* Unitary *) econstructor; eauto.

  * (* Lambda *)
    econstructor; eauto.
    Var.simplify.
    eapply IHe; eauto.
    2:{ Var.simplify. }
    {
      Var.reflect_find. intuition.
      Var.reflect_find.
      intuition.
      match goal with
      | [ H : Var.Map.Properties.Disjoint Γ Δ |- _ ] =>
        apply (H z); auto
      end.
    }

  * (* Fix *)
    rename y into f, t0 into y.
    econstructor; eauto with var_db.
    compare f x; Var.simplify.
    {
      rewrite (Var.Map.MProofs.Proofs.add_neq_sym _ f y) in *;
        auto.
      Var.simplify.
    }
    compare y x; Var.simplify.
    eapply IHe; eauto; Var.simplify.
    rewrite (Var.Map.MProofs.Proofs.add_neq_sym _ x f); auto.
    rewrite (Var.Map.MProofs.Proofs.add_neq_sym _ x y); auto.

  * (* App *) 
    econstructor; eauto;
    reflect_partition; Var.simplify; eauto.
Qed.

Ltac partition_add_inversion :=
    match goal with
      | [ H : Var.Map.Partition (Var.Map.add _ _ _) _ _ |- _ ] =>
        apply Var.Map.Proofs.partition_add_inversion in H; auto;
        try destruct H as [[? [? ?]] | [? [? ?]]]
    end.

(* Substitution for linear variables *)
Lemma wt_subst : forall e Θ1 Θ2 τ Γ Δ Θ x v τ',
  WellTyped (Var.Map.empty _) (Var.Map.empty _) Θ1 v τ ->
  WellTyped Γ (Var.Map.add x τ Δ) Θ2 e τ' ->
  Var.Map.Partition Θ Θ1 Θ2 ->
  ~ Var.Map.In x Γ ->
  ~ Var.Map.In x Δ ->

  WellTyped Γ Δ Θ (subst x v e) τ'.
Proof.
  intros e; induction e;
    intros ? ? ? ? ? ? ? ? ? Hv He Hpart HΓ Hin;
    simpl.
  * (* Var *)
    inversion He; subst; clear He;
      Var.simplify.
    assert (Var.Map.Empty Δ).
    {
      Var.reflect_find.
      specialize (H2 z).
      Var.simplify.
    }
    Var.simplify.
    apply weakening; auto.
    Var.simplify.

  * (* LetIn *) rename t into y.
    inversion He; subst; clear He.
    partition_add_inversion.
    + (* x occcurs in Δ1 *)

      setoid_replace (if Var.FSet.MF.eq_dec x y then e2 else subst x v e2)
        with e2.
      2:{
        compare x y; auto.
        reflect_partition. Var.simplify.
        eapply (subst_not_in e2 x v);
          eauto;
          Var.solve.
      }

      (* Γ; Δ1-{x}; Θ1+Θ0 |- subst x v e1 : τ *)
      eapply (WTLetIn
                (Var.Map.remove x Δ1) Δ2
                (Var.Map.concat Θ1 Θ0) Θ3);
        eauto; Var.simplify.
  
      eapply IHe1; eauto; Var.simplify.
      setoid_replace (Var.Map.add x τ Δ1) with Δ1;
        auto with extra_var_db.
      
    + (* x occurs in Δ2 *)
      erewrite (subst_not_in e1 x v); eauto.
      assert (x <> y).
      { inversion 1; subst.
        Var.solve.
      }
      Var.simplify.

      eapply (WTLetIn 
                Δ1 (Var.Map.remove x Δ2)
                Θ0 (Var.Map.concat Θ1 Θ3));
        eauto; Var.simplify. (* if you use eauto with var_db here, it will hang *)
      
      eapply IHe2; 
        [ eauto | | Var.simplify
        | Var.simplify | Var.solve ].
      setoid_replace
        (Var.Map.add x τ (Var.Map.add y τ0 (Var.Map.remove x Δ2)))
        with (Var.Map.add y τ0 Δ2)
        by Var.solve;
      auto.

  * (* Bang e *) 
    inversion He; subst; clear He.
    Var.simplify.
      
  * (* LetBang *) rename t into y.
    inversion He; subst; clear He.
    partition_add_inversion.

    + (* x occcurs in Δ1 *)

      setoid_replace (if Var.FSet.MF.eq_dec x y then e2 else subst x v e2)
        with e2.
      2:{
        compare x y; auto.
        eapply (subst_not_in e2 x v); eauto.
        Var.simplify.
      }

      (* Γ; Δ1-{x}; Θ1+Θ0 |- subst x v e1 : τ *)
      eapply (WTLetBang _
                (Var.Map.remove x Δ1) Δ2
                (Var.Map.concat Θ1 Θ0) Θ3); eauto;
        Var.simplify.
      eapply IHe1; eauto; Var.simplify.
      setoid_replace (Var.Map.add x τ Δ1) with Δ1;
        auto with extra_var_db.

    + (* x occurs in Δ2 *)
      erewrite (subst_not_in e1 x v); eauto.

      assert (x <> y).
      { (* Lemma: since  Γ,y:τ0; Δ2; Θ3 |- e2 : τ' 
                  it must be the case that Disjoint(\Gamma,y:τ0, Δ2)
                  and thus y ∉ Δ2.
                  But y ∈ Δ2.
        *)
        inversion 1; subst.
        absurd (Var.Map.In y Δ2).
        2:{ exists τ; auto. }
        assert (Hdisj : Var.Map.Properties.Disjoint (Var.Map.add y τ0 Γ) Δ2).
        { eapply wt_disjoint; eauto. }
        specialize (Hdisj y).
        autorewrite with var_db in Hdisj.
        intuition.
      }
      Var.simplify.

      eapply (WTLetBang _ 
                Δ1 (Var.Map.remove x Δ2)
                Θ0 (Var.Map.concat Θ1 Θ3));
        [ eauto |
        | Var.simplify
        | Var.simplify
        | Var.simplify ].
      eapply IHe2; auto;
      try match goal with
      | [ |- WellTyped _ _ _ v _ ] => eauto
      | [ |- Var.Map.Partition _ _ _ ] => Var.simplify
      | [ |- ~ Var.Map.In _ _ ] => Var.simplify
      end.
      setoid_replace
        (Var.Map.add x τ (Var.Map.remove x Δ2))
        with Δ2
        by Var.solve;
      auto.


  * (* Bit b *)
    inversion He; subst; Var.simplify.

  * (* If *)
    inversion He; subst; clear He.
    partition_add_inversion; Var.simplify.

    + (* x in e1 *)
      erewrite (subst_not_in e2 x v); eauto.
      erewrite (subst_not_in e3 x v); eauto.
      eapply (WTIf (Var.Map.remove x Δ1) Δ2 (Var.Map.concat Θ1 Θ0) Θ3);
        Var.simplify.
      eapply IHe1; eauto; Var.simplify.
      setoid_replace (Var.Map.add x τ Δ1)
        with Δ1
        by Var.solve; auto.

    + (* x in e2/e3 *)

      erewrite (subst_not_in e1 x v); eauto.
      eapply (WTIf Δ1 (Var.Map.remove x Δ2) Θ0 (Var.Map.concat Θ3 Θ1));
        Var.simplify.
      - eapply IHe2; eauto; Var.simplify.
        setoid_replace (Var.Map.add x τ Δ2)
        with Δ2 by Var.solve; auto.
      - eapply IHe3; eauto; Var.simplify.
        setoid_replace (Var.Map.add x τ Δ2)
          with Δ2 by Var.solve;
        auto.

  * (* Pair *)
    inversion He; subst; clear He.
    partition_add_inversion; Var.simplify.
    
    + (* x in e1 *)
      erewrite (subst_not_in e2 x v); eauto.
      eapply (WTPair (Var.Map.remove x Δ1) Δ2 (Var.Map.concat Θ1 Θ0) Θ3);
        eauto; Var.simplify.
      eapply IHe1; eauto; Var.simplify.

      setoid_replace (Var.Map.add x τ Δ1)
        with Δ1
        by Var.solve;
      auto.

    + (* x in e2 *)
      erewrite (subst_not_in e1 x v); eauto.
      eapply (WTPair Δ1 (Var.Map.remove x Δ2) Θ0 (Var.Map.concat Θ3 Θ1));
        eauto; Var.simplify.
      eapply IHe2; eauto; Var.simplify.
      setoid_replace (Var.Map.add x τ Δ2)
        with Δ2
        by Var.solve; auto.

  * (* LetPair *) 
    rename t into y1, t0 into y2.
    inversion He; subst; clear He.
    partition_add_inversion.


    + (* x occcurs in Δ1 *)

      setoid_replace (if Var.FSet.MF.eq_dec x y1 then e2 else if Var.FSet.MF.eq_dec x y2 then e2 else subst x v e2)
        with e2.
      2:{
        reflect_partition.
        Var.simplify.
        eapply (subst_not_in e2 x v); [eauto | Var.simplify | Var.solve ].
      }

      (* Γ; Δ1-{x}; Θ1+Θ0 |- subst x v e1 : τ *)
      eapply (WTLetPair
                (Var.Map.remove x Δ1) Δ2
                (Var.Map.concat Θ1 Θ0) Θ3);
        eauto; Var.simplify.
      eapply IHe1;
        [ eauto | 
        | Var.simplify
        | auto
        | Var.simplify ].
      Var.simplify.
      setoid_replace (Var.Map.add x τ Δ1) with Δ1;
        auto with extra_var_db.

    + (* x occurs in Δ2 *)
      erewrite (subst_not_in e1 x v); eauto.
      assert (x <> y1).
      { inversion 1; subst.
        absurd (Var.Map.In y1 Δ2); auto.
        exists τ; auto.
      }
      assert (x <> y2).
      { inversion 1; subst.
        absurd (Var.Map.In y2 Δ2); auto.
        exists τ; auto.
      }
      Var.simplify.

      eapply (WTLetPair
                Δ1 (Var.Map.remove x Δ2)
                Θ0 (Var.Map.concat Θ1 Θ3));
        auto;
        try match goal with
        | [ |- Var.Map.Partition _ _ _ ] => Var.simplify
        | [ |- ~ Var.Map.In _ _ ] => Var.simplify
        | [ |- WellTyped _ _ _ e1 _ ] => eauto
        end.
      
      eapply IHe2; auto;
        try match goal with
        | [ |- WellTyped _ _ _ v _ ] => eauto
        | [ |- Var.Map.Partition _ _ _ ] => Var.simplify
        | [ |- ~ Var.Map.In _ _ ] => Var.simplify; Var.solve
        end.
      
      setoid_replace
        (Var.Map.add x τ (Var.Map.add y1 τ1 (Var.Map.add y2 τ2 (Var.Map.remove x Δ2))))
        with (Var.Map.add y1 τ1 (Var.Map.add y2 τ2 Δ2))
        by Var.solve;
      auto.

  * (* Meas *)
    inversion He; subst; clear He.
    constructor.
    eapply IHe; eauto.

  * (* QRef *)
    inversion He; subst; Var.simplify.

  * (* New *) 
    inversion He; subst; clear He.
    constructor.
    eapply IHe; eauto.

  * (* Unitary *)
    inversion He; subst; clear He.
    constructor; auto.
    eapply IHe; eauto.

  * (* Lambda *)
    rename t into y.
    inversion He; subst; clear He.
    Var.simplify.
    constructor; auto.
    eapply IHe;
      [ eauto | 
      | eauto | Var.simplify | Var.simplify ].
    setoid_replace (Var.Map.add x τ (Var.Map.add y τ1 Δ))
      with         (Var.Map.add y τ1 (Var.Map.add x τ Δ))
      by Var.solve;
      auto.
    
  * (* Fix *)
    inversion He; subst; Var.simplify.

  * (* App *)
    inversion He; subst; clear He.
    partition_add_inversion; Var.simplify.

    + (* x in e1 *)
      erewrite (subst_not_in e2 x v); eauto.
      eapply (WTApp (Var.Map.remove x Δ1) Δ2 (Var.Map.concat Θ1 Θ0) Θ3);
        eauto; Var.simplify.
      eapply IHe1; eauto; Var.simplify.

      setoid_replace (Var.Map.add x τ Δ1)
        with Δ1
        by Var.solve;
      auto.

    + (* x in e2 *)
      erewrite (subst_not_in e1 x v); eauto.
      eapply (WTApp Δ1 (Var.Map.remove x Δ2) Θ0 (Var.Map.concat Θ3 Θ1));
        eauto; Var.simplify.
      eapply IHe2; eauto; Var.simplify.
      setoid_replace (Var.Map.add x τ Δ2)
        with Δ2
        by Var.solve; auto.
    
Qed.

(* Substitution for two linear variables at a time *)
Lemma wt_subst2 : forall Θ1 Θ2 Θ0 Θ τ1 τ2 Γ Δ Θ' x1 v1 x2 v2 e τ',
  WellTyped (Var.Map.empty _) (Var.Map.empty _) Θ1 v1 τ1 ->
  WellTyped (Var.Map.empty _) (Var.Map.empty _) Θ2 v2 τ2 ->
  WellTyped Γ (Var.Map.add x1 τ1 (Var.Map.add x2 τ2 Δ)) Θ0 e τ' ->

  Var.Map.Partition Θ Θ1 Θ2 ->
  Var.Map.Partition Θ' Θ Θ0 ->
  ~ Var.Map.In x1 Δ ->
  ~ Var.Map.In x2 Δ ->
  x1 <> x2 ->
  WellTyped Γ Δ Θ' (subst x2 v2 (subst x1 v1 e)) τ'.
Proof.
  intros.
  assert (Hin : ~ Var.Map.In x1 Γ /\ ~ Var.Map.In x2 Γ).
  {
    apply wt_disjoint in H1.
    split.
    specialize (H1 x1); autorewrite with var_db in *; intuition.
    specialize (H1 x2); autorewrite with var_db in *; intuition.
  }
  destruct Hin.
  eapply wt_subst; eauto.
  eapply wt_subst; eauto.
  2:{ Var.simplify. }
  {
    reflect_partition; try reflexivity.
    Var.simplify.
  }
  {
    reflect_partition; Var.simplify; auto with extra_var_db.
    Var.Map.Proofs.reduce_concat; auto with extra_var_db.
    Var.simplify; auto with extra_var_db.
  }
Qed.