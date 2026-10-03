

Lemma bangval_inversion : forall Gamma Delta Theta e tau,
    Expr.WellTyped Gamma Delta Theta e (Expr.BANG tau) ->
    Expr.Val e ->
    exists e0, e = Expr.Bang e0.
Proof.
  intros.
  Expr.simplify_val.
  exists e0.
  auto.
Qed.

Lemma tensorval_inversion : forall Gamma Delta Theta e tau1 tau2,
    Expr.WellTyped Gamma Delta Theta e (Expr.Tensor tau1 tau2) ->
    Expr.Val e ->
    exists v1 v2, e = Expr.Pair v1 v2 /\ Expr.Val v1 /\ Expr.Val v2 .
Proof.
  intros.
  Expr.simplify_val.
  exists e1.
  exists e2.
  auto.
Qed.

Lemma step_scope : forall Theta Theta2 e Theta1 cfg1 e' Theta1' cfg2,
    Config.WellScoped Theta cfg1 ->
    Var.Map.Partition Theta Theta1 Theta2 ->
    Expr.step e Theta1 cfg1 e' Theta1' cfg2 ->
    Var.Map.Properties.Disjoint Theta1' Theta2.
Proof.
  intros ? ? ? ? ? ? ? ? HWS Hpart Hstep.
  dependent induction Hstep;
    Var.Map.Tactics.reflect_partition; auto;
    try (apply IHHstep; auto;
      Var.Map.Tactics.reflect_partition; auto;
      try reflexivity).

  * inversion H; subst; clear H.
    Var.simplify.
    split; auto.
    intros Hin; eapply Config.wf_qrefs in Hin; eauto.
    lia.
  * inversion H0; subst; clear H0.
    apply Var.Map.Proofs.disjoint_remove_1; auto.
Qed.

Lemma epr_exists : forall A B T cfg,
  exists q1 q2 T0 cfg',  ChorEnv.epr A B T cfg = (q1, q2, T0, cfg').
Proof.
  intros.
  eexists. eexists. eexists. eexists.
  Var.simplify.
Qed.
       
(** Progress *)
Theorem progress : forall G D T1 C1,
    WellTyped G D T1 C1 ->
    forall cfg1,
      ChorEnv.WellScoped T1 cfg1 ->
      Actor.Map.Empty G ->
      Actor.Map.Empty D ->
      C1 = [] \/ exists l C2 T2 cfg2, step C1 T1 cfg1 l C2 T2 cfg2.
Proof.
  intros G D T1 C1 HWT.
  induction HWT; intros cfg1 Hscoped HGempty HDempty.

  (* Case Nil *)
  - auto.

  (* Case EPR *)
  - right.

    destruct (epr_exists A B T cfg1) as [q1 [q2 [T0 [cfg2 Hepr]]]].

    exists (Label.EPR A B).
    exists (Choreography.subst A x (Expr.QRef q1)
              (Choreography.subst B y (Expr.QRef q2) C)).
    eexists T0. 
    exists cfg2.

    eapply EPRB.
    eauto.
    Var.simplify.
    eauto.

  (* Case Send *)
  - right.

    (* This disjunction allows destruction into context and beta subcases *)
    assert (Expr.Val e \/ ~ Expr.Val e) as Hvale.
    tauto.
    destruct Hvale as [HvaleL | HvaleR].
    {
      pose proof (bangval_inversion (ChorEnv.find A G) DeltaA1 ThetaA1 e tau H0 HvaleL) as Hbang.
      destruct Hbang as [e0 Hbang].
      rewrite Hbang in H0.
      rewrite Hbang.

      exists (Label.Send A e0 B).
      exists (Choreography.subst B y e0 C).
      exists T.
      exists cfg1.

      apply SendB.
      auto.
      Var.simplify.
    }
    { 
      unfold ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      pose proof (ChorEnv.ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H2) as Hpart.
      
      pose proof
        (Expr.progress e (Expr.BANG tau) (ChorEnv.find A G) DeltaA1 ThetaA1 H0 cfg1 Hpart) as Heprog.

      rewrite (empty_eq_env G HGempty) in Heprog.

      assert (Var.Map.Empty (ChorEnv.find A D)) as HADempty.
      {
        rewrite (empty_eq_env D HDempty).
        apply (empty_is_empty A).
      }
     
      specialize (Heprog (empty_is_empty A)
                    (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H1)).

      destruct Heprog as [Habsurd | HeprogR].
      { contradiction. }
      {
        destruct HeprogR as [e' [ThetaA1' [cfg2 HeprogR]]].

        exists (Label.Loc A).
        exists (Insn.Send A e' B y :: C).
        exists (Actor.Map.add A (Var.Map.concat ThetaA1' ThetaA2) T).
        exists cfg2.

        eapply SendC.
        auto.
        Var.simplify.

        pose proof (concat_partition ThetaA1' ThetaA2
                      (step_scope (ChorEnv.find A T)
                         ThetaA2 e ThetaA1 cfg1 e' ThetaA1' cfg2
                         Hscoped H2 HeprogR)) as Hstepscope.

        pose proof (Expr.cfg_weakening_1
                      ThetaA1 ThetaA1' ThetaA2 e
                      (ChorEnv.find A T) cfg1 e'
                      (Var.Map.concat ThetaA1' ThetaA2)
                      cfg2
                      HeprogR H2 Hstepscope).
        eauto.
        Var.simplify.
      }
    }

  (* Case LetBang *)
  - right.

    (* This disjunction allows destruction into context and beta subcases *)
    assert (Expr.Val e \/ ~ Expr.Val e) as Hvale.
    tauto.
    destruct Hvale as [HvaleL | HvaleR].
    {
      pose proof (bangval_inversion (ChorEnv.find A G) DeltaA1 ThetaA1 e tau H HvaleL) as Hbang.
      destruct Hbang as [e0 Hbang].
      rewrite Hbang in H.
      rewrite Hbang.

      exists (Label.Loc A).
      exists (Choreography.subst A x e0 C).
      exists T.
      exists cfg1.

      apply LetBangB.
      auto.
      Var.simplify.
    }
    { 
      unfold ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      pose proof (ChorEnv.ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1) as Hpart.
      
      pose proof
        (Expr.progress e (Expr.BANG tau) (ChorEnv.find A G) DeltaA1 ThetaA1 H cfg1 Hpart) as Heprog.

      rewrite (empty_eq_env G HGempty) in Heprog.

      assert (Var.Map.Empty (ChorEnv.find A D)) as HADempty.
      {
        rewrite (empty_eq_env D HDempty).
        apply (empty_is_empty A).
      }
     
      specialize (Heprog (empty_is_empty A)
                    (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0)).

      destruct Heprog as [Habsurd | HeprogR].
      { contradiction. }
      {
        destruct HeprogR as [e' [ThetaA1' [cfg2 HeprogR]]].

        exists (Label.Loc A).
        exists (Insn.LetBang A x e' :: C).
        exists (Actor.Map.add A (Var.Map.concat ThetaA1' ThetaA2) T).
        exists cfg2.

        eapply LetBangC.
 
        pose proof (concat_partition ThetaA1' ThetaA2
                      (step_scope (ChorEnv.find A T)
                         ThetaA2 e ThetaA1 cfg1 e' ThetaA1' cfg2
                         Hscoped H1 HeprogR)) as Hstepscope.

        pose proof (Expr.cfg_weakening_1
                      ThetaA1 ThetaA1' ThetaA2 e
                      (ChorEnv.find A T) cfg1 e'
                      (Var.Map.concat ThetaA1' ThetaA2)
                      cfg2
                      HeprogR H1 Hstepscope).
        eauto.
        Var.simplify.
      }
    }

  (* Case LetIn *)
  - right.

    (* This disjunction allows destruction into context and beta subcases *)
    assert (Expr.Val e \/ ~ Expr.Val e) as Hvale.
    tauto.
    destruct Hvale as [HvaleL | HvaleR].
    {
      exists (Label.Loc A).
      exists (Choreography.subst A x e C).
      exists T.
      exists cfg1.

      apply LetB.
      auto.
      Var.simplify.
      Var.simplify.
    }
    { 
      unfold ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      pose proof (ChorEnv.ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1) as Hpart.
      
      pose proof
        (Expr.progress e tau (ChorEnv.find A G) DeltaA1 ThetaA1 H cfg1 Hpart) as Heprog.

      rewrite (empty_eq_env G HGempty) in Heprog.

      assert (Var.Map.Empty (ChorEnv.find A D)) as HADempty.
      {
        rewrite (empty_eq_env D HDempty).
        apply (empty_is_empty A).
      }
     
      specialize (Heprog (empty_is_empty A)
                    (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0)).

      destruct Heprog as [Habsurd | HeprogR].
      { contradiction. }
      {
        destruct HeprogR as [e' [ThetaA1' [cfg2 HeprogR]]].

        exists (Label.Loc A).
        exists (Insn.Let A x e' :: C).
        exists (Actor.Map.add A (Var.Map.concat ThetaA1' ThetaA2) T).
        exists cfg2.

        eapply LetC.
 
        pose proof (concat_partition ThetaA1' ThetaA2
                      (step_scope (ChorEnv.find A T)
                         ThetaA2 e ThetaA1 cfg1 e' ThetaA1' cfg2
                         Hscoped H1 HeprogR)) as Hstepscope.

        pose proof (Expr.cfg_weakening_1
                      ThetaA1 ThetaA1' ThetaA2 e
                      (ChorEnv.find A T) cfg1 e'
                      (Var.Map.concat ThetaA1' ThetaA2)
                      cfg2
                      HeprogR H1 Hstepscope).
        eauto.
        Var.simplify.
      }
    }

  (* Case LetPair *)
  - right.

    (* This disjunction allows destruction into context and beta subcases *)
    assert (Expr.Val e \/ ~ Expr.Val e) as Hvale.
    tauto.
    destruct Hvale as [HvaleL | HvaleR].
    {
      pose proof (tensorval_inversion
                    (ChorEnv.find A G) DeltaA1 ThetaA1 e tau1 tau2 H HvaleL) as Htensor.
      destruct Htensor as [v1 [v2 [HtensorA [HtensorB HtensorC]]]].
      rewrite HtensorA in H.
      rewrite HtensorA.
      
      exists (Label.Loc A).
      exists (Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C)).
      exists T.
      exists cfg1.

      apply LetPairB; auto.
      Var.simplify.
    }
    { 
      unfold ChorEnv.WellScoped in Hscoped.
      specialize (Hscoped A).
      pose proof (ChorEnv.ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1) as Hpart.
      
      pose proof
        (Expr.progress
           e (Expr.Tensor tau1 tau2) (ChorEnv.find A G) DeltaA1 ThetaA1 H cfg1 Hpart) as Heprog.

      rewrite (empty_eq_env G HGempty) in Heprog.

      assert (Var.Map.Empty (ChorEnv.find A D)) as HADempty.
      {
        rewrite (empty_eq_env D HDempty).
        apply (empty_is_empty A).
      }
     
      specialize (Heprog (empty_is_empty A)
                    (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0)).

      destruct Heprog as [Habsurd | HeprogR].
      { contradiction. }
      {
        destruct HeprogR as [e' [ThetaA1' [cfg2 HeprogR]]].

        exists (Label.Loc A).
        exists (Insn.LetPair A x1 x2 e' :: C).
        exists (Actor.Map.add A (Var.Map.concat ThetaA1' ThetaA2) T).
        exists cfg2.

        eapply LetPairC.
 
        pose proof (concat_partition ThetaA1' ThetaA2
                      (step_scope (ChorEnv.find A T)
                         ThetaA2 e ThetaA1 cfg1 e' ThetaA1' cfg2
                         Hscoped H1 HeprogR)) as Hstepscope.

        pose proof (Expr.cfg_weakening_1
                      ThetaA1 ThetaA1' ThetaA2 e
                      (ChorEnv.find A T) cfg1 e'
                      (Var.Map.concat ThetaA1' ThetaA2)
                      cfg2
                      HeprogR H1 Hstepscope).
        eauto.
        Var.simplify.
      }
    }

Qed.
