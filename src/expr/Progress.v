From Qoreo.Expr Require Import BaseProofs.
From Qoreo.Expr Require Preservation.

Ltac ws_partition_tac :=
  match goal with
  | [Hpart : Var.Map.Partition ?Θ ?Θ1 ?Θ2,
     H : Config.WellScoped ?θ ?cfg |- _ ] =>
     let H' := fresh "H" in
     assert (H' : Config.WellScoped Θ1 cfg /\ Config.WellScoped Θ2 cfg)
     by (apply Config.WellScoped_concat; reflect_partition; auto);
     destruct H'
  end.
Ltac ws_step_tac :=
  match goal with
  | [ Hstep : step ?e ?Θ1 ?cfg ?e' ?Θ1' ?cfg' |- Var.Map.Partition _ ?Θ1' ?Θ2 ] =>
      reflect_partition; [ | reflexivity];
      eapply Preservation.step_WellScoped_disjoint; eauto
  | [ Hpart : Var.Map.Partition ?Θ ?Θ1 ?Θ2,
      Hstep : step ?e ?Θ1 ?cfg ?e' ?Θ1' ?cfg' |- _ ] =>
      let H' := fresh "H" in
      assert (H' : Var.Map.Partition (Var.Map.concat Θ1' Θ2) Θ1' Θ2)
      by (reflect_partition; [ | reflexivity];
          eapply Preservation.step_WellScoped_disjoint; eauto)
  end.



Ltac simplify_val :=
  repeat match goal with
  | [ Hval : Val ?e, Hwt : WellTyped _ _ _ ?e ?τ |- _ ] =>
    match τ with
    | BIT => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    | QUBIT  => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    | Tensor _ _ => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    | Lolli _ _ => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    | BANG _ => inversion Hwt; subst; inversion Hval; subst; clear Hval Hwt
    end
  end.

(* Type progress: well-typed expressions are either values or they can take a step *)
Theorem progress : forall e τ Γ Δ Θ,
  WellTyped Γ Δ Θ e τ ->
  forall cfg,
  Config.WellScoped Θ cfg ->
  Var.Map.Empty Γ ->
  Var.Map.Empty Δ ->
  Val e \/ exists e' Θ' cfg', step e Θ cfg e' Θ' cfg'.
Proof.
  intros e τ Γ Δ Θ Hwt.
  induction Hwt; intros cfg Hscoped HΓ HΔ;
    vsimpl;
    autorewrite with var_db in *;
    try contradiction;
    try (left; auto with var_db; fail).

  * (* Let *)
    ws_partition_tac.
    
    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    + (* e1 is a value *)
      right. eexists. eexists. eexists.
      eapply LetB; eauto; try reflexivity.

    + (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply LetC; eauto.
      eapply Preservation.cfg_weakening_1; eauto;
        ws_step_tac.

  * (* Let! *)
    ws_partition_tac.

    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    + (* e1 is a value *)
      (* e1 must be of the form (Bang e1') *)
      simplify_val.
      right. eexists. eexists. eexists.
      eapply LetBangB; auto; try reflexivity.

    + (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply LetBangC; eauto.
      eapply Preservation.cfg_weakening_1; eauto;
        ws_step_tac.

  * (* If *)
    ws_partition_tac.

    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    + (* e1 is a value *)
      (* e1 must be of the form Bit b *)
      simplify_val.
      right. eexists. eexists. eexists.
      eapply IfB; auto; try reflexivity.

    + (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply IfC; eauto.
      eapply Preservation.cfg_weakening_1; eauto;
        ws_step_tac.

  * (* Pair *)
    ws_partition_tac.
    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    2:{ (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply PairC1; eauto.
      eapply Preservation.cfg_weakening_1; eauto;
        ws_step_tac.
    }
    edestruct IHHwt2 as [Hv2 | [e2' [Θ2' [cfg' Hstep2]]]];
      eauto with var_db.
    { (* e2 can take a step *)
      right. eexists. eexists. eexists.
      apply PairC2; eauto.
      eapply Preservation.cfg_weakening_2; [eauto | eauto with var_db | ];
        auto.
      {
        reflect_partition; try reflexivity.
        apply Var.Map.Proofs.disjoint_sym.
        eapply Preservation.step_WellScoped_disjoint; eauto.
        apply Var.Map.Proofs.disjoint_sym; auto.
      }
    }

  * (* LetPair *)
    ws_partition_tac.
    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    + (* e1 is a value *)
      (* e1 must be of the form Bit b *)
      simplify_val.
      right. eexists. eexists. eexists.
      eapply LetPairB; auto with var_db; try reflexivity.

    + (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply LetPairC; eauto.
      eapply Preservation.cfg_weakening_1; eauto;
        ws_step_tac.
  
  * (* Meas *)
    edestruct IHHwt as [Hv | [e' [Θ' [cfg' Hstep]]]];
      eauto with var_db.
    + (* e' is a value -- must be a qref *)
      simplify_val.
      right. eexists. eexists. eexists.
      Var.simplify.
      eapply MeasB; Var.simplify.

    + (* e' can take a step *)
      right. eexists. eexists. eexists.
      apply MeasC; eauto.

  * (* New *)
    edestruct IHHwt as [Hv | [e' [Θ' [cfg' Hstep]]]];
      eauto with var_db.
    + (* e' is a value -- must be a bit *)
      simplify_val.
      right. eexists. eexists. eexists.
      eapply NewB; try reflexivity.

    + (* e' can take a step *)
      right. eexists. eexists. eexists.
      apply NewC; eauto.

  * (* Unitary *)
    edestruct IHHwt as [Hv | [e' [Θ' [cfg' Hstep]]]];
      eauto with var_db.
    
    + (* e' is a value *)

      (* τ = Qubit or Qubit ** Qubit *)
      assert (Hτ : τ = QUBIT \/ τ = Tensor QUBIT QUBIT).
      { destruct U; inversion H; subst; auto. }
      destruct Hτ as [Hτ | Hτ]; rewrite Hτ in *.
      - (* τ = QUBIT *)
        simplify_val.
        right. eexists. eexists. eexists.
        eapply UnitaryB1; eauto.
        unfold Var.Map.Singleton in *.
        Var.simplify.

      - (* τ = Tensor QUBIT QUBIT *)
        simplify_val.
        unfold Var.Map.Singleton in *.
        vsimpl.
        reflect_partition.
        right. eexists. eexists. eexists.
        eapply UnitaryB2; auto; Var.simplify.

    + (* e can take a step *)
      right. eexists. eexists. eexists.
      apply UnitaryC; eauto.

  * (* App *)
    ws_partition_tac.
    edestruct IHHwt1 as [Hv1 | [e1' [Θ1' [cfg' Hstep1]]]];
      eauto with var_db.
    2:{ (* e1 can take a step *)
      right. eexists. eexists. eexists.
      apply AppC1; eauto.
      eapply Preservation.cfg_weakening_1; eauto;
        ws_step_tac.
    }
    edestruct IHHwt2 as [Hv2 | [e2' [Θ2' [cfg' Hstep2]]]];
      eauto with var_db.
    2:{ (* e2 can take a step *)
      right. eexists. eexists. eexists.
      apply AppC2; eauto.
      eapply Preservation.cfg_weakening_2; eauto.
      {
        reflect_partition; try reflexivity.
        apply Var.Map.Proofs.disjoint_sym.
        eapply Preservation.step_WellScoped_disjoint; eauto.
        apply Var.Map.Proofs.disjoint_sym; auto.
      }
    }
    (* both e1 and e2 are values *)
    simplify_val.
    - (* v1 is a lambda *)
      right. eexists. eexists. eexists.
      eapply AppB; eauto; try reflexivity.

    - (* v1 is a fix *)
      right. eexists. eexists. eexists.
      eapply AppFixB; eauto; try reflexivity.

Unshelve. exact true.
Qed.