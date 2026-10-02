From Qoreo.Expr Require Import BaseProofs Substitution.

(** cfg weakening: If e can take a step with qrefs Θ1, and Θ is strictly bigger than Θ1, then e can take a step with Θ as well. *)
Lemma cfg_weakening_1 : forall Θ1 Θ1' Θ2 e Θ cfg e' Θ' cfg',
  step e Θ1 cfg e' Θ1' cfg' ->
  Var.Map.Partition Θ Θ1 Θ2 ->
  Var.Map.Partition Θ' Θ1' Θ2 ->
  step e Θ cfg e' Θ' cfg'.
Proof.
  intros ? ? ? ? ? ? ? ? ?.
  intros Hstep.
  induction Hstep; intros Hpart Hpart';
    try (constructor; auto; fail);
    try (reflect_partition; constructor; auto; try reflexivity; fail).

  * (* new *)
    Var.simplify.
    inversion H; subst; clear H.
    econstructor.
    + unfold Config.new. repeat f_equal.
    + reflect_partition.
      Var.solve.

  * (* meas *)
    Var.simplify.
    inversion H0; subst; clear H0.
    reflect_partition.
    eapply MeasB.
    2:{
      reflect_partition.
      unfold Config.measure, Config.find.
      f_equal. f_equal.
      Var.reflect_find; auto.
    }
    1:{ Var.simplify. }
    1:{
      Var.reflect_find; auto.
      specialize (Hdisj0 x).
      apply Classical_Prop.not_and_or in Hdisj0.
      destruct Hdisj0; Var.solve.
    }

  * reflect_partition.
    apply UnitaryB1; Var.simplify.
    subst.
    unfold Config.apply_gate, Config.find.
    f_equal. f_equal.
    simpl.
    Var.solve.

  * reflect_partition.
    constructor; Var.simplify.
    subst.
    unfold Config.apply_gate, Config.find.
    f_equal. f_equal.
    simpl.
    Var.solve.
Qed.

Lemma cfg_weakening_2 : forall Θ1 Θ2 Θ2' e Θ cfg e' Θ' cfg',
  step e Θ2 cfg e' Θ2' cfg' ->
  Var.Map.Partition Θ Θ1 Θ2 ->
  Var.Map.Partition Θ' Θ1 Θ2' ->
  step e Θ cfg e' Θ' cfg'.
Proof.
  intros ? ? ? ? ? ? ? ? ? Hstep Hpart Hpart'.
  eapply cfg_weakening_1; [eauto | | ].
  apply Var.Map.Properties.Partition_sym; eauto.
  apply Var.Map.Properties.Partition_sym; eauto.
Qed.

(** Step inversion: If e can take a step with refs, but its free qrefs (refs1) are only a subset of those, then it can can a step with using only refs1 *)
Lemma step_inversion : forall e refs ρ e' refs' ρ',

  step e refs ρ e' refs' ρ' ->

  forall refs1 refs2 τ,
  Config.WellScoped refs ρ ->
  WellTyped (Var.Map.empty _) (Var.Map.empty _) refs1 e τ ->
  Var.Map.Partition refs refs1 refs2 ->
  exists refs1', 
    step e refs1 ρ e' refs1' ρ'
    /\
    Var.Map.Partition refs' refs1' refs2.
Proof.
  intros ? ? ? ? ? ? Hstep.
  induction Hstep;
    intros refs1 refs2 τ HWS HWT Hpart;
    inversion HWT; subst; clear HWT;

    try (eexists;
      split;
      [ constructor; eauto; try reflexivity
      | Var.simplify ];
      fail).
  (* only the contextual rules and the quantum-specific rules should remain *)

  * Var.simplify. 
    (* refs = refs1 + refs2 = Θ1 + Θ2 + refs2 *)
    (* e1 / refs -> e1' / refs' *)
    (* Θ1 |- e1 : τ0 *)
    (* IH: e1 / Θ1 -> e1' / Θ1'  and refs' = Θ1' + Θ2 + refs2 *)

    destruct (IHHstep Θ1 (Var.Map.concat Θ2 refs2) τ0)
      as [Θ1' [IH Hpart']]; auto; Var.simplify.
    (* By weakening:
       e1 / refs1 -> e1' / refs1'  where refs1' = Θ1' + Θ2
    *)
    exists (Var.Map.concat Θ1' Θ2).
    split.
    2:{ Var.simplify. }
    eapply cfg_weakening_1.
    + apply LetC. eauto.
    + eauto.
    + Var.simplify.

  * Var.simplify.

    edestruct (IHHstep Θ1 (Var.Map.concat Θ2 refs2))
      as [Θ1' [IH Hpart']]; eauto; Var.simplify.
    (* By weakening:
       e1 / refs1 -> e1' / refs1'  where refs1' = Θ1' + Θ2
    *)
    exists (Var.Map.concat Θ1' Θ2).
    split; Var.simplify.
    eapply cfg_weakening_1;
      [econstructor; eauto | | ]; eauto; Var.simplify.

  * (* IfC *)
    Var.simplify.

    (* refs = refs1 + refs2 = Θ1 + Θ2 + refs2 *)
    (* e1 / refs -> e1' / refs' *)
    (* Θ1 |- e1 : τ0 *)
    (* IH: e1 / Θ1 -> e1' / Θ1'  and refs' = Θ1' + Θ2 + refs2 *)
    edestruct (IHHstep Θ1 (Var.Map.concat Θ2 refs2))
      as [Θ1' [IH Hpart']]; eauto; Var.simplify.
    (* By weakening:
       e1 / refs1 -> e1' / refs1'  where refs1' = Θ1' + Θ2
    *)
    exists (Var.Map.concat Θ1' Θ2).
    split; Var.simplify.
    eapply cfg_weakening_1.
    + apply IfC. eauto.
    + eauto.
    + Var.simplify.

  * (* PairC1 *)
    Var.simplify.

    (* refs = refs1 + refs2 = Θ1 + Θ2 + refs2 *)
    (* e1 / refs -> e1' / refs' *)
    (* Θ1 |- e1 : τ0 *)
    (* IH: e1 / Θ1 -> e1' / Θ1'  and refs' = Θ1' + Θ2 + refs2 *)
    edestruct (IHHstep Θ1 (Var.Map.concat Θ2 refs2))
      as [Θ1' [IH Hpart']]; eauto; Var.simplify.
    (* By weakening:
       e1 / refs1 -> e1' / refs1'  where refs1' = Θ1' + Θ2
    *)
    exists (Var.Map.concat Θ1' Θ2).
    reflect_partition.
    split; Var.simplify.
    eapply cfg_weakening_1.
    { apply PairC1; eauto. }
    all:Var.simplify.

  * (* PairC2 *)
    Var.simplify.

    (* refs = refs1 + refs2 = Θ1 + Θ2 + refs2 *)
    (* e1 / refs -> e1' / refs' *)
    (* Θ1 |- e1 : τ0 *)
    (* IH: e1 / Θ1 -> e1' / Θ1'  and refs' = Θ1' + Θ2 + refs2 *)
    edestruct (IHHstep Θ2 (Var.Map.concat Θ1 refs2))
      as [Θ2' [IH Hpart']]; eauto; Var.simplify.
    exists (Var.Map.concat Θ1 Θ2').
    split; Var.simplify.
    reflect_partition.
    eapply cfg_weakening_1.
    { apply PairC2; eauto. }
    all: Var.simplify.

  * (* LetPair *)
    Var.simplify.

    (* refs = refs1 + refs2 = Θ1 + Θ2 + refs2 *)
    (* e1 / refs -> e1' / refs' *)
    (* Θ1 |- e1 : τ0 *)
    (* IH: e1 / Θ1 -> e1' / Θ1'  and refs' = Θ1' + Θ2 + refs2 *)
    edestruct (IHHstep Θ1 (Var.Map.concat Θ2 refs2))
      as [Θ1' [IH Hpart']]; eauto; Var.simplify.
    (* By weakening:
       e1 / refs1 -> e1' / refs1'  where refs1' = Θ1' + Θ2
    *)
    exists (Var.Map.concat Θ1' Θ2).
    split; Var.simplify.
    reflect_partition.
    eapply cfg_weakening_1.
    { apply LetPairC. eauto. }
    all: Var.simplify.

  * (* AppC1 *)
    Var.simplify.

    (* refs = refs1 + refs2 = Θ1 + Θ2 + refs2 *)
    (* e1 / refs -> e1' / refs' *)
    (* Θ1 |- e1 : τ0 *)
    (* IH: e1 / Θ1 -> e1' / Θ1'  and refs' = Θ1' + Θ2 + refs2 *)
    edestruct (IHHstep Θ1 (Var.Map.concat Θ2 refs2))
      as [Θ1' [IH Hpart']]; eauto; Var.simplify.
    (* By weakening:
       e1 / refs1 -> e1' / refs1'  where refs1' = Θ1' + Θ2
    *)
    exists (Var.Map.concat Θ1' Θ2).
    split; Var.simplify.
    reflect_partition.
    eapply cfg_weakening_1.
    { apply AppC1. eauto. }
    all: Var.simplify.

  * (* AppC2 *)
    Var.simplify.

    (* refs = refs1 + refs2 = Θ1 + Θ2 + refs2 *)
    (* e1 / refs -> e1' / refs' *)
    (* Θ2 |- e2 : τ2 *)
    (* IH: e2 / Θ2 -> e2' / Θ2'  and refs' = Θ1 + Θ2' + refs2 *)
    edestruct (IHHstep Θ2 (Var.Map.concat Θ1 refs2))
      as [Θ2' [IH Hpart']]; eauto; Var.simplify.
    (* By weakening:
       e1 / refs1 -> e1' / refs1'  where refs1' = Θ1' + Θ2
    *)
    exists (Var.Map.concat Θ1 Θ2').
    split; Var.simplify.
    reflect_partition.
    eapply cfg_weakening_1.
    { apply AppC2; eauto. }
    all: Var.simplify.

  * (* NewC *)  
    edestruct (IHHstep refs1 refs2)
      as [Θ1' [IH Hpart']]; eauto.
    exists Θ1'.
    split; Var.simplify.
    reflect_partition.
    eapply cfg_weakening_1.
    { apply NewC. eauto. }
    + apply Var.Map.Proofs.partition_empty_r.
    + apply Var.Map.Proofs.partition_empty_r.

  * (* NewB *)
    Var.simplify.
    inversion H; subst; clear H.
    exists (Var.Map.add (Config.dim cfg) (Config.dim cfg) refs1).
    split.
    2:{
      apply Var.Map.Proofs.partition_add_l; auto.
      (* refs1 and refs2 are wellscoped *)
      reflect_partition. Var.simplify.
      intros Hin.
      eapply Config.wf_qrefs in Hin; eauto.
      lia.
    }
    econstructor; reflexivity.

  * (* MeasC *)
    edestruct (IHHstep refs1 refs2)
      as [Θ1' [IH Hpart']]; eauto.
    exists Θ1'.
    split; Var.simplify.
    reflect_partition.
    eapply cfg_weakening_1.
    { apply MeasC. eauto. }
    + apply Var.Map.Proofs.partition_empty_r.
    + apply Var.Map.Proofs.partition_empty_r.

  * (* MeasB *)
    repeat match goal with
    | [ H : _ = Config.measure _ _ _ _ |- _ ] =>
      inversion H; subst; clear H
    | [ H : WellTyped _ _ _ (QRef _) _ |- _ ] =>
      inversion H; subst; clear H; Var.simplify
    end.

    exists (Var.Map.empty nat).
    reflect_partition; Var.simplify.
    split; Var.simplify.
    2:{ reflect_partition; Var.solve. }
    eapply MeasB.
    2:{
      unfold Config.measure.
      f_equal. f_equal. f_equal. f_equal.
      unfold Config.find.
      Var.simplify.
    }
    all: Var.simplify.

  *
    edestruct (IHHstep refs1 refs2)
      as [Θ1' [IH Hpart']]; eauto.
    exists Θ1'.
    split; Var.simplify.
    reflect_partition.
    apply UnitaryC; auto.

  * (* UnitaryB1 *) 
    match goal with
    | [ H : WellTyped _ _ _ (QRef _) _ |- _ ] =>
      inversion H; subst; clear H
    end.
    Var.simplify.
    exists (Var.Map.add q idx (Var.Map.empty nat)).
    split; auto.
    apply UnitaryB1.
    2:{
      unfold Config.apply_gate, Config.find.
      f_equal. f_equal.
      simpl.
      reflect_partition.
      Var.simplify.
    }
    all: Var.simplify.

  * (* UnitaryB2 *)
    repeat match goal with
    | [ H : WellTyped _ _ _ (Pair _ _) _ |- _ ] =>
      inversion H; subst; clear H
    | [ H : WellTyped _ _ _ (QRef _) _ |- _ ] =>
      inversion H; subst; clear H
    end.
    Var.simplify.
    exists refs1.
    split; auto.
    reflect_partition. Var.simplify.
    apply UnitaryB2; auto.
    3:{
      unfold Config.apply_gate, Config.find.
      f_equal. f_equal.
      simpl.
      Var.simplify.
    }
    all: Var.simplify.
Qed.


Ltac cfg_weakening_tac :=
  match goal with
  | [ Hstep : step ?e ?refs ?ρ ?e' ?refs' ?ρ',
      HTyped : WellTyped ?Γ ?Δ ?Θ ?e ?τ
      |- _ ] =>
      let refs1 := fresh "refs1" in
      let Hstep1 := fresh "Hstep1" in
      let Hpart1 := fresh "Hpart1" in
      edestruct (step_inversion _ _ _ _ _ _ Hstep) as [refs1 [Hstep1 Hpart1]]; eauto
  end.



(** Typing preservation *)
Lemma WellTyped_preservation : forall Γ Δ Θ e τ,
  WellTyped Γ Δ Θ e τ ->

  forall ρ e' Θ' ρ',
  Var.Map.Empty Γ ->
  Var.Map.Empty Δ ->
  Config.WellScoped Θ ρ ->
  
  step e Θ ρ e' Θ' ρ' ->
  
  WellTyped Γ Δ Θ' e' τ.
Proof.
  intros ? ? ? ? ? HWT.
  induction HWT; intros ? ? ? ? HΓ HΔ HWS Hstep;
    try (rewrite HΔ in *; clear Δ HΔ);
    try (rewrite HΔ' in *; clear Δ' HΔ');
    try (inversion Hstep; auto; fail).
  * Var.simplify.
    assert (~ Var.Map.In x (Var.Map.empty typ))
      by (Var.simplify; auto).
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *)  

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      cfg_weakening_tac; eauto.
      econstructor; eauto with var_db.
      reflect_partition. Var.simplify.
      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply IHHWT1; eauto with var_db.
      
    + eapply wt_subst; eauto.
      Var.simplify.

  * (* Let!*)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *)

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      cfg_weakening_tac.
      econstructor; eauto with var_db; Var.simplify.
      reflect_partition. Var.simplify.
      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply IHHWT1; eauto with var_db.

    + (* beta *)

      inversion HWT1; subst.
      Var.simplify.
      eapply wt_subst_bang; eauto with var_db.
    

  * (* If *) 
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e -> e1' *)
      cfg_weakening_tac.
      econstructor; eauto with var_db.
      reflect_partition. Var.simplify.
      eapply IHHWT1; eauto with var_db.

    + inversion HWT1; subst.
      Var.simplify.
      destruct b; auto.

  * (* Pair *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + cfg_weakening_tac.
      econstructor; eauto with var_db.
      reflect_partition; Var.simplify.
      eapply IHHWT1; eauto with var_db.      

    + cfg_weakening_tac; eauto with var_db.
      {
        apply Var.Map.Properties.Partition_sym.
        eauto with var_db.
      }
      econstructor; eauto with var_db.
      2:{ apply Var.Map.Properties.Partition_sym; eauto. }
      reflect_partition. Var.simplify.
      eapply IHHWT2; eauto with var_db.

  * (* LetPair *) 
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      cfg_weakening_tac.

      econstructor; eauto with var_db;
        Var.simplify.
      reflect_partition; Var.simplify.

      (* So by the IH, Γ;refs1' |- e1' : τ *)
      eapply IHHWT1; eauto with var_db.

    + inversion HWT1; subst; clear HWT1.
      match goal with
      | [ H : Val (Pair _ _) |- _ ] =>
          inversion H; subst; clear H
      end.
      Var.simplify.
      autorewrite with var_db in HWT2.
      eapply wt_subst2; eauto;
      Var.simplify.

  * (* Meas *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      cfg_weakening_tac; eauto with var_db.
      econstructor; eauto with var_db.
      

    + inversion HWT; subst; clear HWT.
      match goal with
      | [ H : _ = Config.measure _ _ _ _ |- _ ] =>
        inversion H; subst; clear H
      end.
      Var.simplify.
      econstructor; eauto with var_db.
      econstructor; eauto with var_db.

  * (* New *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      cfg_weakening_tac; eauto with var_db.
      econstructor; eauto with var_db.

    + match goal with
      | [ H : _ = Config.new _ _ _ |- _ ] =>
        inversion H; subst; clear H
      end.
      inversion HWT; subst; clear HWT.
      Var.simplify.
      econstructor; eauto with var_db.
      Var.simplify.

  * (* Unitary *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      cfg_weakening_tac; eauto with var_db.
      econstructor; eauto.
      eapply IHHWT; eauto with var_db.

    + inversion HWT; subst.
      econstructor; eauto.
      Var.simplify.

    + inversion HWT; subst; auto.
      econstructor; eauto.
      Var.simplify.

  * (* App *)
    Var.simplify.
    inversion Hstep; subst; clear Hstep.
    + (* e1 -> e1' *) 

      (* We are given: (e1,refs) ~> (e1',refs') *)
      (* By weakening, we know that (e1,refs1) ~> (e1',refs1') where refs'=refs1' + refs2 *)
      cfg_weakening_tac; eauto with var_db.
      econstructor; eauto; eauto with var_db.
      reflect_partition. Var.simplify.
      eapply IHHWT1; eauto with var_db.      

    + (* e2 -> e2' *)
      cfg_weakening_tac.
      { apply Var.Map.Properties.Partition_sym; eauto. }
      econstructor; eauto with var_db.
      2:{ apply Var.Map.Properties.Partition_sym; eauto. }

      reflect_partition. Var.simplify.

      eapply IHHWT2; eauto with var_db.

    + (* Lambda beta reduction *)
      inversion HWT1; subst; clear HWT1.
      Var.simplify.
      eapply wt_subst; eauto; Var.simplify.
      { apply Var.Map.Properties.Partition_sym; eauto. }

    + (* Fix beta reduction *)
      (*
        f:!τ -o τ', x:τ; ∅; Θ1 ⊢ e : τ'     ∅;∅;∅ ⊢ v2 : τ
        ------------------------------    --------------------
        ∅;∅;Θ1 ⊢ fix f.x.e : !τ -o τ'    ∅;∅;∅ ⊢ !v2 : !τ
        -----------------------------------------------------
        ∅;∅;Θ1 ⊢ (fix f.x.e) !v2 : τ'

      WTS
      ∅;∅;Θ1,Θ2 ⊢ e{fix f.x.e / f, e2/x} : τ'
      *)
      inversion HWT1; subst.
      inversion HWT2; subst.
      Var.simplify.

      eapply wt_subst_bang; eauto with var_db.
      eapply wt_subst_bang; eauto with var_db.
Qed.

(** Scoping preservation *)
Lemma WellScoped_preservation : forall e Θ ρ e' Θ' ρ',
  step e Θ ρ e' Θ' ρ' ->
  Config.WellScoped Θ ρ ->
  Config.WellScoped Θ' ρ'.
Proof.
  intros ? ? ? ? ? ? Hstep.
  induction Hstep; intros HWS; auto; Var.simplify.
  * (* new *)
    inversion H; subst; clear H.
    destruct HWS.
    split; simpl in *.
    + auto with wf_db.
    + intros x Hin.
      Var.simplify.
      destruct Hin as [? | Hin]; subst; [lia | ].
      rewrite wf_qrefs; [ lia | auto].
  * (* measure *) 
    inversion H0; subst; clear H0.
    destruct HWS.
    split; simpl in *.
    + unfold super. auto with wf_db.
    + intros z Hin. Var.simplify.
  * (* apply_gate *)
    subst.
    unfold Config.apply_gate.
    destruct HWS.
    split; auto.
    simpl. unfold Config.find.
    Var.reflect_find.
    unfold super.
    destruct g; simpl; auto with wf_db.

  * subst. unfold Config.apply_gate.
    destruct HWS.
    split; auto.
    simpl. unfold Config.find.
    Var.reflect_find.
    unfold super.
    destruct g; simpl; auto with wf_db.
Qed.

(** Combined preservation lemma *)
Theorem preservation :  forall Θ e τ ρ e' Θ' ρ',
  WellTyped (Var.Map.empty _) (Var.Map.empty _) Θ e τ ->
  Config.WellScoped Θ ρ ->
  step e Θ ρ e' Θ' ρ' ->
  WellTyped (Var.Map.empty _) (Var.Map.empty _) Θ' e' τ /\ Config.WellScoped Θ' ρ'.
Proof.
  intros ? ? ? ? ? ? ? HWT HWS Hstep.
  split.
  * eapply WellTyped_preservation; eauto; Var.simplify.
  * eapply WellScoped_preservation; eauto.
Qed.


(** ** Progress *)

Lemma step_WellScoped_disjoint : forall Θ2 e Θ1 cfg e' Θ1' cfg',
  step e Θ1 cfg e' Θ1' cfg' ->
  Var.Map.Properties.Disjoint Θ1 Θ2 ->
  Config.WellScoped Θ2 cfg ->
  Var.Map.Properties.Disjoint Θ1' Θ2.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  revert Θ2.
  induction Hstep; intros Θ2 Hdisj Hws; auto;
  Var.simplify.
  * (* new *)
    unfold Config.new in H.
    inversion H; subst; clear H.
    Var.simplify.
    split; auto.
    { (* dim cfg ∉ Θ2 *)
      destruct Hws as [_ Hws].
      intros Hin.
      apply Hws in Hin.
      lia.
    }
  * (* measure *)
    unfold Config.measure in H0.
    inversion H0; subst; clear H0.
    apply Var.Map.Proofs.disjoint_remove_1; auto.
Qed.

