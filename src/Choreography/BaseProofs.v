From Qoreo.Base Require Import Var.
From Qoreo Require Expr.Expr.
From Qoreo.Choreography Require Import Choreography.


From Stdlib Require Export Lia List.
Export List.ListNotations.


(* Helpful Lemmas about binding equality based on Insn.beq *)
Lemma beq : forall A B x y,
    Insn.bind_eqb (A, x) (B, y) = true <-> (A = B /\ x = y).
Proof.
  intros.
  pose proof (Insn.bind_eqb_true (A, x) (B, y)).
  rewrite -> (Insn.beq (A, x) (B, y)) in H.
  simpl in H.
  auto.
Qed.

Lemma nbeq : forall A B x y,
    ~ Actor.eq A B -> ~ ((Insn.bind_eqb (A,x) (B,y)) = true).
Proof.
  intros.
  unfold Insn.bind_eqb, Insn.bind_eq_dec. simpl.
  destruct (Actor.eq_dec A B) as [pf1 | pf1]; [ | discriminate].
  contradiction.
Qed.

Lemma nbeqeq : forall A x y,
    Insn.bind_eqb (A, x) (A, y) = false ->
    x <> y.
Proof.
  intros.  
  pose proof (Insn.bind_eqb_false (A, x) (A, y)).
  destruct H0.
  specialize (H0 H).
  rewrite -> (Insn.beq (A, x) (A, y)) in H0.
  simpl in H0.
  auto.
Qed.

Lemma beqeq : forall A x y,
    Insn.bind_eqb (A, x) (A, y) = true ->
    x = y.
Proof.
  intros.
  pose proof (Insn.bind_eqb_true (A, x) (A, y)).
  destruct H0.
  specialize (H0 H).
  rewrite -> (Insn.beq (A, x) (A, y)) in H0.
  simpl in H0.
  destruct H0.
  auto.
Qed.  



Lemma stepC_wf_label : forall I Theta ρ l I' Theta' ρ',
  Insn.stepC I Theta ρ l I' Theta' ρ' ->
  Insn.WellFormed I ->
  Label.WellFormed l.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep; inversion 1; subst;
    try constructor;
    match goal with
    | [ H : Insn.WellFormed _ |- _ ] => inversion H; subst; clear H; auto
    end.
Qed.

Lemma stepB_wf_label : forall C Theta ρ l C' Theta' ρ',
  stepB C Theta ρ l C' Theta' ρ' ->
  Choreography.WellFormed C ->
  Label.WellFormed l.
Proof.
  intros ? ? ? ? ? ? ? Hstep;
  induction Hstep; inversion 1; subst;
    try constructor;
    match goal with
    | [ H : Insn.WellFormed _ |- _ ] => inversion H; subst; clear H; auto
    end.
Qed.

Lemma step_wf_label : forall C Theta ρ l C' Theta' ρ',
  step C Theta ρ l C' Theta' ρ' ->
  Choreography.WellFormed C ->
  Label.WellFormed l.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep;
    try (eapply stepB_wf_label; eauto; fail);
    inversion 1; subst;
    try (eapply stepC_wf_label; eauto; fail);
    try constructor;
    try (apply IHHstep; auto; fail).
Qed.
