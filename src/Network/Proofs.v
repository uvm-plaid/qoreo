
From Qoreo.Base Require Var Actor Config ChorEnv.
From Qoreo.Expr Require Expr BaseProofs.
From Qoreo.Choreography Require Choreography.

From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms (* for Proper *).

From Qoreo.Base Require Var Config ChorEnv.
From Qoreo.Expr Require Expr.
From Qoreo.Choreography Require Choreography.
From Qoreo.Network Require Import Network.
From Stdlib Require Import Morphisms (* for Proper *).

Module Label := Choreography.Label.
Module Choreography := Choreography.Choreography.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Stdlib.Structures.Equalities.
Import Actor.Map.Tactics.


Lemma EPP_correct : forall A C P,
    EPP A C P <-> epp A C = Some P.
Proof.
    intros.
    split.
    * intros HEPP. 
      induction HEPP; simpl; auto;
        subst;
        try rewrite IHHEPP;
        Actor.simplify.
      destruct I; simpl in *;
        Actor.simplify.
    * revert A P.
      induction C as [ | I C]; intros A P Hepp.
      { 
        simpl in *.
        inversion Hepp; subst; clear Hepp.
        constructor.
      }
      simpl in Hepp.
      destruct (epp A C) eqn:IH.
      2:{
        destruct I; Actor.simplify; try rewrite IH in Hepp.
      }
      destruct I
        as [B1 e B2 x | B1 x1 B2 x2 | B x e | B x e | B x1 x2 e];
        Actor.simplify;
        inversion Hepp; subst; clear Hepp;
          constructor; auto;
        simpl; Actor.simplify.
Qed.

Lemma eppI_disjoint : forall D I,
  ~ Actor.FSet.In D (Choreography.Insn.actors I) ->
  eppI D I = [].
Proof.
  intros D I Hin; destruct I; auto; simpl in *; Actor.simplify.
Qed.


Lemma EPP_cons : forall A I C PA,
  Choreography.Insn.WellFormed I ->
  EPP A (I :: C) PA <->
  exists PA', PA = eppI A I ++ PA' /\ EPP A C PA'.
Proof.
  intros A I C PA HI. split.
  * intros  HEPPA.
    inversion HEPPA; subst; clear HEPPA;
    simpl; Actor.simplify; simpl;
    try (eexists; split; eauto; fail).
    rewrite eppI_disjoint; auto. simpl.
    eexists. split; eauto.
  * intros [PA' [? HEPPA]]; subst.
    destruct (Actor.Map.FSetProofs.in_dec A (Choreography.Insn.actors I))
      as [Hin | Hin].
    2:{
      rewrite eppI_disjoint; auto.
      simpl.
      apply EPP_disjoint; auto.
    }
    inversion HI; subst; clear HI; simpl in *;
      Actor.simplify; simpl;
      try(constructor; auto; fail).
    destruct Hin; subst; try contradiction.
    destruct Hin; subst; try contradiction.
Qed.


Lemma EPP_N_eq : forall N1 N2 C,
  Actor.Map.Equal N1 N2 ->
  EPP_N C N1 ->
  EPP_N C N2.
Proof.
  intros N1 N2 C Heq H1. revert N2 Heq.
  induction H1; intros N2 Heq.
  * apply EPP_N_empty.
    rewrite <- Heq; auto.
  * rewrite Heq in *.
    eapply EPP_N_add; eauto.
    apply IHEPP_N.
    Actor.simplify.
Qed.

Global Instance EPP_N_Proper :
  Proper (eq ==> Actor.Map.Equal ==> iff) EPP_N.
Proof.
  intros ? C ? N1 N2 HN; subst.
  split; intros;
    eapply EPP_N_eq; eauto.
  symmetry; auto.
Qed.

Lemma EPP_N_spec : forall C N,
  EPP_N C N <->
  forall D PD, Actor.Map.MapsTo D PD N -> EPP D C PD.
Proof.
  intros C N.
  split; intros H.
  * induction H.
    { intros D PD Hmapsto.
      apply H in Hmapsto. contradiction.
    }
    intros D PD Hmapsto.
    compare D A.
    { (* D = A *)
      replace PD with PA; auto.
      {
        Actor.solve. congruence.
      }
    }
    { (* D <> A *)
      apply IHEPP_N.
      Actor.simplify.
    }

  * induction N using Actor.Map.Properties.map_induction.
    { apply EPP_N_empty; auto. }
    rename x into A, e into PA.
    Actor.simplify.
    apply (EPP_N_add C A PA).
    { Actor.simplify. }
    { apply H. Actor.simplify. }

    Actor.simplify.
    rewrite Actor.Map.Proofs.remove_not_in; auto.
    apply IHN1; auto.
    {
      intros D PD Hmaps.
      apply H.
      Actor.simplify.
      compare A D.
      {
        exfalso. Actor.solve.
      }
      right. split; auto.
    }
Qed.

Lemma EPP_disjoint_inversion : forall A I C P,
  EPP A (I :: C) P ->
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A C P.
Proof.
  intros A I C P HP Hin.
  inversion HP; subst; clear HP;
  simpl in Hin; Actor.simplify.
Qed.


Lemma EPP_N_cons : forall I C N ,
  EPP_N (I :: C) N <->
  (forall A PA,
    Actor.FSet.In A (Choreography.Insn.actors I) ->
    Actor.Map.MapsTo A PA N ->
    EPP A (I :: C) PA
  ) /\
  EPP_N C (Actor.Map.setminus (Choreography.Insn.actors I) N).
Proof.
  intros I C N.
  split.
  * intros HEPP_N.
    rewrite EPP_N_spec in HEPP_N.
    split.
    + intros A PA Hin Hmapsto.
      apply HEPP_N; auto.
    + apply EPP_N_spec.
      intros D PD Hmapsto.
      Actor.simplify.
      eapply EPP_disjoint_inversion; eauto.
  * intros [HA HC].
    rewrite EPP_N_spec in *.
    intros D PD Hmapsto.
    destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I))
      as [Hin | Hin].
    + apply HA; auto.
    + apply EPP_disjoint; auto.
      apply HC; auto.
      Actor.simplify.
Qed.

Require Import Stdlib.Program.Equality.


Lemma bind_eqb_equiv : forall p1 p2,
  Choreography.Insn.bind_eqb p1 p2 =
    if Actor.eq_dec (fst p1) (fst p2)
    then if Var.eq_dec (snd p1) (snd p2)
    then true
    else false
    else false.
Proof.
  intros [A x] [B y].
  unfold Choreography.Insn.bind_eqb, Choreography.Insn.bind_eq_dec; simpl.
  Actor.simplify.
  Var.simplify.
Qed.
#[global] Hint Rewrite bind_eqb_equiv : var_db.

Lemma EPP_subst_neq : forall C A P B x v,
    A <> B ->
    EPP A C P ->
    EPP A (Choreography.subst B x v C) P.
Proof.
  induction C as [ | I C];
    intros ? ? ? ? ? Hneq H.
  { inversion H; subst; constructor. }
  inversion H; subst; clear H; simpl;
    try (
    autorewrite with var_db;
    repeat reduce_eq_dec;
    repeat Var.Map.Tactics.reduce_eq_dec;
    simpl;
    constructor; auto; fail).

  apply EPP_disjoint.
  { Actor.simplify. }
  destruct (Choreography.Insn.rebound_in B x I) eqn:HI; auto.
Qed.

Lemma EPP_subst_neq_bwd : forall C A P B x v,
    A <> B ->
    EPP A (Choreography.subst B x v C) P ->
    EPP A C P.
Proof.
  intros C A P B x v Hneq.
  revert P.
  induction C as [ | I C]; 
    intros P Hepp; simpl; auto.
  assert (Hdec : Actor.FSet.In A (Choreography.Insn.actors I) 
        \/ ~ Actor.FSet.In A (Choreography.Insn.actors I)).
  {
    destruct I; simpl; Var.simplify.
  }
  destruct Hdec as [Hin | Hin].
  2:{
    apply EPP_disjoint; auto.
    simpl in *.
    apply EPP_disjoint_inversion in Hepp.
    destruct (Choreography.Insn.rebound_in B x I) eqn:HB; auto.
    rewrite Choreography.Insn.actors_subst; auto.
  }

  destruct I as 
    [A0 v0 B0 | A0 x0 B0 y0 | A0 x0 v0 | A0 x0 v0 | A0 x0 y0 v0];
    simpl in *.
  * simpl in Hin. autorewrite with actor_db in Hin.
    destruct Hin; subst.
    + (* A = A0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
      Var.simplify; simpl in *; Actor.simplify.
    + (* A = B0 *)
      inversion Hepp; subst; clear Hepp;
      Var.simplify; simpl in *; Actor.simplify;
      constructor; auto.
  * autorewrite with var_db in Hepp; simpl in Hepp.
    autorewrite with actor_db in Hin.
    destruct Hin; subst.
    + (* A = A0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
      Var.simplify.
    + (* A = B0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
      Var.simplify.

  * autorewrite with var_db in Hepp; simpl in *.
    autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * autorewrite with var_db in Hepp; simpl in *.
    autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * autorewrite with var_db in Hepp; simpl in *.
    autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
Qed. 


Lemma subst_not_in_I : forall I A x v,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  Choreography.Insn.subst A x v I = I.
Proof.
  destruct I; intros; simpl in *; Actor.simplify.
Qed.
Lemma rebound_not_in_I : forall I A x,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  Choreography.Insn.rebound_in A x I = false.
Proof.
  destruct I; intros; simpl in *;
    autorewrite with var_db; simpl;
    Actor.simplify.    
Qed.


Lemma EPP_subst_eq : forall A C P x v,
    EPP A C P ->
    EPP A (Choreography.subst A x v C) (Process.subst x v P).
Proof.
  intros ? ? ? ? ? H.
  induction H; subst; simpl;
    try (constructor; fail);
    autorewrite with var_db; simpl;
    Actor.simplify;
    Var.simplify;
    simpl in *; subst;
    try (constructor; auto; fail).

  rewrite subst_not_in_I; auto.
  rewrite rebound_not_in_I; auto.
  apply EPP_disjoint; auto.
Qed.


Lemma EPP_subst_eq_bwd : forall A x v C P',
  EPP A (Choreography.subst A x v C) P' ->
  exists P, EPP A C P /\ P' = Process.subst x v P.
Proof.
  intros A x v C.
  induction C as [ | I C];
    intros P' H;
    simpl in *.
  {
    inversion H; subst.
    exists []. split; auto.
  }
    assert (Hdec : Actor.FSet.In A (Choreography.Insn.actors I) 
        \/ ~ Actor.FSet.In A (Choreography.Insn.actors I)).
  {
    destruct I; simpl; Var.simplify.
  }
  destruct Hdec as [Hin | Hin].
  2:{
    apply EPP_disjoint_inversion in H; auto.
    2:{ rewrite Choreography.Insn.actors_subst; auto. }
    rewrite rebound_not_in_I in H; auto.
    apply IHC in H.
    destruct H as [P [H ?]]; subst.
    exists P; split; auto.
    apply EPP_disjoint; auto.
  }

  destruct I as 
    [A0 v0 B0 y0 | A0 x0 B0 y0 | A0 x0 v0 | A0 x0 v0 | A0 x0 y0 v0];
    simpl in *;
    autorewrite with var_db in *;
    simpl in *.

  * autorewrite with actor_db in Hin.
    inversion H; subst; clear H.

    + (* A = A0 *)
      Actor.simplify.
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.Send v0 B0 :: P0).
      split; auto.
      constructor; auto.

    + (* A = B0 *)
      Actor.simplify.
      Var.Map.Tactics.compare x y0.
      - (* x = y0 *)
        exists (Insn.Receive x A0 :: P).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.
      
      - (* x <> y0 *)
        edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
        exists (Insn.Receive y0 A0 :: P0).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.

    + (* A <> A0 /\ B <> B0 *)
      (* contradicts Hin *)
      simpl in *. Actor.simplify.
      destruct Hin; subst; contradiction.

  * (* EPR *) 
    autorewrite with actor_db in Hin.
    inversion H; subst; clear H.

    + (* A = A0 *)
      Actor.simplify.
      Var.Map.Tactics.compare x x0.
      - (* x = y0 *)
        exists (Insn.EPR x B0 :: P).
        simpl in *. Var.simplify.
        split; auto.
        constructor; auto.

      - (* x <> x0 *)
        edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
        exists (Insn.EPR x0 B0 :: P0).
        simpl in *. Var.simplify.
        split; auto.
        constructor; auto.

    + (* A = B0 *)
      Actor.simplify. simpl in *.
      Var.Map.Tactics.compare x y0.
      - (* x = y0 *)
        exists (Insn.EPR x A0 :: P).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.
      
      - (* x <> y0 *)
        edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
        exists (Insn.EPR y0 A0 :: P0).
        simpl. Var.simplify.
        split; auto.
        constructor; auto.

    + (* A <> A0 /\ B <> B0 *)
      (* contradicts Hin *)
      simpl in *. Actor.simplify.
      destruct Hin; subst; contradiction.

  * (* Let *)
    autorewrite with actor_db in Hin. subst.
    Actor.simplify.
    inversion H; subst; clear H.
    2:{ simpl in *. Actor.simplify. }

    Var.Map.Tactics.compare x x0.
    + (* x = x0 *)
      exists (Insn.Let x v0 :: P).
      simpl. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x <> x0 *)
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.Let x0 v0 :: P0).
      simpl; Var.simplify.
      split; auto.
      constructor; auto.


  * (* LetBang *)
    autorewrite with actor_db in Hin. subst.
    Actor.simplify.
    inversion H; subst; clear H.
    2:{ simpl in *. Actor.simplify. }

    Var.Map.Tactics.compare x x0.
    + (* x = x0 *)
      exists (Insn.LetBang x v0 :: P).
      simpl. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x <> x0 *)
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.LetBang x0 v0 :: P0).
      simpl; Var.simplify.
      split; auto.
      constructor; auto.

  
  * (* LetPair *)
    autorewrite with actor_db in Hin. subst.
    Actor.simplify.
    inversion H; subst; clear H.
    2:{ simpl in *. Actor.simplify. }

    Var.Map.Tactics.compare x x0;
      [ | Var.Map.Tactics.compare x y0 ].
    + (* x = x0 *)
      exists (Insn.LetPair x y0 v0 :: P).
      simpl in *. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x = y0 *)
      exists (Insn.LetPair x0 x v0 :: P).
      simpl in *. Var.simplify.
      split; auto.
      constructor; auto.

    + (* x <> x0 /\ x <> y0 *)
      edestruct (IHC P) as [P0 [H0 ?]]; eauto; subst.
      exists (Insn.LetPair x0 y0 v0 :: P0).
      simpl; Var.simplify.
      split; auto.
      constructor; auto.
Qed.


Lemma EPP_subst_iff : forall C D PD A x v,
    EPP D (Choreography.subst A x v C) PD <->
    (D = A /\ exists PD0,
                EPP D C PD0 
                /\ PD = Process.subst x v PD0)
    \/
    (D <> A /\ EPP D C PD).
Proof.
  intros.
  split; intros H.
  * compare A D.
    + left. split; auto.
      apply EPP_subst_eq_bwd; auto.
    + right. split; auto.
      eapply EPP_subst_neq_bwd; eauto.
  * destruct H as [[? [PD0 [HPD0 ?]]] | [? HPD]]; subst.
    + apply EPP_subst_eq; auto.
    + apply EPP_subst_neq; auto. 
Qed.



Ltac EPP_N_cons :=
  match goal with
  | [H : EPP_N (_ :: _) _ |- _] =>
    rewrite EPP_N_cons in H;
    simpl in H; Actor.simplify
  | [ |- EPP_N (_ :: _) _ ] =>
    eapply EPP_N_cons;
    repeat split; intros; simpl; Actor.simplify
  end.

Lemma EPP_N_subst_neq : forall A x e C N,
  ~ Actor.Map.In A N ->
  EPP_N (Choreography.subst A x e C) N
  <->
  EPP_N C N.
Proof.
  intros.
  repeat rewrite EPP_N_spec.
  apply Modulus.forall_iff. intros D.
  apply Modulus.forall_iff. intros PD.
  apply Modulus.forall_iff. intros Hmapsto.
  rewrite EPP_subst_iff.
  assert (D <> A).
  {
    inversion 1; subst.
    apply H. exists PD; auto.
  }
  intuition.
Qed.

Lemma chor_epr_eq : forall T2 T1 T1' A B cfg cfg' q1 q2,
  ChorEnv.epr A B T1 cfg = (q1, q2, T1', cfg') ->
  ChorEnv.Equal T1 T2 ->
  exists T2', ChorEnv.epr A B T2 cfg = (q1, q2, T2', cfg') /\ ChorEnv.Equal T2' T1'.
Proof.
  intros ? ? ? ? ? ? ? ? ? Hepr Heq.
  unfold ChorEnv.epr.
  unfold ChorEnv.epr in Hepr.
  destruct (Config.epr_cfg cfg) as [[q1' q2'] cfg''] eqn:Hcfg.
  inversion Hepr; subst; clear Hepr.
  eexists.
  
  split.
  + reflexivity.
  + rewrite Heq. reflexivity.
Qed.

(* TODO: move to Choreography.v *)
Lemma epr_Proper : Proper (eq ==> eq ==> ChorEnv.Equal ==> eq ==> RelationPairs.RelProd (RelationPairs.RelProd eq ChorEnv.Equal) eq) ChorEnv.epr.
Proof.
  intros ? A ? ? B ? T1 T2 HT ? cfg ?; subst.
  unfold ChorEnv.epr.
  split; split; simpl; unfold RelationPairs.RelCompFun; simpl; auto.
  rewrite HT. reflexivity.
Qed.

Lemma chor_step_Proper' : forall C Θ1 cfg l C' Θ1' cfg',
  Choreography.step C Θ1 cfg l C' Θ1' cfg' ->
  forall Θ2 Θ2',
    ChorEnv.Equal Θ1 Θ2 ->
    ChorEnv.Equal Θ1' Θ2' ->
    Choreography.step C Θ2 cfg l C' Θ2' cfg'.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep; intros Θ2 Θ2' Heq Heq';
    try rewrite Heq in *;
    try rewrite Heq' in *;
    try (econstructor; eauto; fail).
  (* only EPR cases left *)
  * subst.

    apply (chor_epr_eq Θ2) in H; auto.
    destruct H as [T0' [Heq'' H]].

    apply (Choreography.EPRB q1 q2 T0'); auto.
    { rewrite H; auto. }

  * apply (chor_epr_eq Θ2) in H; auto.
    destruct H as [T0' [Heq'' H]].

    apply (Choreography.EPRB' q1 q2 T0'); auto.
    {
      rewrite H; auto.
    }
Qed.

Global Instance chor_step_Proper : Proper (eq ==> ChorEnv.Equal ==> eq ==> eq ==> eq ==> ChorEnv.Equal ==> eq ==> iff) (Choreography.step).
Proof.
  intros ? C ? Θ1 Θ2 HΘ ? cfg ? ? l ? ? C' ? Θ1' Θ2' HΘ' ? cfg' ?; subst.
  split; intros Hstep.
  * eapply chor_step_Proper'; eauto.
  * eapply chor_step_Proper'; eauto. symmetry; auto. symmetry; auto.
Qed.

Lemma EPP_N_weakening : forall C N N',
  (forall A PA, Actor.Map.MapsTo A PA N' -> Actor.Map.MapsTo A PA N) ->
  EPP_N C N ->
  EPP_N C N'.
Proof.
  intros C N N' Hsub HN.
  rewrite EPP_N_spec in *.
  intros D PD HD.
  apply HN.
  auto.
Qed.

Lemma EPP_N_remove : forall C A N,
  EPP_N C N -> 
  EPP_N C (Actor.Map.remove A N).
Proof.
  intros.
  rewrite EPP_N_spec in *.
  intros D PD Hmapsto.
  Actor.simplify.
Qed.


Require Import Setoid.

(** uncons *)

(* TODO: move to FSet module *)
Definition actor_map {T} (f : Actor.t -> option (option T)) (X : Actor.FSet.t) N0 : Actor.Map.t T :=
  Actor.FSet.fold (fun A N => match f A with
                              | Some (Some v) => Actor.Map.add A v N
                              | Some None => Actor.Map.remove A N
                              | None => N
                              end)
                  X N0.
Definition uncons (N : Network.t) A : option (option Process.t):=
  match Actor.Map.find A N with
  | Some (_ :: P) => Some (Some P)
  | Some [] => None
  | None => None
  end.
Definition unconsN N X := actor_map (uncons N) X N.

Lemma find_fold_left_neq' : forall (ls : list Actor.t) A T (f : Actor.t -> option (option T)) (N : Actor.Map.t T) (g : Actor.Map.t T -> Actor.t -> Actor.Map.t T),
  ~ SetoidList.InA eq A ls ->
  g = (fun N A => match f A with
                              | Some (Some v) => Actor.Map.add A v N
                              | Some None => Actor.Map.remove A N
                              | None => N
                              end) ->
  Actor.Map.find A (List.fold_left g ls N : Actor.Map.t T) = Actor.Map.find A N.
Proof.
  intros ls; induction ls as [ | B ls];
    intros A T f N g Hin Hg.
  { simpl. auto. }
  simpl.
  assert (A <> B).
  { inversion 1; subst. apply Hin. auto. }
  assert (Hin' : ~ SetoidList.InA eq A ls).
  { intros Hin'. apply Hin. auto. }
  erewrite IHls; eauto.
  subst.
  destruct (f B) as [[|]|]; Actor.simplify; auto.
Qed.



Lemma find_fold_left_eq' : forall (ls : list Actor.t) A T (f : Actor.t -> option (option T)) (N : Actor.Map.t T) (g : Actor.Map.t T -> Actor.t -> Actor.Map.t T),
  SetoidList.NoDupA eq ls ->
  SetoidList.InA eq A ls ->
  g = (fun N A => match f A with
                              | Some (Some v) => Actor.Map.add A v N
                              | Some None => Actor.Map.remove A N
                              | None => N
                              end) ->
  Actor.Map.find A (List.fold_left g ls N) = match f A with
                                             | Some o => o
                                             | None => Actor.Map.find A N
                                             end.
Proof.
  intros ls; induction ls as [ | B ls];
    intros A T f N g Hdup Hin Hg.
  { exfalso. inversion Hin. }
  simpl.
  inversion Hdup; subst; clear Hdup.

  compare A B.
  { (* A = B *)
    erewrite find_fold_left_neq'; eauto.
    destruct (f A) as [[|]|] eqn:HB; 
      Actor.simplify.
  }

  (* A <> B *)
  inversion Hin; subst; clear Hin; try contradiction.
  erewrite IHls; eauto.
  destruct (f A) eqn:HA; auto.
  destruct (f B) as [[|]|] eqn:HB; auto;
    Actor.simplify.
Qed.

(*
Definition uncons A (N : Network.t) :=
  match Actor.Map.find A N with
  | Some (_ :: P) => Actor.Map.add A P N
  | Some [] => N
  | _ => Actor.Map.remove A N
  end.

Lemma uncons_neq : forall A B PB N,
  A <> B ->
  Actor.Map.MapsTo B PB (uncons A N) <-> Actor.Map.MapsTo B PB N.
Proof.
  intros A B PB N Hneq.
  unfold uncons.
  destruct (Actor.Map.find A N) as [[ | IA PA] | ] eqn:Hfind;
    Actor.simplify.
Qed.
  *)


Lemma find_actor_map_nin : forall T (X : Actor.FSet.t) A (f : Actor.t -> option (option T)) N,
  ~ Actor.FSet.In A X ->
  Actor.Map.find A (actor_map f X N) = Actor.Map.find A N.
Proof.
  intros.
  unfold actor_map.
  rewrite Actor.FSet.fold_1.
  erewrite find_fold_left_neq'; eauto.
Qed.
Lemma find_actor_map_in : forall T (X : Actor.FSet.t) A (f : Actor.t -> option (option T)) N,
  Actor.FSet.In A X ->
  Actor.Map.find A (actor_map f X N)
    = match f A with
      | Some o => o
      | None => Actor.Map.find A N
      end.
Proof.
  intros.
  unfold actor_map.
  rewrite Actor.FSet.fold_1.
  erewrite find_fold_left_eq'; eauto.
  apply Actor.FSet.elements_3w.
Qed.

Lemma find_actor_map : forall T (X : Actor.FSet.t) A (f : Actor.t -> option (option T)) N,
  Actor.Map.find A (actor_map f X N)
    = if Actor.Map.FSetProofs.in_dec A X
      then match f A with
          | Some o => o
          | None => Actor.Map.find A N
          end
      else Actor.Map.find A N.
Proof.
  intros.
  destruct (Actor.Map.FSetProofs.in_dec A X).
  + apply find_actor_map_in; auto.
  + apply find_actor_map_nin; auto.
Qed.
Hint Rewrite find_actor_map : actor_db.

(*  
Lemma actor_map_mapsto_neq : forall T (X : Actor.FSet.t) A PA (f : Actor.t -> option (option T)) N,
  ~ Actor.FSet.In A X ->
  Actor.Map.MapsTo A PA (actor_map f X N)
  <->
  Actor.Map.MapsTo A PA N.
Proof.
  intros T X A PA f N Hin. unfold actor_map. rewrite Actor.FSet.fold_1.
  remember (Actor.FSet.elements X) as ls eqn:Hls.
  assert (Hls' : SetoidList.equivlistA eq ls (Actor.FSet.elements X)).
  { rewrite Hls. reflexivity. }
  assert (Hdup : SetoidList.NoDupA eq ls).
  { rewrite Hls. apply Actor.FSet.elements_3w. }
  clear Hls.
  revert X Hls' Hdup N Hin.
  induction ls as [ | B ls]; intros X Hls Hdup N Hin.
  { reflexivity. }
  simpl.

  compare A B.
  {
    exfalso.
    apply Hin.
    apply Actor.FSet.elements_2.
    rewrite <- Hls.
    constructor; auto.
  }

  rewrite (IHls (Actor.FSet.remove B X)).
  2:{
    erewrite Actor.Map.FSetProofs.elements_cons_remove; eauto.
    { reflexivity. }
    { inversion Hdup; auto. }
    { symmetry. auto. }
  }
  2:{ inversion Hdup; auto. }
  2:{ Actor.simplify. }
  destruct (f B) as [[v | ] |] eqn:HB.
  { Actor.simplify. intuition. }
  { Actor.simplify. intuition. }
  { reflexivity. }
Qed.
*)

Lemma fold_uncons_mapsto_neq : forall X A PA N,
  ~ Actor.FSet.In A X ->
  Actor.Map.MapsTo A PA (unconsN N X) <->
  Actor.Map.MapsTo A PA N.
Proof.
  intros X A PA N Hin.
  unfold unconsN.
  split; intros Hmapsto; Actor.reflect_find.
  * destruct (Actor.Map.FSetProofs.in_dec A X); auto; try contradiction.
  * destruct (Actor.Map.FSetProofs.in_dec A X); auto; try contradiction.
Qed.


Lemma find_fold_uncons_neq : forall X A N,
  ~ Actor.FSet.In A X ->
  Actor.Map.find A (unconsN N X) = Actor.Map.find A N.
Proof.
  intros.
  apply find_actor_map_nin; auto.
Qed.

Instance fold_left_Proper : forall f,
  Proper (Actor.Map.Equal ==> eq ==> Actor.Map.Equal) f ->
  Proper (SetoidList.eqlistA (@eq Actor.t) ==> Actor.Map.Equal ==> @Actor.Map.Equal Actor.t) (List.fold_left f).
Proof.
  intros f Hf ls1 ls2 Hls M1 M2 HM.
  apply Actor.Map.FSetProofs.foldProper''; auto.
Qed.

Instance unconsProper : Proper (Actor.Map.Equal ==> eq ==> eq) uncons.
Proof.
  intros M1 M2 HM ? A ?; subst.
  unfold uncons.
  rewrite HM.
  destruct (Actor.Map.find A M2) as [ [ | P] | ]; auto.
Qed.

Instance actor_map_Proper : forall T f, Proper (Actor.FSet.Equal ==> Actor.Map.Equal ==> Actor.Map.Equal) (@actor_map T f).
Proof.
  intros T f X1 X2 HX M1 M2 HM; subst.
  unfold actor_map.
  apply Actor.Map.FSetProofs.foldProper; auto.
  clear X1 X2 HX M1 M2 HM.
  intros ? A ? N1 N2 HN; subst.
  destruct (f A) as [[|]|]; auto;
    rewrite HN;
    reflexivity.
Qed.


Lemma fold_uncons_mapsto_eq : forall N A PA X,
  Actor.FSet.In A X ->
  Actor.Map.MapsTo A PA (unconsN N X) <->
  (PA = [] /\ Actor.Map.MapsTo A [] N) \/ exists I, Actor.Map.MapsTo A (I :: PA) N.
Proof.
  intros N A PA X Hin.
  repeat rewrite Actor.Map.Properties.F.find_mapsto_iff.
  unfold unconsN.
  autorewrite with actor_db.
  destruct (Actor.Map.FSetProofs.in_dec A X); try contradiction.
  unfold uncons.
  unfold Process.t.
  destruct (Actor.Map.find A N) as [[ | I0 PA0] | ] eqn:HA;
    try unfold Process.t in HA.
  * rewrite HA.
    split; [inversion 1; subst | intros [[? Hfind] | [I0' HI0']]]; subst; auto.
    Actor.reflect_find.
    discriminate.
  * rewrite HA.
    split; [inversion 1; subst | intros [[? Hfind] | [I0' HI0']]]; subst; auto;
      try discriminate.
    + right. exists I0. Actor.solve.
    + Actor.reflect_find. congruence.

  * rewrite HA.
    split; [inversion 1; subst | intros [[? Hfind] | [I0' HI0']]]; subst; auto;
      try discriminate.
    Actor.reflect_find. discriminate.
Qed.

Lemma fold_uncons_find_iff : forall X A N,
  Actor.Map.find A (unconsN N X)
  =
  if Actor.Map.FSetProofs.in_dec A X
  then match Actor.Map.find A N with
       | Some (_ :: PA) => Some PA
       | Some [] => Some []
       | None => None
       end
  else Actor.Map.find A N.
Proof.
  intros.
  unfold unconsN.
  autorewrite with actor_db.
  destruct (Actor.Map.FSetProofs.in_dec A X); auto.
  unfold uncons.
  destruct (Actor.Map.find A N) as [[ | IA PA]|]; auto.
Qed.

#[global] Hint Rewrite fold_uncons_find_iff : actor_db.
  

Lemma EPP_N_cons_inversion : forall I C N,
  EPP_N (I :: C) N ->
  EPP_N C (unconsN N (Choreography.Insn.actors I)).
Proof.
  intros I C N HN.
  rewrite EPP_N_spec in *.
  intros D PD HD.
  Actor.simplify.
  destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I)) as [Hin | Hin].
  * rewrite fold_uncons_mapsto_eq in HD; auto.
    destruct HD as [[? HD] | [I0 HD]]; subst.
    {
      exfalso. apply HN in HD.
      inversion HD; subst; clear HD.
      contradiction.
    }
    apply HN in HD.
    inversion HD; subst; clear HD; auto.
    contradiction.
  * rewrite fold_uncons_mapsto_neq in HD; auto.
    apply HN in HD.
    eapply EPP_disjoint_inversion in HD; auto.
Qed.


Lemma completeness_local : forall PA (refs : Var.Map.t nat) cfg PA' refs' cfg',
  Process.step PA refs cfg PA' refs' cfg' -> 
  forall A N C (Θ : ChorEnv.t nat) Θ',
  EPP_N C N ->
  Choreography.WellFormed C ->
  Actor.Map.MapsTo A PA N ->
  (*Actor.Map.MapsTo A refs Θ ->*)
  Var.Map.Equal refs (ChorEnv.find A Θ) ->
  ChorEnv.Equal Θ' (Actor.Map.add A refs' Θ) ->
  
  exists C',
    Choreography.step C Θ cfg (Label.Loc A) C' Θ' cfg'
    /\
    EPP_N C' (Actor.Map.add A PA' N).
Proof.
  intros ? ? ? ? ? ? Hstep A N C Θ Θ' HEPP_N HWF Hmapsto Hrefs HΘ'.
  rewrite EPP_N_spec in HEPP_N.
  apply HEPP_N in Hmapsto.
  rewrite <- EPP_N_spec in HEPP_N.
  revert N HEPP_N.
  revert refs cfg PA' refs' cfg' Hstep Hrefs HΘ' HWF.
  induction Hmapsto;
    intros refs cfg PA' refs' cfg' Hstep Hrefs HΘ' HWF N HEPP_N;
    subst;
    try (inversion Hstep; fail).

  * (* SendC *)
    inversion Hstep; subst; clear Hstep.
    Var.simplify.
    exists (Choreography.Insn.Send A e' B y :: C).
    split.
    { econstructor; eauto. }
    { 
      eapply (EPP_N_add _ A (Insn.Send e' B :: P)).
      { Actor.simplify. }
      { constructor; auto. }
      {
        Actor.simplify.

        EPP_N_cons.
        EPP_N_cons.
        {
          simpl in *. Actor.simplify.
          match goal with
          | [ H : Actor.Map.M.MapsTo _ _ _ |- _ ] =>
            rename H into Hmapsto'
          end.
          apply H in Hmapsto'.
          2:{ Actor.simplify. }
          inversion Hmapsto'; subst; try contradiction.
          2:{ exfalso. simpl in *. Actor.simplify. }
          constructor; auto.
        }
      }
    }

  * (* Let *)
    inversion Hstep; subst; clear Hstep.
    + (* LetC *)
      Var.simplify.
      exists (Choreography.Insn.Let A x e' :: C).
      split.
      { econstructor; eauto. }
      {
        EPP_N_cons.
        EPP_N_cons.
        destruct H2 as [[? ?] | [? ?]]; try contradiction;
            subst.
        constructor; auto.
        apply EPP_disjoint; simpl; Actor.simplify.
        eapply EPP_disjoint_inversion.
        { apply H; auto. }
        { simpl; Actor.simplify. }
      }

    + (* LetB *)
      exists (Choreography.subst A x e C).
      split.
      {
        assert (Heq' : ChorEnv.Equal Θ' Θ).
        {
          rewrite HΘ'.
          intros D.
          ChorEnv.simplify.
        }
        rewrite Heq'.
        eapply Choreography.LetB; eauto.
        reflexivity.
      }
      {
        eapply (EPP_N_add _ A).
        { Actor.simplify. }
        { apply EPP_subst_eq; auto. }
        {
          Actor.simplify.

          rewrite EPP_N_subst_neq; auto.
          2:{ Actor.simplify. }
          EPP_N_cons; auto.
        }
      }


  * (* LetBang *)
    inversion Hstep; subst; clear Hstep.
    + (* LetBangC *)
      Var.simplify.
      exists (Choreography.Insn.LetBang A x e' :: C).
      split.
      { econstructor; eauto. }
      {
        EPP_N_cons.
        EPP_N_cons.
        destruct H2 as [[? ?] | [? ?]]; try contradiction;
            subst.
        constructor; auto.
        apply EPP_disjoint; simpl; Actor.simplify.
        eapply EPP_disjoint_inversion.
        apply H; auto.
        simpl; Actor.simplify.
      }

    + (* LetBangB *)
      exists (Choreography.subst A x e0 C).
      split.
      {
        
        assert (Heq' : ChorEnv.Equal Θ' Θ).
        {
          rewrite HΘ'.
          ChorEnv.solve.
        }
        rewrite Heq'.
        eapply Choreography.LetBangB; eauto.
        reflexivity.
      }
      {
        eapply (EPP_N_add _ A).
        { Actor.simplify. }
        { apply EPP_subst_eq; auto. }
        {
          Actor.simplify.
          rewrite EPP_N_subst_neq; auto.
          2:{ Actor.simplify. }
          EPP_N_cons; auto.
        }
      }

  * (* LetPair *) 
    inversion Hstep; subst; clear Hstep.
    + (* LetPairC *)
      Var.simplify.
      exists (Choreography.Insn.LetPair A x1 x2 e' :: C).
      split.
      { econstructor; eauto. }
      {
        EPP_N_cons.
        EPP_N_cons.
        simpl in *. Actor.simplify. subst.
        destruct H2 as [[? ?] | [? ?]]; try contradiction;
            subst.
        constructor; auto.
      }

    + (* LetPairB *)
      eexists.
      split.
      { 
        assert (Heq' : ChorEnv.Equal Θ' Θ).
        {
          rewrite HΘ'.
          ChorEnv.solve.
        }
        rewrite Heq'.
        eapply Choreography.LetPairB; eauto.
        reflexivity.
      }
      {
        eapply (EPP_N_add _ A).
        { Actor.simplify. }
        {
          apply EPP_subst_eq.
          apply EPP_subst_eq.
          auto.
        }
        {
          EPP_N_cons; auto.
          Actor.simplify.
          rewrite EPP_N_subst_neq; auto.
          2:{ Actor.simplify. }
          rewrite EPP_N_subst_neq; auto.
          { Actor.simplify. }
        }
      }

  * (* Inductive case *)

    inversion HWF; subst; clear HWF.

    set (HEPP_N_uncons := EPP_N_cons_inversion _ _ _ HEPP_N).
    eapply IHHmapsto in HEPP_N_uncons; eauto.
    destruct HEPP_N_uncons as [C' [Hstep' HEPP_N_uncons]].
    exists (I :: C').
    split.
    + apply Choreography.Delay; auto.
      simpl.
      intros B. Actor.simplify.
      intros [? Hin]; subst.
      contradiction.
    + rewrite EPP_N_spec.
      intros D PD HD.
      Actor.simplify.
      destruct HD as [[? ?] | [? HD]]; subst.
      { (* A = D *)
        apply EPP_disjoint; auto.
        rewrite EPP_N_spec in HEPP_N_uncons.
        apply HEPP_N_uncons.
        Actor.simplify.
      }
      destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I))
        as [HinD | HinD].
      2:{ (* D not in I *)
        apply EPP_disjoint; auto.
        rewrite EPP_N_spec in HEPP_N_uncons.
        apply HEPP_N_uncons.
        Actor.simplify.
        right. split; auto.
        rewrite fold_uncons_mapsto_neq; auto.
      }
      { (* D in I but not equal to A *)
        assert (HD' : exists PD', PD = eppI D I ++ PD' /\ EPP D C PD').
        {
          rewrite EPP_N_spec in HEPP_N.
          rewrite <- EPP_cons; auto.
        }
        destruct HD' as [PD' [? HD']]; subst.
        rewrite EPP_cons; auto.
        exists PD'. split; auto.
        rewrite EPP_N_spec in HEPP_N_uncons.
        apply HEPP_N_uncons.
        Actor.simplify. right. split; auto.
        rewrite fold_uncons_mapsto_eq; auto.
        right.
        destruct I; simpl in *; Actor.simplify; simpl in *; eexists; eauto.
        all: (destruct HinD; subst; contradiction).
      }

    Unshelve.
    all: (subst; try contradiction).
    exact (Insn.Send t0 t).
    exact (Insn.EPR t0 t).
Qed.


Lemma fold_uncons_in_iff : forall A X N,
  Actor.Map.In A (unconsN N X)
  <->
  Actor.Map.In A N.
Proof.
  intros A X N.
  split; intros Hin.
  * Actor.reflect_find.
    destruct (Actor.Map.FSetProofs.in_dec A X) as [HinX | HinX].
    + destruct (Actor.Map.find A N); discriminate.
    + rewrite Hin. discriminate.

  * Actor.reflect_find. 
    destruct (Actor.Map.FSetProofs.in_dec A X) as [HinX | HinX].
    + destruct v; discriminate.
    + discriminate. 
Qed.
Hint Rewrite fold_uncons_in_iff : actor_db.


Lemma completeness_send : forall C N refs cfg A v B N' refs' cfg',
  Choreography.WellFormed C ->
  Network.step N refs cfg (Label.Send A v B) N' refs' cfg' ->
  EPP_N C N ->
  (forall D, Actor.FSet.In D (Choreography.actors C) -> Actor.Map.In D N) ->
  exists C',
    Choreography.step C refs cfg (Label.Send A v B) C' refs' cfg'  /\
    EPP_N C' N' /\
    (forall D, Actor.FSet.In D (Choreography.actors C') -> Actor.Map.In D N').
Proof.
  induction C as [ | I C]; intros N refs cfg A v B N' refs' cfg' HWF Hstep HEPP_N Hdomain.
  {
    exfalso.
    (* absurd *)
    rewrite EPP_N_spec in HEPP_N.
    inversion Hstep; subst; clear Hstep.
    rename H3 into HA.
    apply HEPP_N in HA.
    inversion HA.
  }
  inversion HWF; subst; clear HWF.
  inversion Hstep; subst; clear Hstep.
  rename H1 into WFI.
  rename H2 into WFC'.
  rename H5 into HA.
  rename H6 into HB.
  rename H10 into HN'.
  rename H14 into Hrefs.

  (*
  intros N refs cfg A v B N' refs' cfg' C HWF H.
  inversion H; subst; clear H.
  generalize dependent B. generalize dependent A.
  generalize dependent refs.
  (*generalize dependent v.*)
  revert N PA PB refs'.
  induction HWF;
    intros N (*refs' cfg'*) PA PB  refs' refs Hrefs (*y*) (*v Hv*) A B Hneq HA HB HN' HEPP_N.
  {
    exfalso.
    (* absurd *)
    rewrite EPP_N_spec in HEPP_N.
    apply HEPP_N in HA.
    inversion HA.
  }
    *)

  assert (HI : I = Choreography.Insn.Send A (Expr.Bang v) B y
    \/ (~ Actor.FSet.In A (Choreography.Insn.actors I)
     /\ ~ Actor.FSet.In B (Choreography.Insn.actors I))).
  {
    EPP_N_cons.
    destruct (Actor.Map.FSetProofs.in_dec A (Choreography.Insn.actors I)) as [HinA | HinA];
    destruct (Actor.Map.FSetProofs.in_dec B (Choreography.Insn.actors I)) as [HinB | HinB].
    2:{
      (* contradiction *)
      set (HinA' := H _ _ HinA HA).
      inversion HinA'; subst; clear HinA'; try contradiction.
      simpl in *. Actor.simplify.
    }
    2:{
      (* contradiction *)
      set (HinB' := H _ _ HinB HB).
      inversion HinB'; subst; clear HinB'; try contradiction.
      simpl in *. Actor.simplify.
    }
    {
      left.
      set (HinA' := H _ _ HinA HA).
      set (HinB' := H _ _ HinB HB).
      inversion HinA'; subst; clear HinA'; try contradiction.
      inversion HinB'; subst; clear HinB'; try contradiction.
      simpl in *. Actor.simplify.
    }
    { auto. }
  }
  destruct HI as [? | [HinA HinB]]; subst.
  + (* I = Send *)

    exists (Choreography.subst B y v C).
    split.
    {
      constructor; auto. symmetry; auto.
    }

    apply EPP_N_cons_inversion in HEPP_N.
    rewrite EPP_N_spec in HEPP_N.

    split.
    2:{
      intros D HD.
      rewrite HN'.
      Actor.simplify.
      right. right.
      eapply Hdomain; eauto.
      simpl.
      Actor.simplify.
    }

    rewrite HN'; clear N' HN'.

    apply EPP_N_spec.
    intros D PD HD.
    Actor.simplify.
    destruct HD as [[? ?] | [? [[? ?] | [? HD]]]]; subst.
    { apply EPP_subst_neq; auto. apply HEPP_N.
      Actor.reflect_find. simpl. unfold Process.t in *.
      match goal with
      | [ |- context[Actor.Map.FSetProofs.in_dec ?A ?X]] =>
        let HA := fresh "H" in
        destruct (Actor.Map.FSetProofs.in_dec A X) as [HA | HA]
      end.
      2:{ Actor.simplify. }
      rewrite HA; auto.
    }
    {
      apply EPP_subst_eq; auto.
      apply HEPP_N. simpl.
      rewrite fold_uncons_mapsto_eq; auto.
      2:{ Actor.simplify. }
      right.
      eexists; eauto. 
    }
    {
      apply EPP_subst_neq; auto.
      apply HEPP_N. simpl.
      rewrite fold_uncons_mapsto_neq; auto.
      { Actor.simplify. }
    }

  + (* inductive case *) 
    assert (HEPP_N_cons : forall D PD,
      Actor.FSet.In D (Choreography.Insn.actors I) ->
      Actor.Map.MapsTo D PD N ->
      EPP D (I :: C) PD).
    { EPP_N_cons. }
    apply EPP_N_cons_inversion in HEPP_N.
    eapply IHC in WFC'; eauto.
    2:{
      econstructor; eauto.
      { apply fold_uncons_mapsto_neq; eauto. }
      { apply fold_uncons_mapsto_neq; eauto. }
      reflexivity.
    }
    2:{
      intros D HD.
      Actor.simplify.
      apply Hdomain. simpl.
      Actor.simplify.
    }
    destruct WFC' as [C' [IHstep [IHEPP_N IHdomain]]].

    exists (I :: C').
    split.
    { constructor; eauto.
      {
        intros D. simpl. Actor.simplify.
        intuition; subst; try contradiction.
      }
    }
    split.
    2:{
      intros D HD.
      rewrite HN'.
      simpl in HD.
      Actor.simplify.
      destruct HD as [HD | HD]; subst.
      {
        (* D in I *)
        right. right.
        eapply Hdomain. simpl.
        Actor.simplify.
      }
      {
        apply IHdomain in HD.
        Actor.simplify.
      }
    }


    rewrite HN'; clear N' HN'.
    rewrite EPP_N_spec in *.
    intros D PD HD.
    Actor.simplify.
    destruct HD as [[? ?] | [? [[? ?] | [? HD]]]]; subst; try contradiction.
    {
      apply EPP_disjoint; auto.
      apply IHEPP_N. Actor.simplify.
    }
    {
      apply EPP_disjoint; auto.
      apply IHEPP_N. Actor.simplify.
    }
    destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I)) as [Hin | Hin].
    2:{ 
      apply EPP_disjoint; auto.
      apply IHEPP_N. Actor.simplify.
      right. split; auto.
      right. split; auto.
      apply fold_uncons_mapsto_neq; auto.
    }

      set (HD' := HEPP_N_cons D PD Hin HD).
      apply EPP_cons in HD'; auto.
      destruct HD' as [PD' [? HD']]; subst.
      apply EPP_cons; auto.
      exists PD'. split; auto.
      apply IHEPP_N. Actor.simplify.
      right. split; auto.
      right. split; auto.
      assert (HI : exists I', eppI D I = [I']).
      (* could make this a lemma *)
      { destruct I;
          simpl in *; autorewrite with actor_db in *;
          try (destruct Hin; subst; Actor.simplify;
                eexists; eauto; fail).
      }
      destruct HI as [I' HI].
      rewrite HI in HD. simpl in HD.
      rewrite fold_uncons_mapsto_eq; auto.
      right. exists I'; auto.
Qed.


Lemma EPP_deterministic : forall C A P1 P2,
  EPP A C P1 ->
  EPP A C P2 ->
  P1 = P2.
Proof.
  induction C as [ | I C]; intros A P1 P2 H1 H2.
  * inversion H1; inversion H2; subst; clear H1 H2.
    auto.
  * inversion H1; inversion H2; subst; clear H1 H2; auto;
    try discriminate;
    repeat match goal with
    | [ H : ?A <> ?A |- _ ] => contradiction
    | [ H : ?C _ = ?C _ |- _ ] => inversion H; subst; clear H
    | [ H : ?C _ _ = ?C _ _ |- _ ] => inversion H; subst; clear H
    | [ H : ?C _ _ _ = ?C _ _ _ |- _ ] => inversion H; subst; clear H
    | [ H : ?C _ _ _ _ = ?C _ _ _ _ |- _ ] => inversion H; subst; clear H
    end;
    f_equal; eauto;
    simpl in *; Actor.simplify. 
Qed.

Lemma EPP_disjoint_iff : forall A I C P,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A (I :: C) P <-> EPP A C P.
Proof.
  intros. split; intros Hepp.
  { apply EPP_disjoint_inversion in Hepp; auto. }
  { apply EPP_disjoint; auto. }
Qed.

Lemma EPP_N_nil : forall N,
  EPP_N [] N ->
  forall D PD, Actor.Map.MapsTo D PD N -> PD = [].
Proof.
  intros N HN.
  dependent induction HN; intros D PD HD.
  * Actor.simplify.
  * compare D A.
    + inversion H0; subst.
      eapply Actor.Map.Properties.F.MapsTo_fun; eauto.
    + apply (IHHN D PD).
      Actor.simplify.
Qed.

Lemma EPP_N_nil_nostep : forall N refs cfg l N' refs' cfg',
  EPP_N [] N ->
  ~ Network.step N refs cfg l N' refs' cfg'.
Proof.
  intros.
  assert (Hempty : forall D PD, Actor.Map.MapsTo D PD N -> PD = []).
  { apply EPP_N_nil; auto. }
  intros Hstep.
  clear H. revert Hempty.
  induction Hstep; intros Hempty; subst.
  * apply Hempty in H. subst. inversion H0.
  * apply Hempty in H0. inversion H0.
  * apply Hempty in H0. inversion H0.
Qed. 


Lemma EPR_cons_dec : forall I C x y A B PA PB,
  EPP A (I :: C) (Insn.EPR x B :: PA) ->
  EPP B (I :: C) (Insn.EPR y A :: PB) ->
  (I = Choreography.Insn.EPR A x B y)
    \/
  (I = Choreography.Insn.EPR B y A x)
    \/ (~ Actor.FSet.In A (Choreography.Insn.actors I)
        /\
        ~ Actor.FSet.In B (Choreography.Insn.actors I)).
Proof.
  intros I C x y A B PA PB HA HB.
  destruct (Actor.Map.FSetProofs.in_dec A (Choreography.Insn.actors I)) as [HinA | HinA].
  { (* A in I *)
    inversion HA; subst; clear HA;
    inversion HB; subst; clear HB;
    simpl in *; Actor.simplify.
  }
  destruct (Actor.Map.FSetProofs.in_dec B (Choreography.Insn.actors I)) as [HinB | HinB].
  { (* B in I *)
    inversion HA; subst; clear HA;
    inversion HB; subst; clear HB;
    simpl in *; Actor.simplify.
  }
  auto.
Qed.


Lemma completeness_epr : forall C N refs cfg A B N' refs' cfg',
  Network.step N refs cfg (Label.EPR A B) N' refs' cfg' ->
  EPP_N C N ->
  Choreography.WellFormed C ->
  (forall D, Actor.FSet.In D (Choreography.actors C) -> Actor.Map.In D N) ->
  exists C',
    Choreography.step C refs cfg (Label.EPR A B) C' refs' cfg'  /\
    EPP_N C' N' /\
    (forall D, Actor.FSet.In D (Choreography.actors C') -> Actor.Map.In D N').
Proof.
  intros C; induction C as [ | I C];
    intros ? ? ? ? ? ? ? ? Hstep HEPP_N HWF Hdomain.
  {
    (* absurd *)
    apply EPP_N_nil_nostep in Hstep; auto.
    contradiction.
  }

  inversion Hstep; subst; clear Hstep.
  rename H2 into HmapstoA, H3 into HmapstoB.
  rename H4 into HEPR, H12 into HN'.

  rewrite EPP_N_spec in HEPP_N.
  assert (HEPPA : EPP A (I :: C) (Insn.EPR x B :: PA))
    by (apply HEPP_N; auto).
  assert (HEPPB : EPP B (I :: C) (Insn.EPR y A :: PB))
    by (apply HEPP_N; auto).
  rewrite <- EPP_N_spec in HEPP_N.

  assert (HI : I = Choreography.Insn.EPR A x B y
    \/ I = Choreography.Insn.EPR B y A x
    \/ (~ Actor.FSet.In A (Choreography.Insn.actors I)
     /\ ~ Actor.FSet.In B (Choreography.Insn.actors I))).
  {
    eapply EPR_cons_dec; eauto.
  }
  destruct HI as [? | [? | [HA HB]]]; subst; simpl in *.

  + eexists.
    split.
    { econstructor; eauto. }
    split.
    2:{
      intros D HD.
      rewrite HN'.
      Actor.simplify. 
      right. right. apply Hdomain.
      Actor.simplify.
    }

    rewrite HN'; clear N' HN'.
    rewrite EPP_N_spec.
    intros D PD HD.
    Actor.simplify.
    EPP_N_cons.
    rename H into HEPP_AB, H0 into HEPP_N_other.

    destruct HD as [[? ?] | [? [[? ?] | [? HD]]]]; subst.
    - (* D = A *)
      apply EPP_subst_eq.
      apply EPP_subst_neq; auto.
      apply HEPP_AB in HmapstoA.
      2:{ Actor.simplify. }
      inversion HmapstoA; subst; auto; simpl in *; Actor.simplify.

    - (* D = B *)
      apply EPP_subst_neq; auto.
      apply EPP_subst_eq.
      apply HEPP_AB in HmapstoB.
      2:{ Actor.simplify. }
      inversion HmapstoB; subst; auto; simpl in *; Actor.simplify.

    - (* D <> A or B *)
      apply EPP_subst_neq; auto.
      apply EPP_subst_neq; auto.
      rewrite EPP_N_spec in HEPP_N_other.
      apply HEPP_N_other.
      Actor.simplify.

  + eexists.
    split.
    {
      eapply Choreography.EPRB'; eauto.
    }
    split.
    2:{
      intros D HD. rewrite HN'; clear N' HN'.
      Actor.simplify.
      right. right.
      apply Hdomain.
      Actor.simplify.
    }

    rewrite HN'; clear N' HN'.
    rewrite EPP_N_spec.
    intros D PD HD.
    Actor.simplify.
    EPP_N_cons.
    rename H into HEPP_AB, H0 into HEPP_N_other.

    destruct HD as [[? ?] | [? [[? ?] | [? HD]]]]; subst.
    - (* D = A *)
      apply EPP_subst_neq; auto.
      apply EPP_subst_eq; auto.
      apply HEPP_AB in HmapstoA.
      2:{ Actor.simplify. }
      inversion HmapstoA; subst; auto; simpl in *; Actor.simplify.

    - (* D = B *)
      apply EPP_subst_eq.
      apply EPP_subst_neq; auto.
      apply HEPP_AB in HmapstoB.
      2:{ Actor.simplify. }
      inversion HmapstoB; subst; auto; simpl in *; Actor.simplify.

    - (* D <> A or B *)
      apply EPP_subst_neq; auto.
      apply EPP_subst_neq; auto.
      rewrite EPP_N_spec in HEPP_N_other.
      apply HEPP_N_other.
      Actor.simplify.

  + (* A,B not in actors(I) *)

    apply EPP_disjoint_inversion in HEPPA; auto.
    apply EPP_disjoint_inversion in HEPPB; auto.
    inversion HWF; subst; clear HWF.

    set (HEPP_N' := EPP_N_cons_inversion _ _ _ HEPP_N).
    eapply IHC in HEPP_N'; auto.
    2:{
      eapply Network.EPR; eauto.
      { rewrite fold_uncons_mapsto_neq; eauto. }
      { rewrite fold_uncons_mapsto_neq; eauto. }
      { reflexivity. }
    }
    2:{
      intros D HD. Actor.simplify.
      apply Hdomain. Actor.simplify.
    }
    destruct HEPP_N' as [C' [Hstep' [HEPP_N' Hdomain']]].
    
    eexists (I :: C').
    split.
    { 
      apply Choreography.Delay; auto. simpl.
      intros D. Actor.simplify.
      intros [[? | ?] Hin]; subst; try contradiction.
    }
    split.
    2:{
      intros D HD. rewrite HN'; subst; clear HN'.
      simpl in HD.
      Actor.simplify.
      destruct HD as [HD | HD].
      { (* D in I *)
        right. right.
        apply Hdomain. simpl.
        Actor.simplify.
      }
      { (* D in C' *)
        apply Hdomain' in HD.
        Actor.simplify.
      }
    }

    rewrite HN' in *; clear N' HN'.
    rewrite EPP_N_spec in *.
    intros D PD Hmapsto.
    destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I)) as [Hin | Hin].
    2:{
      apply EPP_disjoint; auto.
      apply HEPP_N'.
      Actor.simplify.
      destruct Hmapsto as [[? ?] | [? [[? Hmapsto] | [? Hmapsto]]]]; subst; auto.
      right. split; auto.
      right. split; auto.
      apply fold_uncons_mapsto_neq; auto.
    }
    Actor.simplify.
    destruct Hmapsto as [[? ?] | [? [[? Hmapsto] | [? Hmapsto]]]]; subst;
      try contradiction.
    {
      set (HEPP' := HEPP_N _ _ Hmapsto).
      rewrite EPP_cons in HEPP'; auto.
      destruct HEPP' as [PA' [? HD]]; subst.
      rewrite EPP_cons; auto.
      exists PA'. split; auto.
      apply HEPP_N'.
      Actor.simplify.
      right. split; auto.
      right. split; auto.
      apply fold_uncons_mapsto_eq; auto.
      right.
      destruct I; simpl in *; Actor.simplify; eexists; subst; try contradiction; eauto.
      destruct Hin; subst; try contradiction.
      destruct Hin; subst; try contradiction.
    }

    Unshelve.
    all: (apply Insn.EPR; auto).
Qed.


Lemma step_domain_label_subset : forall C Θ ρ l C' Θ' ρ',
  Choreography.step C Θ ρ l C' Θ' ρ' ->
  forall D,
  Actor.FSet.In D (Choreography.Label.actors l) ->
  Actor.FSet.In D (Choreography.actors C).
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep; intros D HD; simpl in *; Actor.simplify.
Qed.

Lemma step_domain_subset : forall C Θ ρ l C' Θ' ρ',
  Choreography.step C Θ ρ l C' Θ' ρ' ->
  forall D,
  Actor.FSet.In D (Choreography.actors C') ->
  Actor.FSet.In D (Choreography.actors C).
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep; intros D HD; simpl in *; subst; Actor.simplify.
  * destruct HD; auto.
Qed.

Theorem completeness : forall N refs cfg l N' refs' cfg',

    Network.step N refs cfg l N' refs' cfg' ->

    forall C, Choreography.WellFormed C ->
    EPP_N C N ->
    (forall D, Actor.FSet.In D (Choreography.actors C) -> Actor.Map.In D N) ->
    exists C', EPP_N C' N' /\
                Choreography.step C refs cfg l C' refs' cfg' /\
                (forall D, Actor.FSet.In D (Choreography.actors C') -> Actor.Map.In D N').
Proof.
    intros N refs cfg l N' refs' cfg' Hstep C HWF HEPP Hdomain.
    destruct l as [A v B | A B | A ].

    * (* send *)
      eapply completeness_send in Hstep; eauto.
      destruct Hstep as [C' [Hstep [HEPP_N Hdomain']]].
      exists C'; auto.

    * (* EPR *)
      eapply completeness_epr in Hstep; eauto.
      destruct Hstep as [C' [Hstep [HEPP_N Hdomain']]].
      exists C'; auto.
  
    * (* local step *)
      inversion Hstep; subst; clear Hstep.
      rename H1 into Hstep, H2 into HN', H6 into Hrefs'.
      eapply completeness_local in Hstep; eauto; try reflexivity.
      destruct Hstep as [C0 [Hstep HEPP_N]].
      exists C0.
      split; auto.
      { rewrite HN'; auto. }
      split; auto.
      {
        intros D HD.
        rewrite HN'.
        eapply step_domain_subset in HD; eauto.
        Actor.simplify.        
      }
Qed.



(* Correctness of EPP *)


Hint Rewrite Actor.Map.FSetProofs.find_setminus : actor_db.

Lemma remove_singleton : forall A B,
  Actor.FSet.Equal (Actor.Map.S.remove A (Actor.FSet.singleton B))
    (if Actor.eq_dec A B then Actor.FSet.empty else Actor.FSet.singleton B).
Proof.
  intros A B.
  compare A B.
  * intros D. split; intros; Actor.simplify.
    rewrite Actor.Map.FSetProperties.empty_iff in H. contradiction.
  * intros D. Actor.simplify.
    split; [intros [? ?] | intros ?]; subst; auto.
Qed.
Hint Rewrite remove_singleton : actor_db.

Lemma EPP_cons_in_inversion : forall I C D PD,
  EPP D (I :: C) PD ->
  Actor.FSet.In D (Choreography.Insn.actors I) ->
  exists I' PD', eppI D I = [I'] /\ PD = I' :: PD'.
Proof.
  intros I C D PD HEPP Hin.
  inversion HEPP; subst; try contradiction;
  simpl; Actor.simplify; eexists; eexists; eauto. 
Qed.

Lemma EPP_send_inversion : forall A v B x C N PA,
  EPP_N (Choreography.Insn.Send A v B x :: C) N ->
  Actor.Map.MapsTo A PA N ->
  exists PA', PA = (Insn.Send v B :: PA').
Proof.
  intros A v B x C N PA H HA.
  rewrite EPP_N_spec in H.
  set (HEPP := H _ _ HA).
  apply EPP_cons_in_inversion in HEPP.
  2:{ simpl. Actor.simplify. }
  destruct HEPP as [I [PB' [Heq ?]]]; subst.
  simpl in *.
  Actor.simplify.
  inversion Heq; subst; clear Heq.
  eexists; eauto.
Qed.

Lemma EPP_receive_inversion : forall A v B x C N PB,
  EPP_N (Choreography.Insn.Send A v B x :: C) N ->
  A <> B ->
  Actor.Map.MapsTo B PB N ->
  exists PB', PB = Insn.Receive x A :: PB'.
Proof.
  intros A v B x C N PB H Hneq HB.
  rewrite EPP_N_spec in H.
  set (HEPP := H _ _ HB).
  apply EPP_cons_in_inversion in HEPP.
  2:{ simpl. Actor.simplify. }
  destruct HEPP as [I [PB' [Heq ?]]]; subst.
  simpl in *.
  Actor.simplify.
  inversion Heq; subst; clear Heq.
  eexists; eauto.
Qed.

Lemma EPP_let_inversion : forall A x e C N PA,
  EPP_N (Choreography.Insn.Let A x e :: C) N ->
  Actor.Map.MapsTo A PA N ->
  exists PA', PA = Insn.Let x e :: PA'.
Proof.
  intros A x e C N PA H HA.
  rewrite EPP_N_spec in H.
  set (HEPP := H _ _ HA).
  apply EPP_cons_in_inversion in HEPP.
  2:{ simpl. Actor.simplify. }
  destruct HEPP as [I [PB' [Heq ?]]]; subst.
  simpl in *.
  Actor.simplify.
  inversion Heq; subst; clear Heq.
  eexists; eauto.
Qed.

Lemma EPP_let_bang_inversion : forall A x e C N PA,
  EPP_N (Choreography.Insn.LetBang A x e :: C) N ->
  Actor.Map.MapsTo A PA N ->
  exists PA', PA = Insn.LetBang x e :: PA'.
Proof.
  intros A x e C N PA H HA.
  rewrite EPP_N_spec in H.
  set (HEPP := H _ _ HA).
  apply EPP_cons_in_inversion in HEPP.
  2:{ simpl. Actor.simplify. }
  destruct HEPP as [I [PB' [Heq ?]]]; subst.
  simpl in *.
  Actor.simplify.
  inversion Heq; subst; clear Heq.
  eexists; eauto.
Qed.

Lemma EPP_let_pair_inversion : forall A x1 x2 e C N PA,
  EPP_N (Choreography.Insn.LetPair A x1 x2 e :: C) N ->
  Actor.Map.MapsTo A PA N ->
  exists PA', PA = Insn.LetPair x1 x2 e :: PA'.
Proof.
  intros A x1 x2 e C N PA H HA.
  rewrite EPP_N_spec in H.
  set (HEPP := H _ _ HA).
  apply EPP_cons_in_inversion in HEPP.
  2:{ simpl. Actor.simplify. }
  destruct HEPP as [I [PB' [Heq ?]]]; subst.
  simpl in *.
  Actor.simplify.
  inversion Heq; subst; clear Heq.
  eexists; eauto.
Qed.

Lemma EPP_EPR_inversion_1 : forall A x1 B x2 C N PA,
  EPP_N (Choreography.Insn.EPR A x1 B x2 :: C) N ->
  Actor.Map.MapsTo A PA N ->
  exists PA', PA = Insn.EPR x1 B :: PA'.
Proof.
  intros A x1 B x2 C N PA H HA.
  rewrite EPP_N_spec in H.
  set (HEPP := H _ _ HA).
  apply EPP_cons_in_inversion in HEPP.
  2:{ simpl. Actor.simplify. }
  destruct HEPP as [I [PB' [Heq ?]]]; subst.
  simpl in *.
  Actor.simplify.
  inversion Heq; subst; clear Heq.
  eexists; eauto.
Qed.
Lemma EPP_EPR_inversion_2 : forall B x1 A x2 C N PA,
  EPP_N (Choreography.Insn.EPR B x1 A x2 :: C) N ->
  Actor.Map.MapsTo A PA N ->
  A <> B ->
  exists PA', PA = Insn.EPR x2 B :: PA'.
Proof.
  intros B x1 A x2 C N PA H HA Hneq.
  rewrite EPP_N_spec in H.
  set (HEPP := H _ _ HA).
  apply EPP_cons_in_inversion in HEPP.
  2:{ simpl. Actor.simplify. }
  destruct HEPP as [I [PB' [Heq ?]]]; subst.
  simpl in *.
  Actor.simplify.
  inversion Heq; subst; clear Heq.
  eexists; eauto.
Qed.


Lemma EPP_mapsto_uncons_in : forall I C N A I' PA',
  EPP_N (I :: C) N ->
  Actor.Map.MapsTo A (I' :: PA') N ->
  Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A C PA'.
Proof.
  intros I C N A I' PA' HN Hmapsto Hin.
  apply EPP_N_cons_inversion in HN.
  rewrite EPP_N_spec in HN.
  apply HN.
  rewrite fold_uncons_mapsto_eq; auto.
  right. eexists; eauto.
Qed.

Lemma EPP_mapsto_uncons_nin : forall I C N D PD,
  EPP_N (I :: C) N ->
  Actor.Map.MapsTo D PD N ->
  ~ Actor.FSet.In D (Choreography.Insn.actors I) ->
  EPP D C PD.
Proof.
  intros I C N D PD HN Hmapsto Hin.
  apply EPP_N_cons_inversion in HN.
  rewrite EPP_N_spec in HN.
  apply HN.
  rewrite fold_uncons_mapsto_neq; auto.
Qed.

Ltac EPP_cons_in_inversion A :=
  try match goal with
  | [ H : Actor.Map.In A ?N |- _ ] =>
    let H' := fresh H in
    let PA := fresh "P" in
    assert (H' : exists PA, Actor.Map.MapsTo A PA N)
      by (destruct H; eauto);
    clear H;
    destruct H' as [PA H]
  end;
  try match goal with
  | [ H : EPP_N (Choreography.Insn.Send A ?e ?B ?x :: ?C) ?N,
      H' : Actor.Map.MapsTo A ?PA _
    |- _ ] =>
    let PA' := fresh PA in
    destruct (EPP_send_inversion A e B x C N PA H)
      as [PA' ?]; subst; auto

  | [ H : EPP_N (Choreography.Insn.Send ?D ?e A ?x :: ?C) ?N,
      H' : Actor.Map.MapsTo A ?PA _
    |- _ ] =>
    let PA' := fresh PA in
    destruct (EPP_receive_inversion D e A x C N PA H)
      as [PA' ?]; subst; auto

  | [ H : EPP_N (Choreography.Insn.Let A ?x ?e :: ?C) ?N,
      H' : Actor.Map.MapsTo A ?PA _
    |- _ ] =>
    let PA' := fresh PA in
    destruct (EPP_let_inversion A x e C N PA H)
      as [PA' ?]; subst; auto

  | [ H : EPP_N (Choreography.Insn.LetBang A ?x ?e :: ?C) ?N,
      H' : Actor.Map.MapsTo A ?PA _
    |- _ ] =>
    let PA' := fresh PA in
    destruct (EPP_let_bang_inversion A x e C N PA H)
      as [PA' ?]; subst; auto

  | [ H : EPP_N (Choreography.Insn.LetPair A ?x1 ?x2 ?e :: ?C) ?N,
      H' : Actor.Map.MapsTo A ?PA _
    |- _ ] =>
    let PA' := fresh PA in
    destruct (EPP_let_pair_inversion A x1 x2 e C N PA H)
      as [PA' ?]; subst; auto

  | [ H : EPP_N (Choreography.Insn.EPR A ?x1 ?B ?x2 :: ?C) ?N,
      H' : Actor.Map.MapsTo A ?PA _
    |- _ ] =>
    let PA' := fresh PA in
    destruct (EPP_EPR_inversion_1 A x1 B x2 C N PA H)
      as [PA' ?]; subst; auto
  | [ H : EPP_N (Choreography.Insn.EPR ?B ?x1 A ?x2 :: ?C) ?N,
      H' : Actor.Map.MapsTo A ?PA _
    |- _ ] =>
    let PA' := fresh PA in
    destruct (EPP_EPR_inversion_2 B x1 A x2 C N PA H)
      as [PA' ?]; subst; auto

  (* fallthrough case *)
  | [ H : EPP_N (?I :: ?C) ?N,
      H' : Actor.Map.MapsTo A ?PA _
    |- _ ] =>
  
      let I' := fresh I in
      let PA' := fresh PA in
      let HI := fresh "HI" in
      destruct (EPP_cons_in_inversion I C A PA)
        as [I' [PA' [HI ?]]]; auto; subst; auto

  end;
  try match goal with
  | [ H : EPP_N (_ :: ?C) _, H' : Actor.Map.MapsTo A (_ :: ?PA') _ |- _ ] =>
    let H0 := fresh H in
    try assert (H0 : EPP A C PA')
    by (apply (EPP_mapsto_uncons_in _ _ _ _ _ _ H H'); simpl; Actor.simplify)
  end.

Ltac EPP_cons_nin_inversion D :=
  match goal with
  | [ H : EPP_N (_ :: ?C) ?N, H' : Actor.Map.MapsTo D ?PD ?N |- _ ] =>
    let H'' := fresh H' in
    assert (H'' : EPP D C PD)
    by (apply (EPP_mapsto_uncons_nin _ _ _ _ _ H H'); simpl; Actor.simplify)
  end.


Ltac destruct_cases H :=
  match type of H with
  | ((_ = _) /\ _) \/ ((_ <> _) /\ _) => destruct H as [[? ?] | [? H]]; subst
  end.

Ltac reflect_EPP_N_goal :=
  repeat match goal with
  | [ |- EPP_N _ _ ] => 
    let D := fresh "D" in
    let PD := fresh "PD" in
    let HD := fresh "HD" in
    rewrite EPP_N_spec; intros D PD HD;
    Actor.simplify;
    try (destruct_cases HD)
  end.

Lemma soundness_local : forall PA C refs cfg A C' refs' cfg' N,
  Choreography.step C refs cfg (Choreography.Label.Loc A) C' refs' cfg' ->
  EPP_N C N ->
  Choreography.WellFormed C ->
  Actor.Map.MapsTo A PA N ->
  exists PA' refsA', Process.step PA (ChorEnv.find A refs) cfg PA' refsA' cfg'
           /\ EPP_N C' (Actor.Map.add A PA' N)
           /\ ChorEnv.Equal refs' (Actor.Map.add A refsA' refs).
Proof.
  intros PA C refs cfg A C' refs' cfg' N Hstep.
  remember (Choreography.Label.Loc A) as l eqn:Hl.
  revert N A Hl.
  induction Hstep; intros N D Hl HEPP_N HWF HD;
    inversion Hl; subst; try clear Hl;
    try rename D into A.
  * (* SendC *)
    assert (A <> B).
    {
      inversion HWF; subst; clear HWF.
      inversion H3; subst; clear H3; auto.
    }
    EPP_cons_in_inversion A; auto.
    
    eexists. eexists.
    split.
    { econstructor; eauto. }
    split; auto.

    eapply (EPP_N_add _ A).
    { Actor.simplify. }
    { econstructor; auto. }
    Actor.simplify.
    
    reflect_EPP_N_goal.

    compare D B.
    { (* D = B *)
      EPP_cons_in_inversion D.
      constructor; auto.
    }
    {
      apply EPP_disjoint.
      { simpl; Actor.simplify. }
      EPP_cons_nin_inversion D; auto.
    }

  * (* LetC *)
    EPP_cons_in_inversion A; auto.
    eexists. eexists.
    split.
    { econstructor; eauto. }
    split; auto.

    reflect_EPP_N_goal.
    { (* D = A *)
      econstructor; auto.
    }
    { (* D <> A *)
      EPP_cons_nin_inversion D.
      constructor; auto.
      simpl; Actor.simplify.
    }

  * (* LetB *)
    EPP_cons_in_inversion A; auto.
    eexists; eexists.
    split.
    { apply Process.LetB; eauto. reflexivity. }
    split; auto.
    2:{ ChorEnv.simplify. symmetry; auto. }

    reflect_EPP_N_goal.
    { (* D = A *)
      apply EPP_subst_eq; auto.
    }
    { (* D <> A *)
      EPP_cons_nin_inversion D.
      apply EPP_subst_neq; auto.
    }

  * (* LetBangC *) 
    EPP_cons_in_inversion A; auto.
    eexists. eexists.
    split.
    { econstructor; eauto. }
    split; auto.

    reflect_EPP_N_goal.
    { (* D = A *)
      econstructor; auto.
    }
    { (* D <> A *)
      EPP_cons_nin_inversion D.
      constructor; auto.
      simpl; Actor.simplify.
    }
    
  * (* LetBangB *)
    EPP_cons_in_inversion A; auto.
    eexists; eexists.
    split.
    { apply Process.LetBangB; eauto. }
    split; auto.
    2:{ rewrite H0. ChorEnv.simplify. }

    reflect_EPP_N_goal.
    { (* D = A *)
      apply EPP_subst_eq; auto.
    }
    { (* D <> A *)
      EPP_cons_nin_inversion D.
      apply EPP_subst_neq; auto.
    }


  * (* LetPairC *) 
    EPP_cons_in_inversion A; auto.
    eexists. eexists.
    split.
    { econstructor; eauto. }
    split; auto.

    reflect_EPP_N_goal.
    { (* D = A *)
      econstructor; auto.
    }
    { (* D <> A *)
      EPP_cons_nin_inversion D.
      constructor; auto.
      simpl; Actor.simplify.
    }
    
  * (* LetPairB *)
    EPP_cons_in_inversion A; auto.
    eexists; eexists.
    split.
    { apply Process.LetPairB; eauto. }
    split; auto.
    2:{ rewrite H2. ChorEnv.simplify. }

    reflect_EPP_N_goal.
    { (* D = A *)
      apply EPP_subst_eq; auto.
      apply EPP_subst_eq; auto.
    }
    { (* D <> A *)
      EPP_cons_nin_inversion D.
      apply EPP_subst_neq; auto.
      apply EPP_subst_neq; auto.
    }

  * (* delay *)
    clear H0.
    assert (Hnin : ~ Actor.FSet.In A (Choreography.Insn.actors I)).
    { 
      intros Hin. apply (H A). simpl. Actor.simplify.
    }
    clear H.

    set (HEPP_N' := HEPP_N).
    apply EPP_N_cons_inversion in HEPP_N'.
    eapply IHHstep in HEPP_N'; eauto.
    2:{ inversion HWF; auto. }
    2:{ rewrite fold_uncons_mapsto_neq; auto. }
    destruct HEPP_N' as [PA' [refsA' [IHstep [IHEPP_N HT']]]].

    exists PA'. exists refsA'.
    split; auto.
    split; auto.
    reflect_EPP_N_goal.
    { (* D = A *)
      apply EPP_disjoint; auto.
      rewrite EPP_N_spec in IHEPP_N.
      apply IHEPP_N.
      Actor.simplify.
    }
    destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I)) as [Hin | Hin].
    2:{ (* D ∉ I *)
      apply EPP_disjoint; auto.
      rewrite EPP_N_spec in IHEPP_N.
      apply IHEPP_N.
      Actor.simplify.
      right. split; auto.
      rewrite fold_uncons_mapsto_neq; auto.
    }
    { (* D in I *)
      EPP_cons_in_inversion D.
      { rewrite EPP_N_spec in HEPP_N. apply HEPP_N; auto. }
      rewrite EPP_cons; auto.
      2:{ inversion HWF; auto. }
      rewrite HI. simpl.
      eexists; split; eauto.

      rewrite EPP_N_spec in IHEPP_N.
      apply IHEPP_N.
      Actor.simplify.
      right; split; auto.
      rewrite fold_uncons_mapsto_eq; auto.
      right. eexists; eauto.
    }
Qed.



Lemma soundness_send : forall C refs cfg A v B C' refs' cfg',
  (* by induction on step relation *)
  Choreography.step C refs cfg (Choreography.Label.Send A v B) C' refs' cfg' ->
  A <> B ->
  Choreography.WellFormed C ->
  forall N,
  EPP_N C N ->
  Actor.Map.In A N ->
  Actor.Map.In B N ->
  exists N', 
    Network.step N refs cfg (Choreography.Label.Send A v B) N' refs' cfg'
    /\ EPP_N C' N'.
Proof.
  intros ? ? ? ? ? ? ? ? ? Hstep Hneq HWF N HN HA HB.
  dependent induction Hstep.
  *

    EPP_cons_in_inversion A.
    EPP_cons_in_inversion B.

    eexists.
    split.
    + econstructor; eauto.
      { reflexivity. }
      { symmetry; auto. }  
    +
      eapply EPP_N_add.
      { Actor.simplify. }
      { apply EPP_subst_neq; auto. }
      eapply (EPP_N_add _ B).
      { Actor.simplify. }
      { apply EPP_subst_eq; auto. }
      apply EPP_N_subst_neq.
      { Actor.simplify. }
      Actor.simplify.
      EPP_N_cons; auto.

  * (* C = I :: C' such that A ∉ I *)
    assert (HA' : ~ Actor.FSet.In A (Choreography.Insn.actors I)).
    { intros Hin. apply (H A). simpl. Actor.simplify. }
    assert (HB' : ~ Actor.FSet.In B (Choreography.Insn.actors I)).
    { intros Hin. apply (H B). simpl. Actor.simplify. }
    set (IH := HN).
    apply EPP_N_cons_inversion in IH.
    eapply IHHstep in IH; eauto.
    2:{ inversion HWF; auto. }
    2:{ 
        Actor.reflect_find.
        discriminate.
    }
    destruct IH as [N' [Hstep' HEPP_N']].
    inversion Hstep'; subst; clear Hstep'.
    rename H4 into HA'', H5 into HB'', H9 into Heq.
    rewrite fold_uncons_mapsto_neq in HA''; auto.
    rewrite fold_uncons_mapsto_neq in HB''; auto.

    eexists.
    split.
    + 
      econstructor; eauto.
      reflexivity.
    + 
      rewrite EPP_N_spec in HEPP_N'.
      reflect_EPP_N_goal.
      { (* D = A *)
        apply EPP_disjoint; auto.
        apply HEPP_N'.
        rewrite Heq.
        Actor.simplify.
      }
      
      destruct_cases HD.
      { (* D = B *)
        apply EPP_disjoint; auto.
        apply HEPP_N'.
        rewrite Heq.
        Actor.simplify.
      }
      destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I)) as [Hin | Hin].
      2:{
        apply EPP_disjoint; auto.
        apply HEPP_N'.
        rewrite Heq.
        Actor.simplify.
        right. split; auto. right. split; auto.
        rewrite fold_uncons_mapsto_neq; auto.
      }
      EPP_cons_in_inversion D.
      { rewrite EPP_N_spec in HN. apply HN; auto. }
      rewrite EPP_cons; auto.
      2:{ inversion HWF; subst; auto. }
      rewrite HI; simpl.
      eexists; split; eauto.
      apply HEPP_N'.
      rewrite Heq.
      Actor.simplify.
      right. split; auto. right. split; auto.
      rewrite fold_uncons_mapsto_eq; auto.
      right. eexists; eauto.

    + Actor.reflect_find.
      discriminate.
Qed.

Lemma soundness_epr : forall C refs cfg A B C' refs' cfg',
  Choreography.step C refs cfg (Choreography.Label.EPR A B) C' refs' cfg' ->
  A <> B ->
  Choreography.WellFormed C ->
  forall N,
  EPP_N C N ->
  Actor.Map.In A N ->
  Actor.Map.In B N ->
  exists N',
    Network.step N refs cfg (Choreography.Label.EPR A B) N' refs' cfg'
    /\ EPP_N C' N'.
Proof.
  intros C refs cfg A B C' refs' cfg' Hstep.
  remember (Choreography.Label.EPR A B) as l eqn:Hl.
  revert A B Hl.
  induction Hstep;
    intros A0 B0 Hl Hneq HWF N HN HA HB;
    inversion Hl; subst; try clear Hl.

  * (* backwards EPR *)
    rename A0 into A, B0 into B.

    EPP_cons_in_inversion A.
    EPP_cons_in_inversion B.
    
    eexists.
    split.
    +
      econstructor; eauto.
      reflexivity.

    +
      rewrite EPP_N_spec in HN.
      reflect_EPP_N_goal.
      { (* D = A *)
        apply EPP_subst_eq.
        apply EPP_subst_neq; auto.
      }
      
      destruct_cases HD.
      { (* D = B *)
        apply EPP_subst_neq; auto.
        apply EPP_subst_eq; auto.
      }
      {
        apply EPP_subst_neq; auto.
        apply EPP_subst_neq; auto.
        apply HN in HD.
        apply EPP_disjoint_inversion in HD; auto.
        { simpl; Actor.simplify. }
      }

  * rename A0 into A, B0 into B.

    EPP_cons_in_inversion A.
    EPP_cons_in_inversion B.
    
    eexists.
    split.
    +
      econstructor; eauto.
      reflexivity.

    +
      rewrite EPP_N_spec in HN.
      reflect_EPP_N_goal.
      { (* D = A *)
        apply EPP_subst_neq; auto.
        apply EPP_subst_eq; auto.
      }
      
      destruct_cases HD.
      { (* D = B *)
        apply EPP_subst_eq; auto.
        apply EPP_subst_neq; auto.
      }
      {
        apply EPP_subst_neq; auto.
        apply EPP_subst_neq; auto.
        apply HN in HD.
        apply EPP_disjoint_inversion in HD; auto.
        { simpl; Actor.simplify. }
      }


  * (* Inductive case *)
    clear H0. rename A0 into A, B0 into B.

    assert (HA' : ~ Actor.FSet.In A (Choreography.Insn.actors I)).
    { intros Hin. apply (H A). simpl. Actor.simplify. }
    assert (HB' : ~ Actor.FSet.In B (Choreography.Insn.actors I)).
    { intros Hin. apply (H B). simpl. Actor.simplify. }
    set (IH := HN).
    apply EPP_N_cons_inversion in IH.
    eapply IHHstep in IH; eauto.
    2:{ inversion HWF; auto. }
    2:{ 
        Actor.reflect_find.
        discriminate.
    }
    destruct IH as [N' [Hstep' HEPP_N']].
    inversion Hstep'; subst; clear Hstep'.
    rename H3 into HA'', H4 into HB'', H5 into Hepr, H9 into HT', H13 into HN'.
    rewrite fold_uncons_mapsto_neq in HA''; auto.
    rewrite fold_uncons_mapsto_neq in HB''; auto.

    eexists.
    split.
    + 
      econstructor; eauto.
      reflexivity.
    + 
      rewrite EPP_N_spec in HEPP_N'.
      reflect_EPP_N_goal.
      { (* D = A *)
        apply EPP_disjoint; auto.
        apply HEPP_N'.
        rewrite HN'.
        Actor.simplify.
      }
      
      destruct_cases HD.
      { (* D = B *)
        apply EPP_disjoint; auto.
        apply HEPP_N'.
        rewrite HN'.
        Actor.simplify.
      }
      destruct (Actor.Map.FSetProofs.in_dec D (Choreography.Insn.actors I)) as [Hin | Hin].
      2:{
        apply EPP_disjoint; auto.
        apply HEPP_N'.
        rewrite HN'.
        Actor.simplify.
        right. split; auto. right. split; auto.
        rewrite fold_uncons_mapsto_neq; auto.
      }
      EPP_cons_in_inversion D.
      { rewrite EPP_N_spec in HN. apply HN; auto. }
      rewrite EPP_cons; auto.
      2:{ inversion HWF; subst; auto. }
      rewrite HI; simpl.
      eexists; split; eauto.
      apply HEPP_N'.
      rewrite HN'.
      Actor.simplify.
      right. split; auto. right. split; auto.
      rewrite fold_uncons_mapsto_eq; auto.
      right. eexists; eauto.

    + Actor.reflect_find.
      discriminate.
Qed.

Theorem soundness : forall C C' refs cfg refs' cfg' l,
    Choreography.step C refs cfg l C' refs' cfg' ->
    Choreography.WellFormed C ->
    Label.WellFormed l ->
    forall N,
      (forall D, Actor.FSet.In D (Choreography.Label.actors l) -> Actor.Map.In D N) ->
      EPP_N C N ->
    exists N', Network.step N refs cfg l N' refs' cfg'
              /\ EPP_N C'  N'.
Proof.
  intros ? ? ? ? ? ? ? Hstep WF WFl N Hsubset HN.
  destruct l as [A v B | A B | A].
  * (* Send *)
    inversion WFl; subst; clear WFl.
    eapply soundness_send; eauto.
    { apply Hsubset. simpl. Actor.simplify. }
    { apply Hsubset. simpl. Actor.simplify. }

  * (* EPR *) 
    eapply soundness_epr; eauto.
    { inversion WFl; auto. }
    { apply Hsubset. simpl. Actor.simplify. }
    { apply Hsubset. simpl. Actor.simplify. }

  * (* Local *)
    assert (HA : exists PA, Actor.Map.MapsTo A PA N).
    { 
      destruct (Hsubset A); eauto.
      simpl; Actor.simplify.
    }
    destruct HA as [PA HA].
    eapply soundness_local in Hstep; eauto.
    destruct Hstep as [PA' [refsA' [Hstep [HPA' Hrefs']]]].
    eexists. split; eauto.
    {
      econstructor; eauto.
      reflexivity.
    }
Qed.

Lemma WellFormed_projectable : forall C,
  Choreography.WellFormed C ->
  forall A, exists P, EPP A C P.
Proof.
  intros C HC.
  induction HC; intros A.
  { eexists; econstructor. }
  {
    destruct (IHHC A) as [P IH].
    eexists.
    rewrite EPP_cons; auto.
    eexists. split; eauto.
  }
Qed.

Definition eppN C :=
  let f := fun A => match epp A C with
                    | Some PA => Some (Some PA)
                    | None => None
                    end
  in actor_map f (Choreography.actors C) (Actor.Map.empty _).


Lemma find_eppN : forall C A,
  Actor.FSet.In A (Choreography.actors C) ->
  Actor.Map.find A (eppN C) = epp A C.
Proof.
  intros C A Hin. unfold eppN.
  autorewrite with actor_db.
  destruct (Actor.Map.FSetProofs.in_dec A) as [_ | ?]; [ | contradiction].
  destruct (epp A C); auto.
Qed.
 
Lemma WellFormed_projectable_N : forall C,
  Choreography.WellFormed C ->
  EPP_N C (eppN C).
Proof.
  intros C HC.
  rewrite EPP_N_spec.
  intros D PD HD.
  rewrite EPP_correct.
  Actor.reflect_find.
  unfold eppN in HD.
  autorewrite with actor_db in HD.
  destruct (Actor.Map.FSetProofs.in_dec D (Choreography.actors C))
    as [Hin | Hnin].
  * destruct (epp D C); try discriminate; auto.
  *  discriminate.
Qed.

Lemma eppN_complete : forall C,
  Choreography.WellFormed C ->
  (forall D, Actor.FSet.In D (Choreography.actors C) -> Actor.Map.In D (eppN C)).
Proof.
    intros C HWF D Hin.
    assert (HEPP : exists PD, EPP D C PD).
    { apply WellFormed_projectable; auto. }
    destruct HEPP as [PD HEPP].
    apply EPP_correct in HEPP.
    Actor.reflect_find.
    rewrite find_eppN; auto.
    rewrite HEPP. discriminate.
Qed.

Definition EPP_N_complete C N :=
  EPP_N C N /\
  Choreography.WellFormed C /\
  (forall D, Actor.FSet.In D (Choreography.actors C) -> Actor.Map.In D N).


Lemma EPP_correctness : forall C N Θ ρ l,
  EPP_N_complete C N ->
  (exists C' Θ' ρ', Choreography.step C Θ ρ l C' Θ' ρ') <->
  (exists N' Θ' ρ', Network.step N Θ ρ l N' Θ' ρ').
Proof.
  intros C N Θ ρ l [HEPP_N [HWF Hdomain]].
  split.
  * intros [C' [Θ' [ρ' Hstep]]].
    eapply soundness in Hstep; eauto.
    2:{ eapply Choreography.step_wf_label; eauto. }
    2:{ intros D HD. apply Hdomain. eapply step_domain_label_subset; eauto. }
    destruct Hstep as [N' [Hstep HEPP']].
    exists N', Θ', ρ'. auto.
  * intros [N' [Θ' [ρ' Hstep]]].
    eapply completeness in Hstep; eauto.
    destruct Hstep as [C' [HEPP_N' [Hstep Hdomain']]].
    exists C', Θ', ρ'. auto.
Qed.



Inductive multi_step : Network.t -> ChorEnv.t nat -> Config.t -> Network.t -> ChorEnv.t nat -> Config.t -> Prop :=
| Step0 : forall N Θ ρ, multi_step N Θ ρ N Θ ρ
| Step1 : forall N1 N2 N3 Θ1 Θ2 Θ3 ρ1 ρ2 ρ3 l,
  Network.step N1 Θ1 ρ1 l N2 Θ2 ρ2 ->
  multi_step N2 Θ2 ρ2 N3 Θ3 ρ3 ->
  multi_step N1 Θ1 ρ1 N3 Θ3 ρ3
.

(** EPP+type safety *)
Theorem safety : forall N Θ ρ N' Θ' ρ',
  multi_step N Θ ρ N' Θ' ρ' ->

  forall C,
  Choreography.WellTyped (Actor.Map.empty _) (Actor.Map.empty _) Θ C ->
  ChorEnv.WellScoped Θ ρ ->
  EPP_N_complete C N ->

  Network.Empty N' \/ exists l N'' Θ'' ρ'', Network.step N' Θ' ρ' l N'' Θ'' ρ''.
Proof.
  intros ? ? ? ? ? ? Hstep.
  induction Hstep; intros C HWT HWS [HEPP_N [HWF Hdomain]].
  * destruct (Choreography.safety C Θ ρ C Θ ρ)
      as [ | [l [C'' [Θ'' [ρ'' Hstep]]]]];
      auto.
    { apply Choreography.Step0. }
    + (* C = [] *)
      subst. left.
      rewrite EPP_N_spec in HEPP_N.
      intros D PD HD.
      apply HEPP_N in HD.
      inversion HD; auto.
    + (* C can take a step *)
      right.
      eapply soundness in Hstep; eauto.
      2:{ eapply Choreography.step_wf_label; eauto. }
      2:{
        intros D HD.
        apply Hdomain.
        eapply step_domain_label_subset; eauto.
      }

      destruct Hstep as [N' [Hstep HEPP_N']].
      exists l, N', Θ'', ρ''; auto.

  * (* First, we know that C can take a step because N1 can, and that C2 is related to N2 *)
    edestruct (completeness N1 Θ1 ρ1 l N2 Θ2 ρ2)
      as [C2 [HEPP2 [Hstep2 Hdomain2]]]; eauto.
    assert (HWT2 : Choreography.WellTyped (Actor.Map.empty _) (Actor.Map.empty _) Θ2 C2).
    {
      (* C2 is well-typed by perservation *)
      eapply Choreography.preservation; eauto.
      intros A HA. ChorEnv.simplify. split; auto with var_db.
    }
    
    destruct (IHHstep C2); auto.
    { eapply Choreography.WellScoped_preservation; eauto. }
    split; auto. split; auto.
    { eapply Choreography.WellTyped_WellFormed; eauto. }
Qed.