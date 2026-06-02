From Qoreo Require Import Base.
From Qoreo Require Expr Choreography.
From Stdlib Require Import Morphisms (* for Proper *).

Module Label := Choreography.Label.
Module Choreography := Choreography.Choreography.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Stdlib.Structures.Equalities.
Import Actor.Map.Tactics.

Module Insn.
    Inductive t :=
    | Let : Var.t -> Expr.t -> t
    | LetBang : Var.t -> Expr.t -> t
    | LetPair : Var.t -> Var.t -> Expr.t -> t
    | Send : Expr.t -> Actor.t -> t
    | Receive : Var.t -> Actor.t ->  t
    | EPR : Var.t -> Actor.t -> t
    .

    Definition subst (x : Var.t) (v : Expr.t) (I : t) : t :=
        match I with
        | Let y e => Let y (Expr.subst x v e)
        | LetBang y e => LetBang y (Expr.subst x v e)
        | LetPair y1 y2 e => LetPair y1 y2 (Expr.subst x v e)
        | Send e A => Send (Expr.subst x v e) A
        | Receive y A => Receive y A
        | EPR y A => EPR y A
        end.

    Definition binders (I : t) : Var.FSet.t :=
        match I with
        | Let y _ | LetBang y _ | Receive y _ | EPR y _ => Var.FSet.singleton y
        | LetPair y1 y2 _ => Var.FSet.add y1 (Var.FSet.singleton y2)
        | Send _ _ => Var.FSet.empty
        end.
End Insn.

Module Process.
    Definition t := list Insn.t.

    Fixpoint subst (x : Var.t) (v : Expr.t) (P : t) : t :=
    match P with
    | [] => []
    | (I0 :: P') =>
      let P'' := if Var.FSet.mem x (Insn.binders I0)
                 then P'
                 else subst x v P'
      in
      (Insn.subst x v I0) :: P''
    end.


    (* Semantics *)

    Inductive step : Process.t -> Var.Map.t nat -> Config.t -> Process.t -> Var.Map.t nat -> Config.t -> Prop :=
    | LetC : forall x e P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.Let x e :: P) refs ρ (Insn.Let x e' :: P) refs' ρ'
    | LetB : forall x v P refs ρ P',
        Expr.Val v ->
        P' = Process.subst x v P ->
        step (Insn.Let x v :: P) refs ρ P' refs ρ

    | LetBangC : forall x e P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.LetBang x e :: P) refs ρ (Insn.LetBang x e' :: P) refs' ρ'
    | LetBangB : forall x e P refs ρ P',
        P' = Process.subst x e P ->
        step (Insn.LetBang x (Expr.Bang e) :: P) refs ρ P' refs ρ

    | LetPairC : forall x1 x2 e P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.LetPair x1 x2 e :: P) refs ρ (Insn.LetPair x1 x2 e' :: P) refs' ρ'
    | LetPairP : forall x1 x2 v1 v2 P ρ refs P',
        Expr.Val v1 -> Expr.Val v2 ->
        P' = Process.subst x2 v2 (Process.subst x1 v1 P) ->
        step (Insn.LetPair x1 x2 (Expr.Pair v1 v2) :: P) refs ρ P' refs ρ

    | SendC : forall e B P refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        step (Insn.Send e B :: P) refs ρ (Insn.Send e' B :: P) refs' ρ'
    .

End Process.

Module Network.
    Definition t := Actor.Map.t (Process.t).

    Inductive step :    Network.t -> ChorEnv.t nat -> Config.t ->
                        Label.t ->
                        Network.t -> ChorEnv.t nat -> Config.t -> Prop :=

    | Loc : forall P P' refsA' N' N refs cfg A refs' cfg',
      Actor.Map.MapsTo A P N ->
      Process.step  P (ChorEnv.find A refs) cfg
                    P' refsA' cfg' ->
      N' = Actor.Map.add A P' N ->
      ChorEnv.Equal refs' (Actor.Map.add A refsA' refs) ->
      step  N refs cfg
            (Label.Loc A)
            N' refs' cfg'

    | Send : forall PA PB y N refs cfg A v B N',
      A <> B ->
      Actor.Map.MapsTo A (Insn.Send v B :: PA) N ->
      Actor.Map.MapsTo B (Insn.Receive y A :: PB) N ->
      Expr.Val v ->
      N' = Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N) ->
      
      step N refs cfg (Label.Send A v B) N' refs cfg

    | EPR : forall x y PA PB qA qB N refs cfg A B N' refs' cfg',
      A <> B ->
      Actor.Map.MapsTo A (Insn.EPR x B :: PA) N ->
      Actor.Map.MapsTo B (Insn.EPR y A :: PB) N ->
      ChorEnv.epr A B refs cfg = (qA, qB, refs', cfg') ->
      N' = Actor.Map.add A (Process.subst x (Expr.Var qA) PA) (
            Actor.Map.add B (Process.subst y (Expr.Var qB) PB) N) ->

      step N refs cfg (Label.EPR A B) N' refs' cfg'
    .

    Record WF (Actors : Actor.FSet.t) (N : Network.t) :=
        {
            wf_domain : forall A, Actor.FSet.In A Actors <-> Actor.Map.In A N;
        }.
    
End Network.

Definition conso {A : Type} (x : A) (xso : option (list A)) : option (list A) :=
  match xso with
  | None => None
  | Some xs => Some (x :: xs)
  end.

Fixpoint epp (p : Actor.t) (c : Choreography.t): option Process.t :=
  match c with
  | [] => Some []
  | Choreography.Insn.Send A1 e A2 x :: C =>
      match (Actor.eq_dec A1 p, Actor.eq_dec A2 p) with
      | (left _, left _)  => None
      | (left _, right _) => conso (Insn.Send e A2) (epp p C)
      | (right _, left _) => conso (Insn.Receive x A1) (epp p C)
      | _ => epp p C
      end
  | Choreography.Insn.EPR A1 x1 A2 x2 :: C =>
      match (Actor.eq_dec A1 p, Actor.eq_dec A2 p) with
      | (left _, left _)  => None
      | (left _, right _) => conso (Insn.EPR x1 A2) (epp p C)
      | (right _, left _) => conso (Insn.EPR x2 A1) (epp p C)
      | _ => epp p C
      end
  | Choreography.Insn.Let A1 x e :: C =>
      if Actor.eq_dec A1 p
      then conso (Insn.Let x e) (epp p C)
      else epp p C
  | Choreography.Insn.LetBang A1 x e :: C =>
      if Actor.eq_dec A1 p
      then conso (Insn.LetBang x e) (epp p C)
      else epp p C
  | Choreography.Insn.LetPair A1 x1 x2 e :: C =>
      if Actor.eq_dec A1 p
      then conso (Insn.LetPair x1 x2 e) (epp p C)
      else epp p C
  (* | _ => None *)
end.

(*
Inductive EPP : list Actor.t -> Choreography.t -> Network.t -> Prop :=
| epp_empty : forall C, EPP [] C (Actor.Map.empty _)
| epp_cons : forall A Actors C P N,
    epp A C = Some P ->
    EPP Actors C N ->
    EPP (A::Actors) C (Actor.Map.add A P N).
*)
Inductive EPP : Actor.t -> Choreography.t -> Process.t -> Prop :=
| EPP_nil : forall A, EPP A [] []

| EPP_send : forall D A C P B e y,
    D = A ->
    D <> B ->
    EPP D C P ->
    EPP D (Choreography.Insn.Send A e B y :: C) (Insn.Send e B :: P)
| EPP_receive : forall D B C P A e y,
    D = B ->
    D <> A ->
    EPP D C P ->
    EPP D (Choreography.Insn.Send A e B y :: C) (Insn.Receive y A :: P)

| EPP_EPR_1 : forall D A B x y C P,
    D = A ->
    D <> B ->
    EPP D C P ->
    EPP D (Choreography.Insn.EPR A x B y :: C) (Insn.EPR x B :: P)
| EPP_EPR_2 : forall D A B x y C P,
    D <> A ->
    D = B ->
    EPP D C P ->
    EPP D (Choreography.Insn.EPR A x B y :: C) (Insn.EPR y A :: P)

| EPP_Let : forall D A x e C P,
    D = A ->
    EPP D C P ->
    EPP D (Choreography.Insn.Let A x e :: C) (Insn.Let x e :: P)

| EPP_LetBang : forall D A x e C P,
    D = A ->
    EPP D C P ->
    EPP D (Choreography.Insn.LetBang A x e :: C) (Insn.LetBang x e :: P)

| EPP_LetPair : forall D A x1 x2 e C P,
    D = A ->
    EPP D C P ->
    EPP D (Choreography.Insn.LetPair A x1 x2 e :: C) (Insn.LetPair x1 x2 e :: P)

| EPP_disjoint : forall A I C P,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A C P ->
  EPP A (I :: C) P
.

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

(*
Definition EPP_N (C : Choreography.t) (N : Network.t) : Prop :=
    forall A PA,
        Actor.Map.MapsTo A PA N
        ->
        (*Actor.FSet.In A (Choreography.actors C)*)
        EPP A C PA.
*)
Inductive EPP_N C : Network.t -> Prop :=
| EPP_N_empty : forall N,
  Actor.Map.Empty N ->
  EPP_N C N
| EPP_N_add : forall A PA N,
  Actor.Map.MapsTo A PA N ->
  EPP A C PA ->
  EPP_N C (Actor.Map.remove A N) ->
  EPP_N C N.

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
    About EPP_N_add.
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
        exfalso. Actor.solve. discriminate.
      }
      right. split; auto.
    }
Qed.

(* Correctness of EPP *)

Theorem soundness : forall C C' refs cfg refs' cfg' l N,

    Choreography.step C refs cfg l C' refs' cfg' ->
    EPP_N C N ->
    exists N', EPP_N C'  N' /\
               Network.step N refs cfg l N' refs' cfg'.
Admitted.

Require Import Stdlib.Program.Equality.

Lemma actors_subst : forall I B x v,
  Actor.FSet.Equal
    (Choreography.Insn.actors (Choreography.Insn.subst B x v I))
    (Choreography.Insn.actors I).
Proof.
  destruct I; intros; Actor.simplify.
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
Hint Rewrite Actor.Map.FSetProperties.add_iff : actor_db.


Lemma EPP_subst_neq : forall C A P B x v,
    A <> B ->
    EPP A C P ->
    EPP A (Choreography.subst B x v C) P.
Proof.
  induction C as [ | I C];
    intros ? ? ? ? ? Hneq H.
  { inversion H; subst; constructor. }
  inversion H; subst; clear H; simpl;
    try (repeat reduce_eq_dec;
    repeat Var.Map.Tactics.reduce_eq_dec;
    simpl;
    constructor; auto; fail).

  apply EPP_disjoint.
  { rewrite actors_subst; auto. }
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
    rewrite actors_subst; auto.
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
      Var.simplify.
    + (* A = B0 *)
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * simpl in Hin. autorewrite with actor_db in Hin.
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
  * simpl in Hin. autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * simpl in Hin. autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
  * simpl in Hin. autorewrite with actor_db in Hin. subst.
  
      inversion Hepp; subst; clear Hepp;
      simpl in *; Actor.simplify;
      constructor; auto.
Qed. 



Lemma add_mem_iff : forall x y s,
  Var.Map.S.mem x (Var.Map.S.add y s)
  =
  if Var.eq_dec x y then true else Var.Map.S.mem x s.
Proof.
  intros.
  rewrite Var.Map.MProofs.FSetProperties.add_b.
  unfold Var.Map.MProofs.FSetProperties.eqb.
  Var.simplify.
Qed.
#[global] Hint Rewrite add_mem_iff : var_db.


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
  destruct I; intros; simpl in *; Actor.simplify.
Qed.

Lemma singleton_mem_iff : forall x y,
  Var.Map.S.mem y (Var.Map.S.singleton x)
  =
  if Var.eq_dec x y then true else false.
Proof.
  intros.
  rewrite Var.Map.FSetProperties.singleton_b.
  auto.
Qed.
#[global] Hint Rewrite singleton_mem_iff : var_db.



Lemma EPP_subst_eq : forall A C P x v,
    EPP A C P ->
    EPP A (Choreography.subst A x v C) (Process.subst x v P).
Proof.
  intros ? ? ? ? ? H.
  induction H; subst; simpl;
    Actor.simplify;
    Var.simplify;
    simpl;
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
    2:{ rewrite actors_subst; auto. }
    rewrite rebound_not_in_I in H; auto.
    apply IHC in H.
    destruct H as [P [H ?]]; subst.
    exists P; split; auto.
    apply EPP_disjoint; auto.
  }

  destruct I as 
    [A0 v0 B0 y0 | A0 x0 B0 y0 | A0 x0 v0 | A0 x0 v0 | A0 x0 y0 v0];
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




Definition insn_matches_label (I : Choreography.Insn.t) (l : Label.t) : bool :=
  match I, l with
  | Choreography.Insn.Send A _ B _, Label.Send A' _ B'
  | Choreography.Insn.EPR A _ B _, Label.EPR A' B' =>
    if Actor.eq_dec A A'
    then if Actor.eq_dec B B' then true else false
    else false
  | Choreography.Insn.Let A _ _, Label.Loc A'
  | Choreography.Insn.LetBang A _ _, Label.Loc A'
  | Choreography.Insn.LetPair A _ _ _, Label.Loc A' =>
    if Actor.eq_dec A A' then true else false

  | _, _ => false
  end.

(** Return the choreography C' such that C, refs -l-> C', refs'
  * if such a choreography exists.
  *)
Inductive step_label : Choreography.t -> ChorEnv.t nat ->
                       Label.t ->
                       Choreography.t -> Prop :=

| StepSend : forall A v B x C refs A' v' B' C',
  A = A' ->
  B = B' ->
  v = v' ->
  Expr.Val v ->
  C' = Choreography.subst B x v C ->
  step_label  (Choreography.Insn.Send A v B x :: C)
              refs
              (Label.Send A' v' B')
              C'

| StepEPR : forall q1 q2 A x B y C refs A' B' C',
  A = A' ->
  B = B' ->
  q1 = Var.fresh (ChorEnv.find A refs) ->
  q2 = Var.fresh (Var.Map.add x q1 (ChorEnv.find A refs)) ->

  C' = Choreography.subst A x (Expr.Var q1)
        (Choreography.subst B y (Expr.Var q2)
        C) ->

  step_label  (Choreography.Insn.EPR A x B y :: C)
              refs
              (Label.EPR A' B')
              C'

| StepLet :forall A x v C refs A' C',
  A = A' ->
  C' = Choreography.subst A x v C ->
  step_label (Choreography.Insn.Let A x v :: C)
             refs
             (Label.Loc A')
             C'

| StepLetBang : forall A x v' C refs A' C',
  A = A' ->
  C' = Choreography.subst A x v' C ->
  step_label (Choreography.Insn.LetBang A x (Expr.Bang v') :: C)
             refs
             (Label.Loc A')
             C'

| StepLetPair : forall A x1 x2 v1 v2 C refs A' C',
  A = A' ->
  C' = Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C) ->
  step_label (Choreography.Insn.LetPair A x1 x2 (Expr.Pair v1 v2) :: C)
             refs
             (Label.Loc A')
             C'

| StepCons : forall I C refs l C',
  Actor.FSet.Empty
    (Actor.FSet.inter (Choreography.Label.actors l)
                      (Choreography.Insn.actors I)) ->
  step_label C refs l C' ->
  step_label (I :: C) refs l (I :: C')
.

(*
Fixpoint step_label l (refs : Var.Map.t nat) C :=
  match C with
  | [] => []
  | I0 :: C' =>

    match I0 with

    | Choreography.Insn.Send A v B y =>
      if insn_matches_label I0 l
      then Choreography.subst B y v C'
      else I0 :: step_label l refs C'

    | Choreography.Insn.EPR A x B y =>
      let q1 := Var.fresh refs in
      let refs' := Var.Map.add x q1 refs in
      let q2 := Var.fresh refs' in
      let refs'' := Var.Map.add y q2 refs' in

      if insn_matches_label I0 l
      then  Choreography.subst A x (Expr.Var q1)
            (Choreography.subst B y (Expr.Var q2)
            C')
      else I0 :: step_label l refs'' C'

    | Choreography.Insn.Let A x v =>
      if insn_matches_label I0 l
      then Choreography.subst A x v C'
      else I0 :: step_label l refs C'

    | Choreography.Insn.LetBang A x (Expr.Bang v') =>
      if insn_matches_label I0 l
      then Choreography.subst A x v' C'
      else I0 :: step_label l refs C'

    | Choreography.Insn.LetPair A x1 x2 (Expr.Pair v1 v2) =>
      if insn_matches_label I0 l
      then Choreography.subst A x1 v1
          (Choreography.subst A x2 v2 C')
      else I0 :: step_label l refs C'

    | _ => I0 :: step_label l refs C'

    end
  end.
  *)

(*
(** Return the choreography C' such that C -(Send A v B y)-> C' *)
Fixpoint step_send A B (C : Choreography.t) : Choreography.t :=
    match C with
    | [] => []
    | Choreography.Insn.Send A0 v0 B0 y0 :: C' =>
        match Actor.eq_dec A A0, Actor.eq_dec B B0 with
        | left _, left _ => Choreography.subst B0 y0 v0 C'
        | _, _ => Choreography.Insn.Send A0 v0 B0 y0 :: (step_send A B C')
        end
    | I' :: C' => I' :: step_send A B C'
    end.
  *)


(* Can take a step with label l *)
Inductive Ready : Choreography.t -> ChorEnv.t nat -> Config.t -> Label.t -> Prop := .
Lemma ready_spec : forall C refs cfg l,
  Ready C refs cfg l ->
  exists C' refs' cfg',
    Choreography.step C refs cfg l C' refs' cfg'.
Admitted.

Lemma step_ready : forall N refs cfg l N' refs' cfg' C,
  Network.step N refs cfg l N' refs' cfg' ->
  EPP_N C N ->
  Ready C refs cfg l.
Admitted.

Lemma EPP_N_step_deterministic :
  forall C N refs cfg l C' refs' cfg' N' refs'' cfg'',
  EPP_N C N ->
  Choreography.step C refs cfg l C' refs' cfg' ->
  Network.step N refs cfg l N' refs'' cfg'' ->
  ChorEnv.Equal refs' refs''
  /\
  cfg' = cfg'
  /\
  EPP_N C' N'.
Proof.
  intros C N refs cfg l C' refs' cfg' N' refs'' cfg''.
  intros HEPP_N HstepC HstepN.
  inversion HstepC; subst; clear HstepC.
  * (* SendC *)
    inversion HstepN; subst; clear HstepN.
    admit (* need a version for steps of processes *).
  * (* Send A v B *)
    inversion HstepN; subst; clear HstepN.
    split; auto. admit (*reflexivity.*).
    split; auto.
    apply EPP_N_spec.
    rewrite EPP_N_spec in HEPP_N.
    intros D PD Hmapsto.
    Actor.simplify.
    destruct Hmapsto as [[? ?] | [? [[? ?] | [? Hmapsto]]]];
      subst.
    + (* A = D *)
      apply EPP_subst_neq; auto.
      apply HEPP_N in H4.
      inversion H4; subst; clear H4; auto.
      { simpl in *; Actor.simplify. }
    + (* B = D *)
      apply HEPP_N in H8.
      inversion H8; subst; clear H8.
      apply EPP_subst_eq; auto.
      { simpl in *; Actor.simplify. }
    + (* A <> D /\ B <> D *)
      apply EPP_subst_neq; auto.
      apply HEPP_N in Hmapsto.
      apply EPP_disjoint_inversion in Hmapsto; auto.
      { simpl; Actor.simplify. }


  * admit.
  * (* Let *) admit.
Admitted. 

Definition setminus {T} (S : Actor.FSet.t) (N : Actor.Map.t T) : Actor.Map.t T :=
  Actor.FSet.fold (fun x N' => Actor.Map.remove x N') S N.
Lemma setminus_mapsto_iff : forall {A} x (a : A) X m,
  Actor.Map.MapsTo x a (setminus X m)
  <->
  ~ Actor.FSet.In x X /\ Actor.Map.MapsTo x a m.
Admitted.
#[global] Hint Rewrite @setminus_mapsto_iff : actor_db.

Global Instance setminusProper : forall T, Proper (Actor.FSet.Equal ==> @Actor.Map.Equal T ==> @Actor.Map.Equal T) setminus.
Admitted.


Lemma dec_In : forall x X, 
  { Actor.FSet.In x X } + { ~ Actor.FSet.In x X }.
Admitted.

Lemma EPP_N_cons : forall I C N ,
  EPP_N (I :: C) N <->
  (forall A PA,
    Actor.FSet.In A (Choreography.Insn.actors I) ->
    Actor.Map.MapsTo A PA N ->
    EPP A (I :: C) PA
  ) /\
  EPP_N C (setminus (Choreography.Insn.actors I) N).
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
    destruct (dec_In D (Choreography.Insn.actors I))
      as [Hin | Hin].
    + apply HA; auto.
    + apply EPP_disjoint; auto.
      apply HC; auto.
      Actor.simplify.
Qed.

(*
Lemma EPP_N_cons_1 : forall C I A N,
  Actor.FSet.Equal
    (Choreography.Insn.actors I)
    (Actor.FSet.singleton A)
    ->
  EPP_N (I :: C) N
  <->
  (forall PA,
    Actor.Map.MapsTo A PA N ->
    EPP A (I :: C) PA)
  /\
  EPP_N C (Actor.Map.remove A N).
Admitted.
Lemma EPP_N_cons_2 : forall C I A B N,
  Actor.FSet.Equal
    (Choreography.Insn.actors I)
    (Actor.FSet.add A (Actor.FSet.singleton B))
    ->
  EPP_N (I :: C) N
  <->
  (forall PA,
    Actor.Map.MapsTo A PA N ->
    EPP A (I :: C) PA)
  /\
  (forall PB,
    Actor.Map.MapsTo B PB N ->
    EPP B (I :: C) PB)
  /\
  EPP_N C (Actor.Map.remove B (Actor.Map.remove A N)).
Admitted.

Ltac EPP_N_cons :=
  match goal with
  | [H : EPP_N (Choreography.Insn.Send _ _ _ _ :: _) _ |- _] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    rewrite EPP_N_cons_2 in H; [ | simpl; reflexivity];
    destruct H as [HA [HB H]]
  | [H : EPP_N (Choreography.Insn.EPR _ _ _ _ :: _) _ |- _] =>
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    rewrite EPP_N_cons_2 in H; [ | simpl; reflexivity];
    destruct H as [HA [HB H]]
  | [ H : EPP_N (_ :: _) _ |- _ ] =>
    let HA := fresh "HA" in
    rewrite EPP_N_cons_1 in H; [ | simpl; reflexivity];
    destruct H as [HA H]
  | [ |- EPP_N (Choreography.Insn.Send ?A _ ?B _ :: _) _ ] =>
    eapply EPP_N_cons_2; [ simpl; reflexivity | ];
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    repeat split; [intros ? HA | intros ? HB | ]; Actor.simplify
  | [ |- EPP_N (Choreography.Insn.EPR _ _ _ _ :: _) _ ] =>
    eapply EPP_N_cons_2; [ simpl; reflexivity | ];
    let HA := fresh "HA" in
    let HB := fresh "HB" in
    repeat split; [intros ? HA | intros ? HB | ]; Actor.simplify
  | [ |- EPP_N (_ :: _) _ ] =>
    eapply EPP_N_cons_1; [ simpl; reflexivity | ];
    let HA := fresh "HA" in
    repeat split; [intros ? HA | ]; Actor.simplify
  end.
  *)

Ltac EPP_N_cons :=
  match goal with
  | [H : EPP_N (_ :: _) _ |- _] =>
    rewrite EPP_N_cons in H;
    simpl in H; Actor.simplify
  | [ |- EPP_N (_ :: _) _ ] =>
    eapply EPP_N_cons;
    repeat split; intros; simpl; Actor.simplify
  end.
Lemma remove_remove : forall T A (m : Actor.Map.t T),
  Actor.Map.Equal
    (Actor.Map.remove A (Actor.Map.remove A m))
    (Actor.Map.remove A m).
Admitted.
#[global] Hint Rewrite remove_remove : actor_db.

Lemma EPP_N_subst_neq : forall A x e C N,
  ~ Actor.Map.In A N ->
  EPP_N (Choreography.subst A x e C) N
  <->
  EPP_N C N.
Admitted.


Lemma setminus_add : forall T A X (N: Actor.Map.t T),
  Actor.Map.Equal
    (setminus (Actor.FSet.add A X) N)
    (setminus X (Actor.Map.remove A N)).
Admitted.
#[global] Hint Rewrite setminus_add : actor_db.
Lemma setminus_singleton : forall T A (N : Actor.Map.t T),
  Actor.Map.Equal
    (setminus (Actor.FSet.singleton A) N)
    (Actor.Map.remove A N).
Admitted.
#[global] Hint Rewrite setminus_singleton : actor_db.

Lemma completeness_local : forall PA (refs : Var.Map.t nat) cfg PA' refs' cfg',
  Process.step PA refs cfg PA' refs' cfg' -> 
  forall A N C (Θ : ChorEnv.t nat) Θ',
  EPP_N C N ->
  Actor.Map.MapsTo A PA N ->
  Var.Map.Equal refs (ChorEnv.find A Θ) ->
  ChorEnv.Equal Θ' (Actor.Map.add A refs' Θ) ->
  
  exists C',
    Choreography.step C Θ cfg (Label.Loc A) C' Θ' cfg'
    /\
    EPP_N C' (Actor.Map.add A PA' N).
Proof.
  intros ? ? ? ? ? ? Hstep A N C Θ Θ' HEPP_N Hmapsto Hrefs HΘ'.
  rewrite EPP_N_spec in HEPP_N.
  apply HEPP_N in Hmapsto.
  rewrite <- EPP_N_spec in HEPP_N.
  revert N HEPP_N.
  revert refs cfg PA' refs' cfg' Hstep Hrefs HΘ'.
  induction Hmapsto;
    intros refs cfg PA' refs' cfg' Hstep Hrefs HΘ' N HEPP_N;
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
        replace Θ' with Θ by admit. (* Equivalence relations *)
        eapply Choreography.LetB; auto.
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
        replace Θ' with Θ by admit. (* Equivalence relations *)
        eapply Choreography.LetBangB; auto.
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
        replace Θ' with Θ by admit. (* Equivalence relations *)
        eapply Choreography.LetPairB; eauto.
      }
      {
        eapply (EPP_N_add _ A).
        { Actor.simplify. }
        { admit (* swap order of substitutions *). }
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
    specialize (IHHmapsto _ _ _ _ _ Hstep Hrefs HΘ' 
                  (Actor.Map.add A P N)).
    destruct IHHmapsto as [C' [IHstep IHEPP_N]].
    {
      eapply (EPP_N_add _ A); eauto;
        Actor.simplify.
      admit (* true *).
    }
    Actor.simplify.
    exists (I :: C').
    split.
    {
      constructor; auto.
      intros Z. simpl. Actor.simplify.
      intros [? ?]; subst; try contradiction.
    }
    eapply (EPP_N_add _ A).
    { Actor.simplify. }
    {
      rewrite EPP_N_spec in IHEPP_N.
      apply EPP_disjoint; auto.
      apply IHEPP_N.
      Actor.simplify.
    }
    Actor.simplify.
    admit (* true *).
Admitted.

Lemma completeness_send : forall N refs cfg A v B N' refs' cfg' C,
  Network.step N refs cfg (Label.Send A v B) N' refs' cfg' ->
  EPP_N C N ->
  exists C',
    Choreography.step C refs cfg (Label.Send A v B) C' refs' cfg'  /\
    EPP_N C' N'.
Proof.
  intros.
  inversion H; subst; clear H.
  dependent induction C.
  {
    (* absurd *) admit.
  }
  rename a into I.
  EPP_N_cons.
  assert (HI : I = Choreography.Insn.Send A v B y
    \/ (~ Actor.FSet.In A (Choreography.Insn.actors I)
     /\ ~ Actor.FSet.In B (Choreography.Insn.actors I))).
  admit.
  destruct HI as [? | [HA HB]]; subst.
  + exists (Choreography.subst B y v C).
    simpl in *.
    split.
    { constructor; auto. }
    eapply (EPP_N_add _ A).
    { Actor.simplify. }
    {
      apply EPP_subst_neq; auto.
      admit (*? *).
    }
    Actor.simplify.
    admit.
  + edestruct IHC as [C' [IHstep IHEPP_N]]; eauto.
    { admit (* true? *). }
    exists (I :: C').
    split.
    { constructor; auto.
      {
        intros D. simpl. Actor.simplify.
        intuition; subst; try contradiction.
      }
    }
    {
      EPP_N_cons.
      { admit. }
      admit.
    }
Admitted.


Theorem completeness : forall N refs cfg l N' refs' cfg',

    Network.step N refs cfg l N' refs' cfg' ->

    forall C,
    EPP_N C N ->
    exists C', EPP_N C' N' /\
                Choreography.step C refs cfg l C' refs' cfg'.
Proof.
    intros N refs cfg l N' refs' cfg' Hstep C HEPP.
    destruct l as [A v B | A B | A ].


    * (* send *)
      eapply completeness_send in Hstep; eauto.
      destruct Hstep as [C' [Hstep HEPP_N]].
      exists C'; auto.

    * (* EPR *)  admit.
  
    * (* local step *)
      inversion Hstep; subst; clear Hstep.
      eapply completeness_local in H1; eauto;
        try reflexivity.
      destruct H1 as [C0 [Hstep HEPP_N]].
      exists C0. split; auto.

Admitted.


Lemma step_label_sound : forall C refs l C',
  step_label C refs l C' ->
  forall cfg, exists refs' cfg',
  Choreography.step C refs cfg l C' refs' cfg'.
Proof.
  induction C as [ | I C];
    intros refs l C' Hstep cfg.
  { inversion Hstep. }
  inversion Hstep; subst; clear Hstep.

  * exists refs; exists cfg.
    constructor; auto.

  * destruct (Config.epr (ChorEnv.find A' refs) cfg) 
      as [[[q1 q2] refsA'] cfgA'] eqn:Hepr.
  
    exists (Actor.Map.add A' refsA' refs).
    exists cfgA'.
    econstructor; simpl; auto.
    unfold ChorEnv.epr.
    unfold Config.epr in Hepr.
    destruct (Config.epr_cfg cfg) as [[q1' q2'] cfg'] eqn:Hepr'.
    inversion Hepr; subst; clear Hepr.
Admitted.
  

  
Lemma step_send_complete : forall C A v y B PA PB refs cfg C',
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    Expr.Val v ->
    step_label C refs (Label.Send A v B) C' ->
    Choreography.step C refs cfg (Label.Send A v B)
                      C' refs cfg.
Proof.
    induction C as [ | I C];
        intros A v y B PA PB refs cfg C' HEPPA HEPPB Hval Hstep.
    { contradict HEPPA. simpl; inversion 1. }
    inversion Hstep; subst; clear Hstep.

    inversion HEPPA; subst; clear HEPPA;
    inversion HEPPB; subst; clear HEPPB;
      simpl in *;
      Actor.simplify.
    * (* send *)
      apply Choreography.SendB; auto.
        
    * apply Choreography.Delay; auto.
        match goal with
        | [ H : Actor.FSet.Empty _ |- _ ] =>
          rename H into Hempty
        end.
    (*
      assert (Hin : ~ (Actor.FSet.In A (Choreography.Insn.actors I)) /\ ~ ).
      {
        intros Hin.
        match goal with
        | [ H : Actor.FSet.Empty _ |- _ ] =>
          specialize (H A);
          simpl in H;
          Actor.simplify
        end.
      }
        *)
      apply EPP_disjoint_inversion in HEPPA; auto.
      2:{
        specialize (Hempty A);
        simpl in *;
        Actor.simplify.
      }
      apply EPP_disjoint_inversion in HEPPB; auto.
      2:{
        specialize (Hempty B);
        simpl in *;
        Actor.simplify.
      }
      eapply IHC; eauto.
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


Lemma EPP_cons : forall A I C1 C2,
  (forall P, EPP A C1 P -> EPP A C2 P) ->
  (forall P, EPP A (I :: C1) P -> EPP A (I :: C2) P).
Proof.
  intros A I C1 C2 H P H'.
  inversion H'; subst; clear H';
    try (constructor; auto; fail).
Qed.

Lemma EPP_cons_iff : forall A I C1 C2,
  (forall P, EPP A C1 P <-> EPP A C2 P) ->
  (forall P, EPP A (I :: C1) P <-> EPP A (I :: C2) P).
Proof.
  intros A I C1 C2 H P.
  split; apply EPP_cons; apply H.
Qed.

Lemma step_label_neq : forall refs l D C C' PD,
      step_label C refs l C' ->
      ~ Actor.FSet.In D (Label.actors l) ->
      EPP D C' PD <-> EPP D C PD.
Proof.
  intros ? ? ? ? ? ? Hstep.
  revert D PD.
  induction Hstep; intros D PD;
    subst; simpl; intros Hin; Actor.simplify.
  * rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    rewrite EPP_subst_iff.
    intuition.

  * remember (Var.fresh (ChorEnv.find A' refs)) as q1.
    remember (Var.fresh (Var.Map.add x q1 (ChorEnv.find A' refs))) as q2.
  
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.

  * 
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.

  * 
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.

  * 
    rewrite EPP_disjoint_iff; auto.
    2:{ simpl; Actor.simplify. }
    repeat rewrite EPP_subst_iff.
    intuition.
    
  * 
    apply EPP_cons_iff.
    intros P. apply IHHstep; auto.
Qed.

Lemma step_send_EPP : forall C A B PA PB v y refs D PD,
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    A <> B ->
    forall C',
    step_label C refs (Label.Send A v B) C' ->

    EPP D C' PD
    <->
    (D = A /\ PD = PA)
    \/
    (D = B /\ PD = Process.subst y v PB)
    \/
    (D <> A /\ D <> B /\ EPP D C PD).
Proof.
  intros C A B PA PB v y refs D PD HA HB Hneq.
  induction C as [ | I C];
    intros C' Hstep;
    simpl in *;
    inversion Hstep; subst; clear Hstep.

  * (* substitution happens here *)
    rewrite EPP_subst_iff; auto.
    inversion HA; subst; clear HA; auto.
    2:{ (* contradiction *)
      simpl in *; Actor.simplify.
    }
    inversion HB; subst; clear HB; auto.
    2:{ (* contradiction *)
      simpl in *; Actor.simplify.
    }
    clear H3 H4 H11 H7.
    split; intros H.
    + compare D A; [ | compare D B].
      - left. split; auto.
        destruct H as [ [PD0 [P0 [HPD0 ?]]] | [? HPD0]]; subst;
          try contradiction.
        eapply EPP_deterministic; eauto.
      - right. left.
        split; auto.
        destruct H as [ [PD0 [P0 [HPD0 ?]]] | [? HPD0]]; subst;
          try contradiction.
        f_equal.
        eapply EPP_deterministic; eauto.
      - right. right.
        split; auto. split; auto.
        destruct H as [ [PD0 [P0 [HPD0 ?]]] | [? HPD0]]; subst;
          try contradiction.
        constructor; auto.
        simpl; Actor.simplify.

    + destruct H as [[? ?] | [ [? ?] | [? [? ?]] ]]; subst.
      - right. split; auto.
      - left. split; auto. exists PB. split; auto.
      - right. split; auto.
        apply EPP_disjoint_inversion in H1; auto.
        simpl; Actor.simplify.

  * (* substitution happens later *)
    assert (~ Actor.FSet.In A (Choreography.Insn.actors I)).
    {
      intros Hin;
      match goal with
      | [ H0 : Actor.FSet.Empty _ |- _ ] => 
        apply (H0 A)
      end.
      simpl; Actor.simplify.
    }
    assert (~ Actor.FSet.In B (Choreography.Insn.actors I)).
    {
      intros Hin;
      match goal with
      | [ H0 : Actor.FSet.Empty _ |- _ ] => 
        apply (H0 B)
      end.
      simpl; Actor.simplify.
    }
    clear H1.
    apply EPP_disjoint_inversion in HA; auto.
    apply EPP_disjoint_inversion in HB; auto.

    match goal with
    | [ Hstep0 : step_label C _ _ _ |- _ ] =>
      set (IH := IHC HA HB _ Hstep0); eauto;
      rename Hstep0 into Hstep
    end.

    compare D A; [ | compare D B].
    - (* D = A *)
      transitivity (EPP D C'0 PD).
      { apply EPP_disjoint_iff; auto. }
      rewrite IH.
      intuition.

    - (* D = B *)
      transitivity (EPP D C'0 PD).
      { apply EPP_disjoint_iff; auto. }
      rewrite IH.
      intuition.

    - (* D <> A /\ D <> B *)
      transitivity (EPP D (I :: C) PD).
      2:{ intuition. }

      eapply (step_label_neq refs (Label.Send A v B)).
      2:{ simpl; Actor.simplify. }
      apply StepCons; auto.
      { intros Z. simpl. Actor.simplify.
        intros [[? | ?] Hin']; subst; try contradiction.
      }
Qed.



Lemma subst_neq_inversion : forall A x v D C P,
  D <> A ->
  EPP D (Choreography.subst A x v C) P ->
  EPP D C P.
Proof.
  intros ? ? ? ? C.
  induction C as [ | I C]; intros P Hneq H;
    simpl in H;
    auto.
  inversion H; subst; clear H;
    try match goal with
    | [ Hsubst : _ = Choreography.Insn.subst _ _ _ I |- _ ] =>
    destruct I; simpl in *;
    inversion Hsubst; subst; clear Hsubst
    end.
  * Actor.Map.Tactics.compare A t.
    constructor; auto.
    Actor.simplify; auto.
    Var.simplify; auto.
  * constructor; auto.
    Actor.simplify; auto.
  * constructor; auto;
    Actor.simplify; auto;
    Var.simplify; auto.
  * constructor; auto.
    Actor.simplify; auto;
    Var.simplify; auto.
  * Actor.Map.Tactics.compare A t.
    apply EPP_Let; auto.
  * Actor.Map.Tactics.compare A t.
    constructor; auto.
  * Actor.Map.Tactics.compare A t.
    constructor; auto.
  * rewrite actors_subst in *.
    apply EPP_disjoint; auto.
    destruct (Choreography.Insn.rebound_in A x I) eqn:Hbound;
      auto.
Qed.


Lemma step_send_EPP_N : forall C A B PA PB y v N refs C',
    EPP_N C N ->
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    Expr.Val v ->
    A <> B ->
    step_label C refs (Label.Send A v B) C' ->
    EPP_N C' (Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N)).
Proof.
  intros.
  apply (EPP_N_add C' A PA);
    Actor.simplify.
  { eapply step_send_EPP; eauto. }
  apply (EPP_N_add C' B (Process.subst y v PB));
    Actor.simplify.
  { eapply step_send_EPP; eauto. }

  apply EPP_N_spec.
  intros D PD Hmapsto.
  Actor.simplify. rename H7 into Hmapsto.
  rewrite EPP_N_spec in H.
  eapply step_label_neq; eauto.
  { simpl; Actor.simplify. }
Qed.

Lemma EPP_N_subst_neq : forall A x v C N,
  EPP_N C N ->
  ~ Actor.Map.In A N ->
  EPP_N (Choreography.subst A x v C) N.
Proof.
  intros A x v C N HEPP Hin.
  rewrite EPP_N_spec in *.
  intros D PD Hmapsto.
  compare A D.
  {
    exfalso. apply Hin. exists PD; auto.
  }
  apply EPP_subst_neq; auto.
Qed.

Lemma step_let_EPP : forall A C x v PA refs D PD,
    EPP A C (Insn.Let x v :: PA) ->
    forall C',
    step_label C refs (Label.Loc A) C' ->
    EPP D C' PD
    <->
    (D = A /\ PD = Process.subst x v PA)
    \/
    (D <> A /\ EPP D C PD).
Proof.
  intros A C x v PA refs.
  induction C as [ | I N ];
    intros D PD HEPPA C' Hstep.
  { inversion Hstep; subst; clear Hstep. }
  compare A D.
  2:{
    rewrite step_label_neq; eauto.
    2:{ simpl; Actor.simplify. }
    intuition.
  }
  transitivity (PD = Process.subst x v PA).
  2:{ intuition. }
  
  assert (Hdec : Actor.FSet.In A (Choreography.Insn.actors I)
    \/ ~ Actor.FSet.In A (Choreography.Insn.actors I)).
  {
    destruct I; simpl; Actor.simplify.
  }
  destruct Hdec as [Hin | Hin].
  2:{
    apply EPP_disjoint_inversion in HEPPA; auto.
    inversion Hstep; subst; clear Hstep;
      simpl in *; Actor.simplify.
    rewrite EPP_disjoint_iff; auto.
    rewrite IHN; eauto.
    tauto.
  }
  {
    inversion Hstep; subst; clear Hstep;
    inversion HEPPA; subst; clear HEPPA;
      simpl in *; Actor.simplify.
    2:{
      match goal with
      | [ H : Actor.FSet.Empty _ |- _ ] => contradict H
      end.
      intros Hempty. apply (Hempty A0).
      Actor.simplify.
    }
    rewrite EPP_subst_iff.
    split.
      {
        intros [[_ [PD0 [? ?]]] | [? ?]];
          subst; try contradiction.
        f_equal.
        eapply EPP_deterministic; eauto.
      }
      {
        intros; subst.
        left. split; auto.
        exists PA; auto.
      }

  }
Qed.


(*
(** Return the choreography C' such that C, refs, cfg' -(EPR A x B y)-> C' in the configuration cfg *)
Fixpoint step_epr A B refs cfg (C : Choreography.t) : Choreography.t :=
    match C with
    | [] => []
    | Choreography.Insn.EPR A0 x0 B0 y0 :: C' =>
        match Actor.eq_dec A A0, Actor.eq_dec B B0 with
        | left _, left _ => 
            match ChorEnv.epr A B refs cfg with
            | (q1,q2,refs',cfg') =>
                Choreography.subst A x0 (Expr.Var q1)
                (Choreography.subst B y0 (Expr.Var q2)
                C')
            end
        | _, _ =>
            Choreography.Insn.EPR A0 x0 B0 y0 :: (step_epr A B refs cfg C')
        end
    | I' :: C' => I' :: step_epr A B refs cfg C'
    end.

Lemma step_epr_complete : forall C A x y B PA PB,
    EPP A C (Insn.EPR x B :: PA) ->
    EPP B C (Insn.EPR y A :: PB) ->
    forall refs cfg q1 q2 refs' cfg',
        ChorEnv.epr A B refs cfg = (q1,q2,refs', cfg') ->
        Choreography.step   C refs cfg
                            (Label.EPR A B)
                            (step_epr A B refs cfg C) refs' cfg'.
Admitted.

Lemma step_epr_EPP_N : forall A B C PA PB x y N refs cfg q1 q2 refs' cfg',
    EPP_N C N ->
    EPP A C (Insn.EPR x B :: PA) ->
    EPP B C (Insn.EPR y A :: PB) ->
    ChorEnv.epr A B refs cfg = (q1, q2, refs', cfg') ->
    EPP_N (step_epr A B refs cfg C)
        (Actor.Map.add A (Process.subst x (Expr.Var q1) PA)
            (Actor.Map.add B (Process.subst y (Expr.Var q2) PB) N)).
Admitted.
*)

Theorem completeness : forall N refs cfg l N' refs' cfg',

    Network.step N refs cfg l N' refs' cfg' ->

    forall C,
    EPP_N C N ->
    exists C', EPP_N C' N' /\
                Choreography.step C refs cfg l C' refs' cfg'.
Proof.
    intros N refs cfg l N' refs' cfg' Hstep.
    induction Hstep; intros C HEPP; subst.
  
    * (* local step *)
      admit.

    * (* send *)
      rewrite EPP_N_spec in HEPP.
      apply HEPP in H0.
      apply HEPP in H1.
      exists (step_send A B C).
      split.
      { apply step_send_EPP_N; auto. }
      { eapply step_send_complete; eauto. }

    * (* EPR *) 
      apply HEPP in H0; destruct H0 as [_ HEPPA].
      apply HEPP in H1; destruct H1 as [_ HEPPB].
      exists (step_epr A B refs cfg C).
      split.
      { eapply step_epr_EPP_N; eauto. }
      { eapply step_epr_complete; eauto. }

Admitted.
