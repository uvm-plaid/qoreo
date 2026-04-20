From Qoreo Require Import Base.
Import Base.Tactics.
From Qoreo Require Expr Choreography.

Module Label := Choreography.Label.
Module Choreography := Choreography.Choreography.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Stdlib.Structures.Equalities.

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

    Inductive step : Process.t * Config.t -> Process.t * Config.t -> Prop :=
    | LetC : forall x e P ρ e' ρ',
        Expr.step (e, ρ) (e', ρ') ->
        step (Insn.Let x e :: P, ρ) (Insn.Let x e' :: P, ρ')
    | LetB : forall x v P ρ P',
        Expr.Val v ->
        P' = Process.subst x v P ->
        step (Insn.Let x v :: P, ρ) (P', ρ)

    | LetBangC : forall x e P ρ e' ρ',
        Expr.step (e, ρ) (e', ρ') ->
        step (Insn.LetBang x e :: P, ρ) (Insn.LetBang x e' :: P, ρ')
    | LetBangB : forall x e P ρ P',
        P' = Process.subst x e P ->
        step (Insn.LetBang x (Expr.Bang e) :: P, ρ) (P', ρ)

    | LetPairC : forall x1 x2 e P ρ e' ρ',
        Expr.step (e, ρ) (e', ρ') ->
        step (Insn.LetPair x1 x2 e :: P, ρ) (Insn.LetPair x1 x2 e' :: P, ρ')
    | LetPairP : forall x1 x2 v1 v2 P ρ P',
        Expr.Val v1 -> Expr.Val v2 ->
        P' = Process.subst x2 v2 (Process.subst x1 v1 P) ->
        step (Insn.LetPair x1 x2 (Expr.Pair v1 v2) :: P, ρ) (P', ρ)

    | SendC : forall e B P ρ e' ρ',
        Expr.step (e, ρ) (e', ρ') ->
        step (Insn.Send e B :: P, ρ) (Insn.Send e' B :: P, ρ')
    .

End Process.

Module Network.
    Definition t := Actor.Map.t (Process.t).

    Inductive step : Network.t * Config.t -> Label.t -> Network.t * Config.t -> Prop :=

    | Loc : forall P P' N cfg A N' cfg',
      Actor.Map.MapsTo A P N ->
      Process.step (P, cfg) (P', cfg') ->
      N' = Actor.Map.add A P' N ->
      step (N, cfg) (Label.Loc A) (N', cfg')

    | Send : forall PA PB y N cfg A v B N',
      A <> B ->
      Actor.Map.MapsTo A (Insn.Send v B :: PA) N ->
      Actor.Map.MapsTo B (Insn.Receive y A :: PB) N ->
      Expr.Val v ->
      N' = Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N) ->
      
      step (N, cfg) (Label.Send A v B) (N', cfg)

    | EPR : forall x y PA PB qA qB N cfg A B N' cfg',
      A <> B ->
      Actor.Map.MapsTo A (Insn.EPR x B :: PA) N ->
      Actor.Map.MapsTo B (Insn.EPR y A :: PB) N ->
      Config.epr cfg = (qA, qB, cfg') ->
      N' = Actor.Map.add A (Process.subst x (Expr.Var qA) PA) (
            Actor.Map.add B (Process.subst y (Expr.Var qB) PB) N) ->

      step (N, cfg) (Label.EPR A B) (N', cfg')
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
      | (left _, right _) => conso (Insn.Send e A2) (epp p C)
      | (right _, left _) => conso (Insn.Receive x A1) (epp p C)
      | _ => epp p C
      end
  | Choreography.Insn.EPR A1 x1 A2 x2 :: C =>
      match (Actor.eq_dec A1 p, Actor.eq_dec A2 p) with
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
| EPP_disjoint : forall A I C P,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A C P ->
  EPP A (I :: C) P

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
.

Lemma EPP_correct : forall A C P,
    EPP A C P <-> epp A C = Some P.
Admitted.

Definition EPP_N (C : Choreography.t) (N : Network.t) : Prop :=
    forall A PA,
        Actor.Map.MapsTo A PA N
        <->
        Actor.FSet.In A (Choreography.actors C)
        /\ EPP A C PA.

(* Correctness of EPP *)

Theorem soundness : forall C C' cfg cfg' l N,

    Choreography.step (C, cfg) l (C', cfg') ->
    EPP_N C N ->
    exists N', EPP_N C'  N' /\
               Network.step (N, cfg) l (N', cfg').
Admitted.

Require Import Stdlib.Program.Equality.


Lemma EPP_subst_neq : forall A C P B x v,
    A <> B ->
    EPP A C P ->
    EPP A (Choreography.subst B x v C) P.
Admitted.

Lemma EPP_subst_eq : forall A C P x v,
    EPP A C P ->
    EPP A (Choreography.subst A x v C) (Process.subst x v P).
Admitted.

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

Lemma step_send_complete : forall C A v y B PA PB,
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    Expr.Val v ->
    forall cfg,
        Choreography.step (C, cfg) (Label.Send A v B) (step_send A B C, cfg).
Proof.
    induction C as [ | I C'];
        intros A v y B PA PB HEPPA HEPPB Hval cfg.
    { contradict HEPPA. simpl; inversion 1. }
    inversion HEPPA; subst;
    inversion HEPPB; subst; simpl in *;
        autorewrite with actor_db in *.
    * destruct I as   [ (*Send*) A0 v0 B0 y0
                    | (*EPR*)  A0 x0 B0 y0
                    | (*Let*)  A0 x0 e0
                    | (*Let!*) A0 x0 e0
                    | (*LetPair *) A0 x0 y0 e0
      ];
        simpl in *; autorewrite with actor_db in *.
      + destruct (Actor.eq_dec A A0); try (subst; firstorder; fail). 
        apply Choreography.Delay.
        { eapply IHC'; eauto. }
        { simpl; intros D. autorewrite with actor_db. 
          intros [[? | ?] [? | ?]]; subst; firstorder.
        }
      + apply Choreography.Delay.
        { eapply IHC'; eauto. }
        { simpl; intros D. autorewrite with actor_db. 
          intros [[? | ?] [? | ?]]; subst; firstorder.
        }

      + apply Choreography.Delay.
        { eapply IHC'; eauto. }
        { simpl; intros D. autorewrite with actor_db. 
          intros [[? | ?] ?]; subst; firstorder.
        }
      + apply Choreography.Delay.
        { eapply IHC'; eauto. }
        { simpl; intros D. autorewrite with actor_db. 
          intros [[? | ?] ?]; subst; firstorder.
        }
      + apply Choreography.Delay.
        { eapply IHC'; eauto. }
        { simpl; intros D. autorewrite with actor_db. 
          intros [[? | ?] ?]; subst; firstorder.
        }

    * absurd (A=A); auto.
    * absurd (B=B); auto.
    
    * repeat rewrite Actor.eq_dec_refl.
      constructor; auto.
Qed.

Lemma step_send_EPP_A : forall A B C PA PB v y,
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    EPP A (step_send A B C) PA.
Admitted.
Lemma step_send_EPP_B : forall A B C PA PB v y,
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    EPP B (step_send A B C) PB.
Admitted.
Lemma step_send_EPP_other : forall C D A B PD,
        D <> A ->
        D <> B ->
        EPP D (step_send A B C) PD <-> EPP D C PD.
Proof.
    induction C as [ | I C'];
        intros D A B PD HDA HDB.
    { simpl. reflexivity. }
    simpl. split; intros H.
    * admit.
    *
    destruct I as   [ (*Send*) A0 v0 B0 y0
                    | (*EPR*)  A0 x0 B0 y0
                    | (*Let*)  A0 x0 e0
                    | (*Let!*) A0 x0 e0
                    | (*LetPair *) A0 x0 y0 e0
    ].
Admitted.

Lemma step_send_EPP_N : forall A B C PA PB y v N,
    EPP_N C N ->
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    EPP_N (step_send A B C) (Actor.Map.add A PA (Actor.Map.add B (Process.subst y v PB) N)).
Proof.
    intros A B C PA PB y v N EPPN EPPA EPPB.
    intros D PD.
    split; intros HIn;
        repeat rewrite Actor.MapFacts.F.add_mapsto_iff in *.
    * admit.
    * destruct HIn as [HIn EPPD].
      destruct (Actor.eq_dec A D).
      { left. subst; split; auto.  admit. }
      { right. split; auto. admit. }
      (* Might need a different definition of EPP_N. *)
Admitted.
      

(*
Lemma send_complete : forall C A v y B PA PB,
    EPP A C (Insn.Send v B :: PA) ->
    EPP B C (Insn.Receive y A :: PB) ->
    Expr.Val v ->
    exists C', 
        (forall cfg,
            Choreography.step (C, cfg) (Label.Send A v B) (C', cfg))
        /\ EPP A C' PA
        /\ EPP B C' (Process.subst y v PB)
        /\ forall D PD, D <> A -> D <> B -> EPP D C' PD <-> EPP D C PD.
Proof.
    induction C as [ | I C'];
        intros A v y B PA PB HEPPA HEPPB Hval.
    { contradict HEPPA. simpl; inversion 1. }
    destruct I as   [ (*Send*) A0 v0 B0 y0
                    | (*EPR*)  A0 x0 B0 y0
                    | (*Let*)  A0 x0 e0
                    | (*Let!*) A0 x0 e0
                    | (*LetPair *) A0 x0 y0 e0
    ].
    * inversion HEPPA; inversion HEPPB; subst;
        try contradiction.
      + exists (Choreography.subst B y v C').
        split; [ | split; [ | split]].
        2:{ apply EPP_subst_neq; auto. }
        2:{ apply EPP_subst_eq; auto. }
        { constructor; auto. }
        {
            intros D PD HDA0 HDB0.
        }

      +  destruct (IHC' A v y B PA PB) as [C0' [IHEPPA [IHEPPB IHC0']]]; auto.
         exists (Choreography.Insn.Send A0 v0 B0 y0 :: C0'); intros.
         repeat split; intros.
         { apply EPP_send_other; auto. }
         { apply EPP_send_other; auto. }
         {
            apply Choreography.Delay; auto.
            intros D.
            rewrite Actor.FSetFacts.inter_iff.
            simpl.
            repeat rewrite Actor.FSetFacts.add_iff.
            repeat rewrite Actor.FSetFacts.singleton_iff.
            intros [[? | ?] [? | ?]]; subst; contradiction.
         }
    * (* TODO *)

Admitted.
*)


(** Return the choreography C' such that C -(EPR A x B y)-> C' in the configuration cfg *)
Fixpoint step_epr A B cfg (C : Choreography.t) : Choreography.t :=
    match C with
    | [] => []
    | Choreography.Insn.EPR A0 x0 B0 y0 :: C' =>
        match Actor.eq_dec A A0, Actor.eq_dec B B0 with
        | left _, left _ => 
            match Config.epr cfg with
            | (q1,q2,cfg') =>
                Choreography.subst A x0 (Expr.Var q1)
                (Choreography.subst B y0 (Expr.Var q2)
                C')
            end
        | _, _ =>
            Choreography.Insn.EPR A0 x0 B0 y0 :: (step_epr A B cfg C')
        end
    | I' :: C' => I' :: step_epr A B cfg C'
    end.

Lemma step_epr_complete : forall C A x y B PA PB,
    EPP A C (Insn.EPR x B :: PA) ->
    EPP B C (Insn.EPR y A :: PB) ->
    forall cfg q1 q2 cfg',
        Config.epr cfg = (q1,q2,cfg') ->
        Choreography.step (C, cfg) (Label.EPR A B) (step_epr A B cfg C, cfg').
Admitted.

Lemma step_epr_EPP_N : forall A B C PA PB x y N cfg q1 q2 cfg',
    EPP_N C N ->
    EPP A C (Insn.EPR x B :: PA) ->
    EPP B C (Insn.EPR y A :: PB) ->
    Config.epr cfg = (q1, q2, cfg') ->
    EPP_N (step_epr A B cfg C)
        (Actor.Map.add A (Process.subst x (Expr.Var q1) PA)
            (Actor.Map.add B (Process.subst y (Expr.Var q2) PB) N)).
Admitted.

Theorem completeness : forall N cfg l N' cfg',

    Network.step (N, cfg) l (N', cfg') ->

    forall C,
    EPP_N C N ->
    exists C', EPP_N C' N' /\
                Choreography.step (C, cfg) l (C', cfg').
Proof.
    intros N cfg l N' cfg' Hstep.
    remember (N, cfg) as cfgN.
    remember (N', cfg') as cfgN'.
    generalize dependent cfg. generalize dependent cfg'.
    induction Hstep; intros cfg0' Hcfg0' cfg0 Hcfg0 C HEPP;
        inversion Hcfg0'; inversion Hcfg0;
        subst; clear Hcfg0' Hcfg0.
    
    * (* local step *) admit.
    * (* send *)
      apply HEPP in H0; destruct H0 as [_ HEPPA].
      apply HEPP in H1; destruct H1 as [_ HEPPB].
      exists (step_send A B C).
      split.
      { apply step_send_EPP_N; auto. }
      { eapply step_send_complete; eauto. }

    * (* EPR *) 
      apply HEPP in H0; destruct H0 as [_ HEPPA].
      apply HEPP in H1; destruct H1 as [_ HEPPB].
      exists (step_epr A B cfg0 C).
      split.
      { eapply step_epr_EPP_N; eauto. }
      { eapply step_epr_complete; eauto. }

Admitted.
