(**
Definition of process language and endpoint projection

Data structures

  - `Insn.t`, `Process.t`, `Network.t`: Definiton of choreographic instructions, processes, and networks respectively
  - `Process.step`, `Network.step` - small-step operational semantics
  - `epp` - Definition of endpoint projection as a function from choreographies and an actor name to a process.
  - `EPP` - Relational definition of endpoint projection
  - `EPP_N` - Relational definition of when a choreography is projected onto an entire network
  - `soundness` - Soundness of EPP; if a choreography can take a step, then so can the projected choreography
  - `completeness` - Completeness of EPP; if a projected choreography can take a step, then so can the unprojected choreography
  - `safety` - Well-typed choreographies project to safe and deadlock-free networks

*)



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

    Inductive stepC : t -> Var.Map.t nat -> Config.t -> t -> Var.Map.t nat -> Config.t -> Prop :=
    | LetC : forall x e refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        stepC (Insn.Let x e) refs ρ (Insn.Let x e') refs' ρ'
    | LetBangC : forall x e refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        stepC (Insn.LetBang x e) refs ρ (Insn.LetBang x e') refs' ρ'
    
    | LetPairC : forall x1 x2 e refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        stepC (Insn.LetPair x1 x2 e) refs ρ (Insn.LetPair x1 x2 e') refs' ρ'
    
    | SendC : forall e B refs ρ e' refs' ρ',
        Expr.step e refs ρ e' refs' ρ' ->
        stepC (Insn.Send e B) refs ρ (Insn.Send e' B) refs' ρ'.

End Insn.

Module Process.
    Inductive t :=
    | Empty
    | Do : Insn.t -> t -> t
    (* BroadcastIf e As P1 P2 . P
       Send e to all the actors in As;
       if e=True then proceed as P1; P
       otherwise proceed as P2; P
      *)
    | BroadcastIf : Expr.t -> Actor.FSet.t -> t -> t -> t -> t
    (* ReceiveIf x A P1 P2 . P
       Receive x from A;
       if x=True then proceed as P1; P
       otherwise proceed as P2; P
      *)
    | ReceiveIf : Actor.t -> t -> t -> t -> t
    .

    Fixpoint seq (P1 P2 : t) : t :=
      match P1 with
      | Empty => P2
      | Do I0 P1' => Do I0 (seq P1' P2)
      | BroadcastIf e Bs P11 P12 P1' =>
        BroadcastIf e Bs P11 P12 (seq P1' P2)
      | ReceiveIf A P11 P12 P1' =>
        ReceiveIf A P11 P12 (seq P1' P2)
      end.

    Fixpoint subst (x : Var.t) (v : Expr.t) (P : t) : t :=
    match P with
    | Empty => Empty
    | Do I0 P' =>
      let P'' := if Var.FSet.mem x (Insn.binders I0)
                 then P'
                 else subst x v P'
      in
      Do (Insn.subst x v I0) P''
    | BroadcastIf e As P1 P2 P0 =>
      BroadcastIf (Expr.subst x v e) As (subst x v P1) (subst x v P2) (subst x v P0)
    | ReceiveIf A P1 P2 P0 =>
      ReceiveIf A (subst x v P1) (subst x v P2) (subst x v P0)
    end.

    (* Semantics *)

    Inductive step : Process.t -> Var.Map.t nat -> Config.t -> Process.t -> Var.Map.t nat -> Config.t -> Prop :=
    | DoC : forall I P refs ρ I' refs' ρ',
        Insn.stepC I refs ρ I' refs' ρ' ->
        step (Do I P) refs ρ (Do I' P) refs' ρ'

    | LetB : forall x v P refs ρ P' refs',
        Expr.Val v ->
        P' = Process.subst x v P ->
        Var.Map.Equal refs' refs ->
        step (Do (Insn.Let x v) P) refs ρ P' refs' ρ

    | LetBangB : forall x e P refs ρ P' refs',
        P' = Process.subst x e P ->
        Var.Map.Equal refs' refs ->
        step (Do (Insn.LetBang x (Expr.Bang e)) P) refs ρ P' refs' ρ

    | LetPairB : forall x1 x2 v1 v2 P ρ refs P' refs',
        Expr.Val v1 -> Expr.Val v2 ->
        P' = Process.subst x1 v1 (Process.subst x2 v2 P) ->
        Var.Map.Equal refs' refs ->
        step (Do (Insn.LetPair x1 x2 (Expr.Pair v1 v2)) P) refs ρ P' refs' ρ

    .

  
  Lemma stepCProper' : forall I refs1 cfg I' refs1' cfg',
    Insn.stepC I refs1 cfg I' refs1' cfg' ->
    forall refs2 refs2',
    Var.Map.Equal refs1 refs2 ->
    Var.Map.Equal refs1' refs2' ->
    Insn.stepC I refs2 cfg I' refs2' cfg'.
  Proof.
    intros ? ? ? ? ? ? Hstep.
    inversion Hstep; subst; clear Hstep;
      intros refs2 refs2' Hrefs Hrefs';
      try (constructor; auto; Var.simplify; fail).
  Qed.
  
  Global Instance stepCProper : Proper (eq ==> Var.Map.Equal ==> eq ==> eq ==> Var.Map.Equal ==> eq ==> iff) Insn.stepC.
  Proof.
    intros ? P ? refs1 refs2 Hrefs ? ρ ? ? P' ? refs1' refs2' Hrefs' ? ρ' ?;
      subst.
    split; intros; eapply stepCProper'; eauto; symmetry; auto.
  Qed.
  Lemma stepProper' : forall P refs1 cfg P' refs1' cfg',
    step P refs1 cfg P' refs1' cfg' ->
    forall refs2 refs2',
    Var.Map.Equal refs1 refs2 ->
    Var.Map.Equal refs1' refs2' ->
    step P refs2 cfg P' refs2' cfg'.
  Proof.
    intros ? ? ? ? ? ? Hstep.
    induction Hstep; intros refs2 refs2' Hrefs Hrefs';
      try (constructor; auto; Var.simplify; fail).
  Qed.

  Global Instance stepProper : Proper (eq ==> Var.Map.Equal ==> eq ==> eq ==> Var.Map.Equal ==> eq ==> iff) step.
  Proof.
    intros ? P ? refs1 refs2 Hrefs ? ρ ? ? P' ? refs1' refs2' Hrefs' ? ρ' ?;
      subst.
    split; intros; eapply stepProper'; eauto; symmetry; auto.
  Qed.

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
      Actor.Map.Equal N' (Actor.Map.add A P' N) ->
      ChorEnv.Equal refs' (Actor.Map.add A refsA' refs) ->
      step  N refs cfg
            (Label.Loc A)
            N' refs' cfg'

    | Send : forall PA PB y N refs refs' cfg cfg' A e B N',
      A <> B ->
      Actor.Map.MapsTo A (Process.Do (Insn.Send (Expr.Bang e) B) PA) N ->
      Actor.Map.MapsTo B (Process.Do (Insn.Receive y A) PB) N ->
      Actor.Map.Equal N' (Actor.Map.add A PA (Actor.Map.add B (Process.subst y e PB) N)) ->
      ChorEnv.Equal refs' refs ->
      cfg' = cfg ->
      
      step N refs cfg (Label.Send A e B) N' refs' cfg'

    | If : forall PA1 PA2 PA N refs refs' cfg cfg' A b Bs N',

      ~ Actor.FSet.In A Bs ->

      Actor.Map.MapsTo A
        (Process.BroadcastIf (Expr.Bit b) Bs PA1 PA2 PA)
        N ->
      Actor.Map.MapsTo A
        (if b then Process.seq PA1 PA 
              else Process.seq PA2 PA)
        N' ->
      (forall B, Actor.FSet.In B Bs ->
        exists PB1 PB2 PB,
        Actor.Map.MapsTo B
          (Process.ReceiveIf A PB1 PB2 PB)
          N
        /\
        Actor.Map.MapsTo B
          (if b
            then Process.seq PB1 PB
            else Process.seq PB2 PB)
          N'
      ) ->

      (forall C, C <> A -> ~ Actor.FSet.In C Bs ->
        Actor.Map.find C N' = Actor.Map.find C N) ->
 
      ChorEnv.Equal refs' refs ->
      cfg' = cfg ->
      step N refs cfg (Label.If A b Bs) N' refs' cfg'
    

    | EPR : forall refs0 x y PA PB qA qB N refs cfg A B N' refs' cfg',
      A <> B ->
      Actor.Map.MapsTo A (Process.Do (Insn.EPR x B) PA) N ->
      Actor.Map.MapsTo B (Process.Do (Insn.EPR y A) PB) N ->
      ChorEnv.epr A B refs cfg = (qA, qB, refs0, cfg') ->
      ChorEnv.Equal refs' refs0 ->
      Actor.Map.Equal N' 
        (Actor.Map.add A (Process.subst x (Expr.QRef qA) PA) (
            Actor.Map.add B (Process.subst y (Expr.QRef qB) PB) N)) ->

      step N refs cfg (Label.EPR A B) N' refs' cfg'
    .

    Record WF (Actors : Actor.FSet.t) (N : Network.t) :=
        {
            wf_domain : forall A, Actor.FSet.In A Actors <-> Actor.Map.In A N;
        }.

  Lemma stepProper' : forall N Theta cfg l N' Theta' cfg',
    step N Theta cfg l N' Theta' cfg' ->
    forall N0 N0' Theta0 Theta0',
    Actor.Map.Equal N N0 ->
    Actor.Map.Equal N' N0' ->
    ChorEnv.Equal Theta Theta0 ->
    ChorEnv.Equal Theta' Theta0' ->
    step N0 Theta0 cfg l N0' Theta0' cfg'.
  Proof.
    intros ? ? ? ? ? ? ? Hstep.
    induction Hstep; intros N0 N0' Theta0 Theta0' HN HN' HTheta HTheta';
      subst.
    * 
      try (rewrite HTheta in *; clear refs HTheta);
      try (rewrite HTheta' in *; clear refs' HTheta');
      try (rewrite HN in *; clear N HN);
      try (rewrite HN' in *; clear N' HN').
      econstructor; eauto.
    * try (rewrite HTheta in *; clear refs HTheta);
      try (rewrite HTheta' in *; clear refs' HTheta');
      try (rewrite HN in *; clear N HN);
      try (rewrite HN' in *; clear N' HN').
      econstructor; eauto.
    * try (rewrite HTheta in *);
      try (rewrite HTheta' in *);
      try (rewrite HN in *);
      try (rewrite HN' in *).
      econstructor; eauto.
      2:{ intros. rewrite <- HN, <- HN'. auto. }
      {
        intros B Hin.
        destruct (H2 B Hin) as [PB1 [PB2 [PB [HBN HBN']]]].
        exists PB1, PB2, PB.
        rewrite HN in *.
        rewrite HN' in *.
        auto.
      }
    * try (rewrite HN in *; clear N HN);
      try (rewrite HN' in *; clear N' HN').
      rename H2 into Hepr.
      apply (ChorEnv.chor_epr_eq Theta0) in Hepr; auto.
      destruct Hepr as [T2' [HT2 Hepr]].
      econstructor; eauto.
      rewrite <- HTheta'; auto.
      rewrite HT2; auto. 
  Qed.

  Global Instance stepProper : Proper (Actor.Map.Equal ==> ChorEnv.Equal ==> eq ==> eq ==> Actor.Map.Equal ==> ChorEnv.Equal ==> eq ==> iff) step.
  Proof.
    intros N1 N2 HN refs1 refs2 Hrefs ? cfg ? ? l ? N1' N2' HN' refs1' refs2' Hrefs' ? cfg' ?;
      subst.
    split; intros Hstep;
    eapply stepProper'; eauto; symmetry; auto.
  Qed.

  Definition Empty (N : t) := forall A PA, Actor.Map.MapsTo A PA N -> PA = Process.Empty.
End Network.

Definition doo (x : Insn.t) (xso : option Process.t) : option Process.t :=
  match xso with
  | None => None
  | Some xs => Some (Process.Do x xs)
  end.

Fixpoint epp (p : Actor.t) (c : Choreography.t): option Process.t :=
  match c with
  | Choreography.Empty => Some Process.Empty
  | Choreography.Do (Choreography.Insn.Send A1 e A2 x) C =>
      match (Actor.eq_dec A1 p, Actor.eq_dec A2 p) with
      | (left _, left _)  => None
      | (left _, right _) => doo (Insn.Send e A2) (epp p C)
      | (right _, left _) => doo (Insn.Receive x A1) (epp p C)
      | _ => epp p C
      end
  | Choreography.Do (Choreography.Insn.EPR A1 x1 A2 x2) C =>
      match (Actor.eq_dec A1 p, Actor.eq_dec A2 p) with
      | (left _, left _)  => None
      | (left _, right _) => doo (Insn.EPR x1 A2) (epp p C)
      | (right _, left _) => doo (Insn.EPR x2 A1) (epp p C)
      | _ => epp p C
      end
  | Choreography.Do (Choreography.Insn.Let A1 x e) C =>
      if Actor.eq_dec A1 p
      then doo (Insn.Let x e) (epp p C)
      else epp p C
  | Choreography.Do (Choreography.Insn.LetBang A1 x e) C =>
      if Actor.eq_dec A1 p
      then doo (Insn.LetBang x e) (epp p C)
      else epp p C
  | Choreography.Do (Choreography.Insn.LetPair A1 x1 x2 e) C =>
      if Actor.eq_dec A1 p
      then doo (Insn.LetPair x1 x2 e) (epp p C)
      else epp p C
  (* | _ => None *)

  | Choreography.If A e C1 C2 C =>
  (*
    if p = A
    then 
      - send/broadcast e to all of the actos in C1/C2
      - If e then epp A C1 else epp A C2 ; epp A C
    else if p ∈ actors(C1) ∪ actors(C2)
    then
      - receive flag from A
      - If flag then epp p C1 else epp p C2 ; epp p C
    else epp p C
    *)
    let Bs := Actor.FSet.remove A (Actor.FSet.union (Choreography.actors C1) (Choreography.actors C2)) in
    if Actor.eq_dec A p
    then 
      match epp p C1, epp p C2, epp p C with
      | Some P1, Some P2, Some P0 =>
        Some (Process.BroadcastIf e Bs P1 P2 P0)
      | _, _, _ => None
      end
    else if Actor.Map.FSetProofs.in_dec p Bs
    then 
      match epp p C1, epp p C2, epp p C with
      | Some P1, Some P2, Some P0 =>
        Some (Process.ReceiveIf A P1 P2 P0)
      | _, _, _ => None
      end
    else epp p C
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
| EPP_nil : forall A, EPP A Choreography.Empty Process.Empty

| EPP_send : forall D A C P B e y,
    D = A ->
    D <> B ->
    EPP D C P ->
    EPP D
      (Choreography.Do (Choreography.Insn.Send A e B y) C) 
      (Process.Do (Insn.Send e B) P)
| EPP_receive : forall D B C P A e y,
    D = B ->
    D <> A ->
    EPP D C P ->
    EPP D
      (Choreography.Do (Choreography.Insn.Send A e B y) C)
      (Process.Do (Insn.Receive y A) P)

| EPP_EPR_1 : forall D A B x y C P,
    D = A ->
    D <> B ->
    EPP D C P ->
    EPP D
      (Choreography.Do (Choreography.Insn.EPR A x B y) C)
      (Process.Do (Insn.EPR x B) P)
| EPP_EPR_2 : forall D A B x y C P,
    D <> A ->
    D = B ->
    EPP D C P ->
    EPP D
      (Choreography.Do (Choreography.Insn.EPR A x B y) C)
      (Process.Do (Insn.EPR y A) P)

| EPP_Let : forall D A x e C P,
    D = A ->
    EPP D C P ->
    EPP D
      (Choreography.Do (Choreography.Insn.Let A x e) C)
      (Process.Do (Insn.Let x e) P)

| EPP_LetBang : forall D A x e C P,
    D = A ->
    EPP D C P ->
    EPP D
      (Choreography.Do (Choreography.Insn.LetBang A x e) C)
      (Process.Do (Insn.LetBang x e) P)

| EPP_LetPair : forall D A x1 x2 e C P,
    D = A ->
    EPP D C P ->
    EPP D
      (Choreography.Do (Choreography.Insn.LetPair A x1 x2 e) C)
      (Process.Do (Insn.LetPair x1 x2 e) P)

| EPP_disjoint : forall A I C P,
  ~ Actor.FSet.In A (Choreography.Insn.actors I) ->
  EPP A C P ->
  EPP A (Choreography.Do I C) P

(* TODO: EPP_if *)
.


Inductive EPP_N C : Network.t -> Prop :=
| EPP_N_empty : forall N,
  Actor.Map.Empty N ->
  EPP_N C N
| EPP_N_add : forall A PA N,
  Actor.Map.MapsTo A PA N ->
  EPP A C PA ->
  EPP_N C (Actor.Map.remove A N) ->
  EPP_N C N.


Definition eppI (D : Actor.t) (I : Choreography.Insn.t) :=
  match I with
  | Choreography.Insn.Send A v B x =>
    if Actor.eq_dec D A then [Insn.Send v B]
    else if Actor.eq_dec D B then [Insn.Receive x A]
    else []
  | Choreography.Insn.EPR A x B y =>
    if Actor.eq_dec D A then [Insn.EPR x B]
    else if Actor.eq_dec D B then [Insn.EPR y A]
    else []
  | Choreography.Insn.Let A x e =>
    if Actor.eq_dec D A then [Insn.Let x e]
    else []
  | Choreography.Insn.LetBang A x e =>
    if Actor.eq_dec D A then [Insn.LetBang x e]
    else []
  | Choreography.Insn.LetPair A x1 x2 e =>
    if Actor.eq_dec D A then [Insn.LetPair x1 x2 e]
    else []
  end.
