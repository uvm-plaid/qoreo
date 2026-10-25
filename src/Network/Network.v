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

Module Choreography := Choreography.Choreography.

From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Stdlib.Structures.Equalities.
Import Actor.Map.Tactics.


Module Typ.
  (*
  Inductive t :=
  | Loc : Expr.typ -> t
  | Unit : t
  | Pair : t -> t -> t.
  *)


  Fixpoint epp (A : Actor.t) (τ : Choreography.Typ.t) : Expr.typ :=
    match τ with
    | Choreography.Typ.Local B τ' =>
      if Actor.eq_dec A B then τ' else Expr.UNIT
    | Choreography.Typ.Unit => Expr.UNIT
    | Choreography.Typ.Pair τ1 τ2 =>
      Expr.Tensor (epp A τ1) (epp A τ2)
    end.


End Typ.


(* We actually will want our own patterns here, without Actor names. *)
Module Pattern.
  Inductive t :=
  | Var : Var.t -> t
  | Unit : t
  | Pair : t -> t -> t
  | Bang : Var.t -> t.

  Fixpoint in_pat (x : Var.t) (p : t) : bool :=
    match p with
    | Var y | Bang y =>
      if Var.eq_dec x y then true else false
    | Unit => false
    | Pair p1 p2 => in_pat x p1 || in_pat x p2
    (*| Pair y1 y2 => if Var.eq_dec x y1 then true
                    else if Var.eq_dec x y2 then true
                    else false
                    *)
    end.

  Inductive WellTyped : Var.Map.t Expr.typ -> Var.Map.t Expr.typ -> t -> Expr.typ -> Prop :=

  | WTVar : forall Γ Δ x τ,
    ~ Var.Map.In x Γ ->
    Var.Map.Singleton x τ Δ ->
    WellTyped Γ Δ (Var x) τ

  | WTBang : forall Γ Δ x τ,
    Var.Map.MapsTo x τ Γ ->
    Var.Map.Empty Δ ->
    WellTyped Γ Δ (Bang x) (Expr.BANG τ)

  | WTUnit : forall Γ Δ,
    Var.Map.Empty Δ ->
    WellTyped Γ Δ Unit Expr.UNIT

  | WTPair : forall Γ1 Γ2 Δ1 Δ2 Γ Δ p1 p2 τ1 τ2,
    WellTyped Γ1 Δ1 p1 τ1 ->
    WellTyped Γ2 Δ2 p2 τ2 ->
    Var.Map.Partition Γ Γ1 Γ2 ->
    Var.Map.Partition Δ Δ1 Δ2 ->
    WellTyped Γ Δ (Pair p1 p2) (Expr.Tensor τ1 τ2)
  .

  Fixpoint epp (A : Actor.t) (p : Choreography.Pattern.t) : t :=
    match p with
    | Choreography.Pattern.Var B x =>
      if Actor.eq_dec A B then Var x else Unit
    | Choreography.Pattern.Bang B x =>
      if Actor.eq_dec A B then Bang x else Unit
    | Choreography.Pattern.Unit => Unit
    | Choreography.Pattern.Pair p1 p2 => Pair (epp A p1) (epp A p2)
    end.

  (*
  Lemma WT_epp_None : forall p G D τ A,
    Choreography.Pattern.WellTyped G D p τ ->
    epp A p = None ->
    Typ.epp A τ = None.
  Proof.
    intros p G D τ A HWT.
    induction HWT; intros Hepp; simpl in *; auto.
    * Actor.Map.Tactics.compare A A0; auto; discriminate.
    * destruct (epp A p1) as [p1' | ] eqn:Hp1'.
      { destruct (epp A p2); discriminate. }
      rewrite IHHWT1; auto.

    * Actor.Map.Tactics.compare A A0; auto; discriminate.
  Qed.
  *)
  

  Lemma WT_EPP : forall p G D τ,
    Choreography.Pattern.WellTyped G D p τ ->
    forall A,
    WellTyped (ChorEnv.find A G) (ChorEnv.find A D) (epp A p) (Typ.epp A τ).
  Proof.
    intros ? ? ? ? HWT;
      induction HWT;
        intros A0; simpl.
    * specialize (H A0); specialize (H0 A0).
      Actor.Map.Tactics.compare A0 A;
        constructor;
        ChorEnv.simplify.
      Var.solve.
    * constructor; auto. specialize (H0 A0). Var.solve.
    * econstructor; auto.
    * specialize (H A0); specialize (H1 A0).
      ChorEnv.simplify.
      + constructor; Var.solve.
        rewrite H0.
        Var.simplify.
      + constructor; auto.
        rewrite H1. auto with var_db.
  Qed.


End Pattern.


Module Label.
  Inductive t :=
  | Internal : Var.Map.t nat -> Config.t -> 
               Var.Map.t nat -> Config.t -> t
  | Send : Expr.t -> Actor.t -> t
  | Receive : Actor.t -> Expr.t -> t
  | EPR  : Actor.t -> nat -> t
  | SendIf : bool -> Actor.FSet.t -> t
  | ReceiveIf : bool -> Actor.t -> t.

  Inductive Equiv : t -> t -> Prop :=
  | InternalEquiv : forall T1 T1' T2 T2' cfg1 cfg2,
    Var.Map.Equal T1 T1' ->
    Var.Map.Equal T2 T2' ->
    Equiv (Internal T1 cfg1 T2 cfg2) (Internal T1' cfg1 T2' cfg2)
  | SendEquiv : forall e A,
    Equiv (Send e A) (Send e A)
  | ReceiveEquiv : forall A e,
    Equiv (Receive A e) (Receive A e)
  | EPREquiv : forall A q,
    Equiv (EPR A q) (EPR A q)
  | SendIfEquiv : forall b tgt1 tgt2,
    Actor.FSet.Equal tgt1 tgt2 ->
    Equiv (SendIf b tgt1) (SendIf b tgt2)
  | ReceiveIfEquiv :forall b A,
    Equiv (ReceiveIf b A) (ReceiveIf b A).

  #[global] Instance InternalProper : Proper (Var.Map.Equal ==> eq ==> Var.Map.Equal ==> eq ==> Equiv) Internal.
  intros T1 T1' HT1 ? cfg1 ? T2 T2' HT2 ? cfg2 ?; subst.
  constructor; auto.
  Qed.

  #[global] Instance SendIfProper : Proper (eq ==> Actor.FSet.Equal ==> Equiv) SendIf.
  intros ? ? ? T1 T2 HT; subst.
  constructor; auto.
  Qed.

  #[global] Instance EquivEquivalence : Equivalence Equiv.
  Proof.
    split.
    * intros l. induction l; constructor; 
      try reflexivity.
    * intros l1 l2 Hequiv.
      induction Hequiv; constructor; auto;
      symmetry; auto.
    * intros l1 l2 l3 H. revert l3.
      induction H; intros l3 H';
      inversion H'; subst; clear H';
      try (constructor; auto).
      + rewrite H. auto.
      + rewrite H0; auto.
      + rewrite H; auto. 
  Qed.
End Label.

Module Process.
    Inductive t : Type :=

    (*| Var   : Var.t -> t*)
    | LetIn : Pattern.t -> t -> t -> t

    | Ret : Expr.t -> t

    | Unit    : t
    | Pair    : t -> t -> t
    | Send : Expr.t -> Actor.t -> t
    | Receive : Actor.t -> t
    | EPR : Actor.t -> t
    | SendIf  : Expr.t -> Actor.FSet.t -> t -> t -> t
    | ReceiveIf    : Actor.t -> t -> t -> t
    .

    Fixpoint subst (x : Var.t) (v : Expr.t) (P : t) : t :=
    match P with
    (*| Var y => if Var.eq_dec x y then Ret v else Var y*)
    | LetIn p P1 P2 =>
      LetIn p (subst x v P1)
        (if Pattern.in_pat x p
          then P2
          else subst x v P2)
    | Ret e => Ret (Expr.subst x v e)
    | Unit => Unit
    | Pair P1 P2 => Pair (subst x v P1) (subst x v P2)
    | Send e B => Send (Expr.subst x v e) B
    | Receive B => Receive B
    | EPR B => EPR B
    | SendIf e tgts P1 P2 =>
      SendIf (Expr.subst x v e) tgts (subst x v P1) (subst x v P2)
    | ReceiveIf B P1 P2 =>
      ReceiveIf B (subst x v P1) (subst x v P2)
    end.

    Fixpoint subst_pat p (v : t) P :=
    match p, v with
      | Pattern.Var x, Ret v' =>
        subst x v' P
      | Pattern.Bang x, Ret (Expr.Bang e') =>
        subst x e' P
      | Pattern.Unit, Unit => P
      | Pattern.Pair p1 p2, Pair v1 v2 =>
        subst_pat p1 v1 (subst_pat p2 v2 P)

      | _, _ => P
      end.

    Inductive Val : t -> Prop :=
    | VRet : forall v, Expr.Val v -> Val (Ret v)
    | VUnit : Val Unit
    | VPair :forall v1 v2,
      Val v1 -> Val v2 -> Val (Pair v1 v2)
    .

    (* Types *)

    Inductive WellTyped : Var.Map.t Expr.typ -> Var.Map.t Expr.typ -> Var.Map.t nat -> t -> Expr.typ -> Prop :=
    | WTLetIn : forall Γ Δ Θ Γ0 Δ0 Δ1 Δ2 Θ1 Γ' Δ' Θ2 p P1 P2 τ0 τ',
      Pattern.WellTyped Γ0 Δ0 p τ0 ->
      WellTyped Γ Δ1 Θ1 P1 τ0 ->
      WellTyped Γ' Δ' Θ2 P2 τ' ->

      Var.Map.Partition Γ' Γ Γ0 ->
      Var.Map.Partition Δ Δ1 Δ2 ->
      Var.Map.Partition Δ' Δ2 Δ0 ->
      Var.Map.Partition Θ Θ1 Θ2 ->

      WellTyped Γ Δ Θ (LetIn p P1 P2) τ'

    | WTRet : forall Γ Δ Θ e τ,
      Expr.WellTyped Γ Δ Θ e τ ->
      WellTyped Γ Δ Θ (Ret e) τ

    | WTUnit : forall Γ Δ Θ,
      Var.Map.Empty Δ ->
      Var.Map.Empty Θ ->
      WellTyped Γ Δ Θ Unit Expr.UNIT

    | WTPair : forall Δ1 Δ2 Θ1 Θ2 Γ Δ Θ C1 C2 τ1 τ2,
      WellTyped Γ Δ1 Θ1 C1 τ1 ->
      WellTyped Γ Δ2 Θ2 C2 τ2 ->

      Var.Map.Partition Δ Δ1 Δ2 ->
      Var.Map.Partition Θ Θ1 Θ2 ->

      WellTyped Γ Δ Θ (Pair C1 C2) (Expr.Tensor τ1 τ2)

    | WTSend : forall Γ Δ Θ e τ B,
      Expr.WellTyped Γ Δ Θ e (Expr.BANG τ) ->
      WellTyped Γ Δ Θ (Send e B) Expr.UNIT

    | WTReceive : forall Γ Δ Θ B τ,
      Var.Map.Empty Δ ->
      Var.Map.Empty Θ ->
      WellTyped Γ Δ Θ (Receive B) (Expr.BANG τ) (* ? *)

    | WTEPR : forall Γ Δ Θ B,
      Var.Map.Empty Δ ->
      Var.Map.Empty Θ ->
      WellTyped Γ Δ Θ (EPR B) Expr.QUBIT

    | WTSendIf : forall Δ1 Δ2 Θ1 Θ2 Γ Δ Θ e tgts P1 P2 τ,

      Expr.WellTyped Γ Δ1 Θ1 e Expr.BIT ->
      WellTyped Γ Δ2 Θ2 P1 τ ->
      WellTyped Γ Δ2 Θ2 P2 τ ->

      Var.Map.Partition Δ Δ1 Δ2 ->
      Var.Map.Partition Θ Θ1 Θ2 ->

      WellTyped Γ Δ Θ (SendIf e tgts P1 P2) τ

    | WTReceiveIf : forall Γ Δ Θ src P1 P2 τ,

      WellTyped Γ Δ Θ P1 τ ->
      WellTyped Γ Δ Θ P2 τ ->

      WellTyped Γ Δ Θ (ReceiveIf src P1 P2) τ
    .

    Lemma WellTypedProper' : forall Γ1 Δ1 Θ1 P τ,
      WellTyped Γ1 Δ1 Θ1 P τ ->
      forall Γ2 Δ2 Θ2,
        Var.Map.Equal Γ1 Γ2 ->
        Var.Map.Equal Δ1 Δ2 ->
        Var.Map.Equal Θ1 Θ2 ->
      WellTyped Γ2 Δ2 Θ2 P τ.
    Proof.
        intros ? ? ? ? ? HWT.
        induction HWT; intros ? ? ? Heq1 Heq2 Heq3;
        try (econstructor; eauto;
          try apply IHHWT1;
          try apply IHHWT2;
          try apply IHHWT3;
          try rewrite <- Heq1;
          try rewrite <- Heq2;
          try rewrite <- Heq3;
          try reflexivity;
          auto; fail).
        * rewrite Heq1, Heq2, Heq3 in *.
          econstructor; eauto.
        * rewrite Heq1, Heq2, Heq3 in *.
          econstructor; eauto.
          apply IHHWT1; auto; try reflexivity.
          apply IHHWT2; auto; try reflexivity.
    Qed.


    Global Instance WellTypedProper : Proper (Var.Map.Equal ==> Var.Map.Equal ==> Var.Map.Equal ==> eq ==> eq ==> iff) WellTyped.
    Proof.
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?;
        subst.
      split; intros; eapply WellTypedProper'; eauto; symmetry; auto.
    Qed.

    (* Semantics *)


    Inductive step : Process.t -> Label.t -> Process.t -> Prop :=

    | RetC : forall e T cfg e' T' cfg',
      Expr.step e T cfg e' T' cfg' ->
      step (Ret e)
           (Label.Internal T cfg T' cfg')
           (Ret e')

    | LetInC : forall p P1 P2 l P1',
      step P1 l P1' ->
      step (LetIn p P1 P2)
           l
           (LetIn p P1' P2)

    | LetInB : forall p v P2 T cfg P2' T' cfg',
      Val v ->
      P2' = subst_pat p v P2 ->
      Var.Map.Equal T' T ->
      cfg' = cfg ->
      step (LetIn p v P2)
           (Label.Internal T cfg T' cfg')
           P2'


    | PairC1 : forall P1 P2 l P1',
      step P1 l P1' ->
      step (Pair P1 P2) l (Pair P1' P2)

    | PairC2 : forall P1 P2 l P2',
      Val P1 ->
      step P2 l P2' ->
      step (Pair P1 P2) l (Pair P1 P2')

    | SendC : forall e B T cfg e' T' cfg',
      Expr.step e T cfg e' T' cfg' ->
      step (Send e B)
           (Label.Internal T cfg T' cfg')
           (Send e' B)

    | SendB : forall v B,
      Expr.Val v ->
      step (Send v B)
           (Label.Send v B)
           Unit

    | ReceiveB : forall A v,
      Expr.Val v ->
      step (Receive A)
           (Label.Receive A v)
           (Ret v)

    | EPRB : forall B qB,
      step (EPR B)
           (Label.EPR B qB)
           (Ret (Expr.QRef qB))

    | SendIfC : forall e tgts P1 P2 T cfg T' cfg' e',
      Expr.step e T cfg e' T' cfg' ->
      step (SendIf e tgts P1 P2)
           (Label.Internal T cfg T' cfg')
           (SendIf e' tgts P1 P2)

    
    | SendIfB : forall (b : bool) tgts tgts' P1 P2 P',
      P' = (if b then P1 else P2) ->
      Actor.FSet.Equal tgts tgts' ->
      step (SendIf (Expr.Bit b) tgts P1 P2)
           (Label.SendIf b tgts')
           P'

    | ReceiveIfB : forall src P1 P2 (b : bool) P',
      P' = (if b then P1 else P2) ->
      step (ReceiveIf src P1 P2)
           (Label.ReceiveIf b src)
           P'
    .

  
  Lemma stepProper' : forall P l1 P',
    Process.step P l1 P' ->
    forall l2,
    Label.Equiv l1 l2 ->
    Process.step P l2 P'.
  Proof.
    intros P l1 P' Hstep.
    induction Hstep;
      intros  l2 Hl;
      try (constructor; auto; fail);
      try (inversion Hl; subst; clear Hl;
           constructor; auto; Var.simplify; fail).

    * inversion Hl; subst; clear Hl.
      constructor; auto.
      rewrite H0. auto.
  Qed.
  
  Global Instance stepProper : Proper (eq ==> Label.Equiv ==> eq ==> iff) step.
  Proof.
    intros ? P ? l1 l2 Hl ? P' ?;
      subst.
    split; intros; eapply stepProper'; eauto; symmetry; auto.
  Qed.

End Process.

Module Network.
    Definition t := Actor.Map.t (Process.t).

    Inductive step :    Network.t -> ChorEnv.t nat -> Config.t ->
                        Choreography.Label.t ->
                        Network.t -> ChorEnv.t nat -> Config.t -> Prop :=

    | Internal : forall P refsA' P' N refs cfg A N' refs' cfg',
      Actor.Map.MapsTo A P N ->
      Process.step P 
                   (Label.Internal (ChorEnv.find A refs) cfg refsA' cfg')
                   P' ->
      Actor.Map.Equal N' (Actor.Map.add A P' N) ->
      ChorEnv.Equal refs' (Actor.Map.add A refsA' refs) ->
      step  N refs cfg
            (Choreography.Label.Loc A)
            N' refs' cfg'


    | Send : forall PA PA' PB PB' N refs refs' cfg cfg' (A B : Actor.t) v N',

      Actor.Map.MapsTo A PA N ->
      Actor.Map.MapsTo B PB N ->

      Expr.Val v ->
      Process.step PA (Label.Send v B) PA' ->
      Process.step PB (Label.Receive A v) PB' ->


      Actor.Map.Equal N' (Actor.Map.add A PA' (Actor.Map.add B PB' N)) ->
      ChorEnv.Equal refs' refs ->
      cfg' = cfg ->
      
      step N refs cfg (Choreography.Label.Send A v B) N' refs' cfg'

    | EPR : forall refs0 PA PA' PB PB' qA qB N refs cfg A B N' refs' cfg',
      
      Actor.Map.MapsTo A PA N ->
      Actor.Map.MapsTo B PB N ->

      ChorEnv.epr A B refs cfg = (qA, qB, refs0, cfg') ->
      
      Process.step PA (Label.EPR B qA) PA' ->
      Process.step PB (Label.EPR A qB) PB' ->
      
      Actor.Map.Equal N' 
        (Actor.Map.add A PA' (Actor.Map.add B PB' N)) ->

      ChorEnv.Equal refs' refs0 ->

      step N refs cfg (Choreography.Label.EPR A B) N' refs' cfg'


    | If : forall PA PA' N refs refs' cfg cfg' A b Bs N',

      ~ Actor.FSet.In A Bs ->

      Actor.Map.MapsTo A PA N ->
      Process.step PA (Label.SendIf b Bs) PA' ->
      Actor.Map.MapsTo A PA' N' ->

      (forall B,
        Actor.FSet.In B Bs ->
        exists PB PB',
          Actor.Map.MapsTo B PB N 
          /\
          Process.step PB (Label.ReceiveIf b A) PB'
          /\
          Actor.Map.MapsTo B PB' N'
      ) ->


      (forall A0, A <> A0 ->
        ~ Actor.FSet.In A0 Bs ->
        Actor.Map.find A0 N' = Actor.Map.find A0 N
        ) ->

      ChorEnv.Equal refs' refs ->
      cfg' = cfg ->
  
      step N refs cfg (Choreography.Label.If A b Bs) N' refs' cfg'
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
      unfold ChorEnv.epr in *.
      destruct (Config.epr_cfg cfg) as [[q1 q2] cfg0']
          eqn:Hcfg.
        inversion H1; subst; clear H1.
      econstructor;
        [eauto | eauto | | eauto | eauto | eauto | ].
      {
        unfold ChorEnv.epr in *.
        rewrite Hcfg.
        reflexivity.
      }
      {
        rewrite <- HTheta. auto.
      }

    * try (rewrite HTheta in *);
      try (rewrite HTheta' in *);
      try (rewrite HN in *);
      try (rewrite HN' in *).
      econstructor; eauto.
      2:{
        intros A0 ? ?.
        rewrite <- HN, <- HN'.
        auto.
      }
      {
        intros B HB.
        specialize (H3 B HB).
        destruct H3 as [PB [PB' [H3 [HBstep H3']]]].
        exists PB, PB'.
        rewrite <- HN, <- HN'.
        repeat split; auto.
      }
  Qed.

  Global Instance stepProper : Proper (Actor.Map.Equal ==> ChorEnv.Equal ==> eq ==> eq ==> Actor.Map.Equal ==> ChorEnv.Equal ==> eq ==> iff) step.
  Proof.
    intros N1 N2 HN refs1 refs2 Hrefs ? cfg ? ? l ? N1' N2' HN' refs1' refs2' Hrefs' ? cfg' ?;
      subst.
    split; intros Hstep;
    eapply stepProper'; eauto; symmetry; auto.
  Qed.
End Network.

(*
Fixpoint epp_pat (A : Actor.t) (pat : Choreography.Pattern.t) : Pattern.t :=
  match pat with
  | Choreography.Pattern.Var B x =>
    if Actor.eq_dec A B
    then Pattern.Var x
    else Pattern.Unit
  | Choreography.Pattern.Unit => Pattern.Unit
  | Choreography.Pattern.Pair pat1 pat2 =>
    Pattern.Pair (epp_pat A pat1) (epp_pat A pat2)
  | Choreography.Pattern.Bang B x =>
    if Actor.eq_dec A B
    then Pattern.Bang x
    else Pattern.Unit
  end.
  *)


Fixpoint epp (A : Actor.t) (c : Choreography.t) : Process.t :=
  match c with

  | Choreography.Loc B e =>
    if Actor.eq_dec A B
    then Process.Ret e
    else Process.Unit

  | Choreography.Unit => Process.Unit

  | Choreography.Pair C1 C2 => Process.Pair (epp A C1) (epp A C2)

  | Choreography.LetIn pat C1 C2 =>
    Process.LetIn (Pattern.epp A pat) (epp A C1) (epp A C2)

  | Choreography.Send B1 e B2 =>
    if Actor.eq_dec A B1
    then if Actor.eq_dec A B2
    then Process.Ret e
    else Process.Send e B2
    else if Actor.eq_dec A B2
    then Process.Receive B1
    else Process.Unit

  | Choreography.EPR B1 B2 =>
    if Actor.eq_dec A B1
    then if Actor.eq_dec A B2
    then Process.Pair (Process.EPR A) (Process.EPR A)
    else Process.Pair (Process.EPR B2) Process.Unit
    else if Actor.eq_dec A B2
    then Process.Pair Process.Unit (Process.EPR B1)
    else Process.Pair Process.Unit Process.Unit

  | Choreography.If B e C1 C2 =>
    let tgts := Actor.FSet.union (Choreography.actors C1) (Choreography.actors C2) in
    if Actor.eq_dec A B
    then Process.SendIf e tgts (epp A C1) (epp A C2)
    else if Actor.Map.FSetProofs.in_dec A tgts
    then Process.ReceiveIf A (epp A C1) (epp A C2)
    else (*Process.Unit*) (* depends on structure of the return type of C1/C2 *)
      epp A C1

end.

(*
Lemma epp_WellTyped_None : forall G D T C τ A,
  Choreography.WellTyped G D T C τ ->
  epp A C = None ->
  Typ.epp A τ = None.
Proof.
  intros G D T C τ A HWT.
  induction HWT; intros Hepp; simpl in *; auto.
  * admit (* let in *).
  * Actor.Map.Tactics.compare A A0; auto; try discriminate.
  * (* Tensor *)
    destruct (epp A C1) as [P1 | ] eqn:HP1.
    { exfalso. destruct (epp A C2); discriminate. }
    destruct (epp A C2) as [P2 | ] eqn:HP2.
    { exfalso. discriminate. }
    rewrite IHHWT1, IHHWT2; auto.

  * Actor.Map.Tactics.compare A A0; try discriminate. 
    Actor.Map.Tactics.compare A B; auto; try discriminate.
    
  * Actor.Map.Tactics.compare A A0; try discriminate. 
    Actor.Map.Tactics.compare A B; auto; try discriminate.

  * Actor.Map.Tactics.compare A A0; try discriminate. 
    destruct (Actor.Map.FSetProofs.in_dec A
                (Actor.FSet.union (Choreography.actors C1) (Choreography.actors C2)))
      as [? | Hin];
      try discriminate.
    apply IHHWT1.
    (* true --- if A ∉ \domain(C1) then epp A C1 = None *)
    admit.

Admitted.
*)

Lemma WT_EPP : forall G D T C τ,
  Choreography.WellTyped G D T C τ ->
  forall A,
  Process.WellTyped (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) (epp A C) (Typ.epp A τ).
Proof.
  intros G D T C τ HWT.
  induction HWT; intros A0;
    simpl in *;
    try discriminate.
  * eapply Process.WTLetIn
      with (Δ0 := ChorEnv.find A0 D1'); eauto.
    { apply Pattern.WT_EPP; auto. }
    { (* partition_sym *)
      ChorEnv.specialize_partition A0.
      Var.Map.Tactics.reflect_partition.
      2:{
        Var.Map.Tactics.rewrite_map (ChorEnv.find A0 D').
        rewrite (Var.Map.Proofs.concat_sym (ChorEnv.find A0 D1')); auto.
        reflexivity.
      }
      Var.simplify.
    }
  * (* Ret *)
    Actor.Map.Tactics.compare A0 A; try discriminate.
    2:{ constructor.
      apply H0. Actor.simplify.
      apply H1. Actor.simplify.
    }
    constructor; auto.
  * constructor; auto.
    { specialize (H A0). Var.solve. }
    { specialize (H0 A0). Var.solve. }
  * econstructor; eauto.
  
  * Actor.Map.Tactics.compare A0 A;
    Actor.Map.Tactics.compare A0 B.
    { (* A0 = A = B *)
      constructor; auto.
    }
    { (* A = A0 ≠ B *)
      econstructor; eauto.
    }
    { (* A ≠ A0 = B *)
      subst.
      econstructor; eauto.
      { apply H0. Actor.simplify. } 
      { apply H1. Actor.simplify. } 
    }
    { (* A ≠ A0 ≠ B *)
      constructor.
      { apply H0. Actor.simplify. } 
      { apply H1. Actor.simplify. } 
    }
  * Actor.Map.Tactics.compare A0 A;
    Actor.Map.Tactics.compare A0 B; subst;
    eapply Process.WTPair
        with (Δ2 := Var.Map.empty _) 
             (Δ1 := Var.Map.empty _)
             (Θ2 := Var.Map.empty _)
             (Θ1 := Var.Map.empty _);
      try match goal with
      | [ |- Process.WellTyped _ _ _ _ _ ] =>
        constructor; Var.solve
      | [ H : ChorEnv.Empty ?M
        |- Var.Map.Partition (ChorEnv.find ?X ?M) _ _ ] =>
        rewrite (H X); auto with var_db
      end.

  * (* IF *)
    ChorEnv.specialize_partition A0.
    Actor.Map.Tactics.compare A0 A.
    { (* A0 = A *)
      econstructor; eauto;
        ChorEnv.simplify.
    }
    (* A0 <> A *)
    unfold Actor.Map.singleton in *.
    ChorEnv.simplify.
    Var.Map.Tactics.rewrite_map (ChorEnv.find A0 D).
    Var.Map.Tactics.rewrite_map (ChorEnv.find A0 T).
    destruct (Actor.Map.FSetProofs.in_dec A0 (Actor.FSet.union (Choreography.actors C1) (Choreography.actors C2)))
      as [Hin | Hin].
    { (* in *)
      econstructor; eauto.
    }
    {
      (* Lemma: If A0 ∉ actors(C) and C : τ 
         then Typ.epp A0 τ = Unit? Rather, it should be
         unit up to the structure of tau... *)
      auto.
    }
Qed.


(*
Inductive EPP : list Actor.t -> Choreography.t -> Network.t -> Prop :=
| epp_empty : forall C, EPP [] C (Actor.Map.empty _)
| epp_cons : forall A Actors C P N,
    epp A C = Some P ->
    EPP Actors C N ->
    EPP (A::Actors) C (Actor.Map.add A P N).
*)

(*
Print Choreography.t.
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
*)


Inductive EPP_N C : Network.t -> Prop :=
| EPP_N_empty : forall N,
  Actor.Map.Empty N ->
  EPP_N C N
| EPP_N_add : forall A PA N,
  Actor.Map.MapsTo A PA N ->
  epp A C = PA ->
  EPP_N C (Actor.Map.remove A N) ->
  EPP_N C N.

(*
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
  *)
