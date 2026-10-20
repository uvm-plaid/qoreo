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

  Definition tensor (τ1 τ2 : option Expr.typ) : option Expr.typ :=
    match τ1, τ2 with
      | Some τ1', Some τ2' => Some (Expr.Tensor τ1' τ2')
      | None,     τ2'      => τ2'
      | τ1',      None     => τ1'
    end.

  Fixpoint epp (A : Actor.t) (τ : Choreography.Typ.t) : option Expr.typ :=
    match τ with
    | Choreography.Typ.Local B τ' =>
      if Actor.eq_dec A B then Some τ' else None
    | Choreography.Typ.Unit => None
    | Choreography.Typ.Pair τ1 τ2 =>
      tensor (epp A τ1) (epp A τ2)
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

  Inductive WellTyped : Var.Map.t Expr.typ -> Var.Map.t Expr.typ -> t -> option Expr.typ -> Prop :=

  | WTVar : forall Γ Δ x τ,
    ~ Var.Map.In x Γ ->
    Var.Map.Singleton x τ Δ ->
    WellTyped Γ Δ (Var x) (Some τ)

  | WTBang : forall Γ Δ x τ,
    Var.Map.MapsTo x τ Γ ->
    Var.Map.Empty Δ ->
    WellTyped Γ Δ (Bang x) (Some (Expr.BANG τ))

  | WTUnit : forall Γ Δ,
    Var.Map.Empty Δ ->
    WellTyped Γ Δ Unit None

  | WTPair : forall Γ1 Γ2 Δ1 Δ2 Γ Δ p1 p2 τ1 τ2 τ',
    WellTyped Γ1 Δ1 p1 τ1 ->
    WellTyped Γ2 Δ2 p2 τ2 ->
    Var.Map.Partition Γ Γ1 Γ2 ->
    Var.Map.Partition Δ Δ1 Δ2 ->
    τ' = Typ.tensor τ1 τ2 ->
    WellTyped Γ Δ (Pair p1 p2) τ'
  .

  Fixpoint epp (A : Actor.t) (p : Choreography.Pattern.t) : option t :=
    match p with
    | Choreography.Pattern.Var B x =>
      if Actor.eq_dec A B then Some (Var x) else None
    | Choreography.Pattern.Bang B x =>
      if Actor.eq_dec A B then Some (Bang x) else None
    | Choreography.Pattern.Unit => None
    | Choreography.Pattern.Pair p1 p2 =>
      match epp A p1, epp A p2 with
      | Some p1', Some p2' => Some (Pair p1' p2')
      | None,     p2'      => p2'
      | p1',      None     => p1'
      end
    end.

  
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
  
  Lemma WT_EPP : forall p (A : Actor.t) G D τ p',
    Choreography.Pattern.WellTyped G D p τ ->
    epp A p = Some p' ->
    exists τ', Typ.epp A τ = Some τ'
    /\
    WellTyped (ChorEnv.find A G) (ChorEnv.find A D) p' (Some τ').
  Proof.
    intros p. induction p as [B x | | p1 IHp1 p2 IHp2 | B x];
      intros A G D τ p' HWT Hp'.
    * inversion HWT; subst; clear HWT.
      simpl in *.
      Actor.Map.Tactics.compare A B;
        inversion Hp'; subst; clear Hp'.
      exists tau. split; auto.
      constructor; auto.
      { specialize (H1 A).
        Var.solve.
      }
    * simpl in *. discriminate.
      
    * simpl in *.
      inversion HWT; subst; clear HWT.
      destruct (epp A p1) as [p1' | ] eqn:Hp1';
        [ eapply IHp1 in Hp1'; eauto;
          destruct Hp1' as [τ1' [Hτ1' Hp1']]
        | ].
      + destruct (epp A p2) as [p2' | ] eqn:Hp2';
          [ eapply IHp2 in Hp2'; eauto;
            destruct Hp2' as [τ2' [Hτ2' Hp2']]
          | ].
        ++ inversion Hp'; subst; clear Hp'.
           exists (Expr.Tensor τ1' τ2').
           simpl. rewrite Hτ1', Hτ2'.
           split; auto.
           econstructor; eauto.

        ++ simpl.
          rewrite Hτ1'.
          replace (Typ.epp A tau2) with (@None Expr.typ) in *.
          2:{ symmetry; eapply WT_epp_None; eauto. }
          simpl.
          exists τ1'. split; auto.

          assert (ChorEnv.Empty G2) by admit.
          assert (ChorEnv.Empty D2) by admit.
          (* need to show G = G1 and D = D1 *)
          admit.


      + simpl.
        eapply WT_epp_None in Hp1'; eauto.
        rewrite Hp1'. simpl.
        eapply IHp2 in Hp'; eauto.
        assert (ChorEnv.Empty G1) by admit.
        assert (ChorEnv.Empty D1) by admit.
        (* need to show G = G2 and D = D2 *)
        admit.
    * inversion HWT; subst; clear HWT.
      simpl in *.
      Actor.Map.Tactics.compare A B;
        inversion Hp'; subst; clear Hp'.
      exists (Expr.BANG tau). split; auto.
      constructor; auto.
      2:{ specialize (H6 A). Var.solve. }
      { Var.simplify. rewrite H4.
        Var.solve.
      }
  Admitted.


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
      (*| Pattern.Var x, Ret v' =>
        subst x v' P*)
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

    Inductive WellTyped : Var.Map.t Expr.typ -> Var.Map.t Expr.typ -> Var.Map.t nat -> t -> option Expr.typ -> Prop :=
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
      WellTyped Γ Δ Θ (Ret e) (Some τ)

    | WTUnit : forall Γ Δ Θ,
      Var.Map.Empty Δ ->
      Var.Map.Empty Θ ->
      WellTyped Γ Δ Θ Unit None

    | WTSend : forall Γ Δ Θ e τ B,
      Expr.WellTyped Γ Δ Θ e (Expr.BANG τ) ->
      WellTyped Γ Δ Θ (Send e B) None (*???*)

    | WTReceive : forall Γ Δ Θ B τ,
      Var.Map.Empty Δ ->
      Var.Map.Empty Θ ->
      WellTyped Γ Δ Θ (Receive B) (Some (Expr.BANG τ)) (* ? *)

    | WTEPR : forall Γ Δ Θ B,
      Var.Map.Empty Δ ->
      Var.Map.Empty Θ ->
      WellTyped Γ Δ Θ (EPR B) (Some Expr.QUBIT)

    | WTSendIf : forall Δ1 Δ2 Θ1 Θ2 Γ Δ Θ e tgts P1 P2 τ,

      Expr.WellTyped Γ Δ1 Θ1 e Expr.BIT ->
      WellTyped Γ Δ2 Θ2 P1 τ ->
      WellTyped Γ Δ2 Θ2 P2 τ ->

      Var.Map.Partition Δ Δ1 Δ2 ->
      Var.Map.Partition Θ Θ1 Θ2 ->

      WellTyped Γ Δ Θ (SendIf e tgts P1 P2) τ
    .

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


Definition option_let_in (A : Actor.t) (p : option Pattern.t) (P1 P2 : option Process.t) : option Process.t :=
  match p, P1, P2 with
  | Some p', Some P1', Some P2' => Some (Process.LetIn p' P1' P2')
  | _, None, Some P2'           => Some P2'
  | Some p', Some P1', None     => Some (Process.LetIn p' P1' Process.Unit)
  | _, _, _                     => None
  end.


Fixpoint epp (A : Actor.t) (c : Choreography.t) : option Process.t :=
  match c with

  | Choreography.Loc B e =>
    if Actor.eq_dec A B
    then Some (Process.Ret e)
    else None

  | Choreography.Unit => None

  | Choreography.Pair C1 C2 =>
    match epp A C1, epp A C2 with
    | Some P1, Some P2 => Some (Process.Pair P1 P2)
    | Some P1, None    => Some P1
    | None,    Some P2 => Some P2
    | None,    None    => None
    end

  | Choreography.LetIn pat C1 C2 =>
    option_let_in A (Pattern.epp A pat) (epp A C1) (epp A C2)

  | Choreography.Send B1 e B2 =>
    if Actor.eq_dec A B1
    then Some (Process.Send e B2)
    else if Actor.eq_dec A B2
    then Some (Process.Receive B1)
    else None

  | Choreography.EPR B1 B2 =>
    if Actor.eq_dec A B1
    then Some (Process.EPR B2)
    else if Actor.eq_dec A B2
    then Some (Process.EPR B1)
    else None

  | Choreography.If B e C1 C2 =>
    let tgts := Actor.FSet.union (Choreography.actors C1) (Choreography.actors C2) in
    let P1 := match epp A C1 with 
                | Some P1 => P1
                | None => Process.Unit
                end in
    let P2 := match epp A C2 with 
                | Some P2 => P2
                | None => Process.Unit
                end in

    if Actor.eq_dec A B
    then Some (Process.SendIf e tgts P1 P2)
    else if Actor.Map.FSetProofs.in_dec A tgts
    then Some (Process.ReceiveIf A P1 P2)
    else None

end.

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

Lemma epp_WellTyped : forall G D T C τ,
  Choreography.WellTyped G D T C τ ->
  forall A PA, epp A C = Some PA ->
  Process.WellTyped (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) PA (Typ.epp A τ).
Proof.
  intros G D T C τ HWT.
  induction HWT; intros A0 PA0 HPA0;
    simpl in *;
    try discriminate.
  *  admit (* let in *).
  * Actor.Map.Tactics.compare A0 A; try discriminate.
    inversion HPA0; subst; auto.
    constructor; auto.

  * destruct (epp A0 C1) as [P1 | ] eqn:HP1.
    + destruct (epp A0 C2) as [P2 | ] eqn:HP2.
      ++ inversion HPA0; subst; clear HPA0.
         apply IHHWT1 in HP1. 
         apply IHHWT2 in HP2.
         admit (* not sure about the typing of tensor here...
          maybe we need a local unit type to handle send? *).

      ++ eapply epp_WellTyped_None in HP2; eauto.
         rewrite HP2.
         replace (Typ.tensor (Typ.epp A0 tau1) None)
          with (Typ.epp A0 tau1).
          2:{
            destruct (Typ.epp A0 tau1); auto.
          }
          inversion HPA0; subst; clear HPA0.
          (* weakening of the typing contexts *)
          admit.


    + eapply epp_WellTyped_None in HP1; eauto.
      rewrite HP1. simpl.
      destruct (epp A0 C2) as [P2 | ] eqn:HP2; try discriminate.
      inversion HPA0; subst; clear HPA0.
      admit (* weakening of typing contexts *).
    

  * Actor.Map.Tactics.compare A0 A; try discriminate.
    + (* A0 = A *) inversion HPA0; subst; clear HPA0.
      Actor.Map.Tactics.compare A0 B.
      { admit (* can't have self-send... *). }
      econstructor; eauto.
    + (* A0 <> A *)
      Actor.Map.Tactics.compare A0 B; try discriminate.
      inversion HPA0; subst; clear HPA0.
      econstructor; eauto.
      { 
        apply H0. Actor.simplify.
      }
      {
        apply H1. Actor.simplify.
      } 
    
  * Actor.Map.Tactics.compare A0 A; try discriminate.
    + (* A0 = A *) inversion HPA0; subst; clear HPA0.
      Actor.Map.Tactics.compare A B.
      { admit (* can't have self-send... *). }
      simpl. econstructor; eauto.
      { specialize (H A). Var.solve. }
      { specialize (H0 A). Var.solve. }
    + (* A0 <> A *)
      Actor.Map.Tactics.compare A0 B; try discriminate.
      inversion HPA0; subst; clear HPA0.
      simpl.
      econstructor; eauto.
      { specialize (H B). Var.solve. }
      { specialize (H0 B). Var.solve. }

  * (* If *) admit.
Admitted. 


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
