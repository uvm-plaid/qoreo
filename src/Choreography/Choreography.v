(** 
Definition of choreographic language

Data structures:

  - `Insn.t`, `Expr.t` - Choreographic instructions and choreographies, respectively
  - `step` - small-step operational semantics
  - `WellTyped` - typing relation

Theorems:
  - `wt_subst_lin`, `wt_subst_bang`: substitution lemmas for linear and non-linear variables respectively
  - `WellTyped_preservation`: preservation of the typing relation with respect to the step relation
  - `WellScoped_preservation`: preservation of the configuration well-scopedness relation with respect to the step relation
  - `preservation`: conjunction of the previous two lemmas
  - 'progress': well-typed choreographies are either values or can take a step
  - `safety`: top-level type safety theorem


*)

From Qoreo.Base Require Var Actor Config ChorEnv.
From Qoreo.Expr Require Expr BaseProofs.


From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms (* for Proper *).


Module Label.
    Inductive t :=
    | Send : Actor.t -> Expr.t -> Actor.t -> t
    | EPR  : Actor.t -> Actor.t -> t
    | Loc  : Actor.t -> t
    (*| Subst : Actor.FSet.t -> t (* possibly multiple local actions happening at once *) *)
    | Epsilon (* don't count these *) : t
    | If   : Actor.t -> bool -> Actor.FSet.t -> t
    .

    Inductive WellFormed : Label.t -> Prop :=
    | WFLSend : forall A v B, A <> B -> WellFormed (Send A v B)
    | WFLEPR : forall A B, A <> B -> WellFormed (EPR A B)
    | WFLLoc : forall A, WellFormed (Loc A)
    | WFLIf  : forall A v Bs, ~ Actor.FSet.In A Bs ->
               WellFormed (If A v Bs)
    .

    Definition actors (l : t) : Actor.FSet.t :=
        match l with
        | Send A _ B | EPR A B => Actor.FSet.add A (Actor.FSet.singleton B)
        | Loc A    => Actor.FSet.singleton A
        (*| Subst As => As*)
        | Epsilon => Actor.FSet.empty
        | If A _ Bs => Actor.FSet.add A Bs
        end.
End Label.

Module Typ.
  Inductive t :=
  | Local : Actor.t -> Expr.typ -> t
  | Unit : t
  | Pair : t -> t -> t
  .

  Fixpoint actors (typ : t) : Actor.FSet.t :=
    match typ with
    | Local A _ => Actor.FSet.singleton A
    | Unit => Actor.FSet.empty
    | Pair typ1 typ2 => Actor.FSet.union (actors typ1) (actors typ2)
    end.
End Typ.

(* TODO: move to ChorEnv module *)
Notation "T '!' A" := (ChorEnv.find A T)
  (no associativity, at level 60).
Import List.ListNotations.


Module Pattern.
  Inductive t :=
  | Var : Actor.t -> Var.t -> t
  | Unit : t
  | Pair : t -> t -> t
  | Bang : Actor.t -> Var.t -> t
  .

  Fixpoint actors (p : t) : Actor.FSet.t :=
    match p with
    | Var A _ | Bang A _ => Actor.FSet.singleton A
    | Unit => Actor.FSet.empty
    | Pair p1 p2 => Actor.FSet.union (actors p1) (actors p2)
    end.

    Fixpoint in_pat A (x : Var.t) (p : Pattern.t) : bool :=
      match p with
      | Pattern.Var B y | Pattern.Bang B y =>
        if Actor.eq_dec A B 
        then if Var.eq_dec x y then true else false
        else false
      | Pattern.Unit => false
      | Pattern.Pair p1 p2 => in_pat A x p1 || in_pat A x p2
      end.

  Inductive WellTyped : ChorEnv.t Expr.typ -> ChorEnv.t Expr.typ -> t -> Typ.t -> Prop :=
  | WTVar : forall G D A x tau,

    ChorEnv.Empty G ->
    ChorEnv.EmptyExcept (Actor.FSet.singleton A) D ->
    Var.Map.Singleton x tau (D!A) ->

    WellTyped G D (Var A x) (Typ.Local A tau)

  | WTUnit : forall G D,
    ChorEnv.Empty G ->
    ChorEnv.Empty D ->
    WellTyped G D Unit Typ.Unit

  | WTPair : forall G1 G2 D1 D2 G D p1 p2 tau1 tau2,
    
    WellTyped G1 D1 p1 tau1 ->
    WellTyped G2 D2 p2 tau2 ->

    ChorEnv.Partition D D1 D2 ->
    ChorEnv.Partition G G1 G2 ->

    WellTyped G D (Pair p1 p2) (Typ.Pair tau1 tau2)

  | WTBang : forall G D A x tau,

    ChorEnv.EmptyExcept (Actor.FSet.singleton A) G ->
    Var.Map.Singleton x tau (G!A) ->
    ChorEnv.Empty D ->

    WellTyped G D (Bang A x) (Typ.Local A (Expr.BANG tau))
  .


  Lemma WellTypedProper' : forall G D p tau,
    WellTyped G D p tau ->
    forall G' D',
    ChorEnv.Equal G G' ->
    ChorEnv.Equal D D' -> 
    WellTyped G' D' p tau.
  Admitted.
  #[global] Instance WellTypedProper : Proper (ChorEnv.Equal ==> ChorEnv.Equal ==> eq ==> eq ==> iff) WellTyped.
  Proof.
    intros ? ? HG ? ? HD ? p ? ? tau ?; subst.
    split; intros; eapply WellTypedProper'; eauto;
      symmetry; auto.
  Qed.
End Pattern.


Module Choreography.
    Inductive t : Type :=

    (*| Var   : Actor.t -> Var.t -> t*)
    | LetIn : Pattern.t -> t -> t -> t

    | Loc : Actor.t -> Expr.t -> t

    | Unit   : t
    | Pair    : t -> t -> t
    (*| Bang    : t -> t*)
    | Send : Actor.t -> Expr.t -> Actor.t -> t
    | EPR : Actor.t -> Actor.t -> t
    | If  : Actor.t -> Expr.t -> t -> t -> t
    .

    Fixpoint actors (C : t) : Actor.FSet.t :=
      match C with
      | Loc A _ (*| Var A _*) => Actor.FSet.singleton A
      | LetIn p C1 C2 =>
        Actor.FSet.union (Pattern.actors p) (Actor.FSet.union (actors C1) (actors C2))
      
      | Unit => Actor.FSet.empty
      | Pair C1 C2 =>
          Actor.FSet.union (actors C1) (actors C2)
      | Send A _ B | EPR A B =>
          Actor.FSet.add A (Actor.FSet.singleton B)
      | If A _ C1 C2 =>
        Actor.FSet.add A (Actor.FSet.union (actors C1) (actors C2))
      end.


    Fixpoint subst A (x : Var.t) (v : Expr.t) (C : t) : t :=
      match C with
      | Loc B e => Loc B (if Actor.eq_dec A B then Expr.subst x v e else e)
      (*| Var B y =>
        if Actor.eq_dec A B 
        then if Var.eq_dec x y then Loc A v else Var B y
        else Var B y*)
      | LetIn p C1 C2 =>
          LetIn p (subst A x v C1) (if Pattern.in_pat A x p then C2 else subst A x v C2)

      | Unit => Unit
      | Pair C1 C2 => Pair (subst A x v C1) (subst A x v C2)
      | Send B1 e B2 => Send B1 (if Actor.eq_dec A B1 then Expr.subst x v e else e) B2
      | EPR B1 B2 => EPR B1 B2
      | If B e C1 C2 =>
        If B (if Actor.eq_dec A B then Expr.subst x v e else e)
           (subst A x v C1)
           (subst A x v C2)
      end.


    
    Inductive Val : t -> Prop :=
    | VLoc : forall A v, Expr.Val v -> Val (Loc A v)
    | VUnit : Val Unit
    | VPair : forall v1 v2, Val v1 -> Val v2 -> Val (Pair v1 v2)
    .

    (* Assume v is a value of the same type as p *)
    Fixpoint subst_pat (p : Pattern.t) (v : t) (C : t) : t :=
      match p, v with
      | Pattern.Var A x, Loc A' v' =>
        if Actor.eq_dec A A' then subst A x v' C else C
      | Pattern.Bang A x, Loc A' (Expr.Bang e') =>
        if Actor.eq_dec A A' then subst A x e' C else C
      | Pattern.Unit, _ => C
      | Pattern.Pair p1 p2, Pair v1 v2 =>
        subst_pat p1 v1 (subst_pat p2 v2 C)

      | _, _ => C
      end.


  (* TODO: lemmas about the actors that occur in (subst ...) and (subst ...) *)


    Definition rebound_in A (x : Var.t) (C : t) : bool :=
      match C with
      | LetIn p _ _ => Pattern.in_pat A x p
      | _ => false
      end.

End Choreography.
Import Choreography.

    Inductive step :
              Choreography.t -> ChorEnv.t nat -> Config.t ->
              Label.t ->
              Choreography.t -> ChorEnv.t nat -> Config.t ->
              Prop :=

    | LetInC : forall (p : Pattern.t) C1 C2 T cfg l C1' T' cfg',
      step C1 T cfg l C1' T' cfg' ->

      step (LetIn p C1 C2) T cfg l (LetIn p C1' C2) T' cfg'

    | LetInVarB  : forall A x v C T cfg C' T' cfg',

      Expr.Val v ->

      C' = subst A x v C ->
      ChorEnv.Equal T' T ->
      cfg' = cfg ->

      step (LetIn (Pattern.Var A x) (Loc A v) C) T cfg
           (Label.Loc A)
           C' T' cfg'
    | LetInBangB  : forall A x e C T cfg C' T' cfg',

      C' = subst A x e C ->
      ChorEnv.Equal T' T ->
      cfg' = cfg ->

      step (LetIn (Pattern.Bang A x) (Loc A (Expr.Bang e)) C) T cfg
           (Label.Loc A)
           C' T' cfg'

    | LetInPairB : forall p1 p2 v1 v2 C T cfg T' cfg',

      Val v1 -> Val v2 ->
      ChorEnv.Equal T' T ->
      cfg' = cfg ->

      step (LetIn (Pattern.Pair p1 p2) (Pair v1 v2) C) T cfg
           Label.Epsilon
           (LetIn p1 v1 (LetIn p2 v2 C)) T' cfg'

    | LetInUnitB : forall C T cfg T' cfg',

      ChorEnv.Equal T' T ->
      cfg' = cfg ->

      step (LetIn Pattern.Unit Unit C) T cfg
           Label.Epsilon
           C T' cfg'

    | LetInDelay : forall (p : Pattern.t) C1 C2 T cfg l C2' T' cfg',

      step C2 T cfg l C2' T' cfg' ->
      Actor.FSet.Empty (Actor.FSet.inter (Label.actors l) (Pattern.actors p)) ->

      step (LetIn p C1 C2) T cfg
           l
           (LetIn p C1 C2') T' cfg'

  
    | LocC : forall ThetaA' e A T cfg e' T' cfg',
      Expr.step e (ChorEnv.find A T) cfg e' ThetaA' cfg' ->
      ChorEnv.Equal T' (Actor.Map.add A ThetaA' T) ->

      step (Loc A e) T cfg
           (Label.Loc A)
           (Loc A e') T' cfg'
    
    | PairC1 : forall (C1 C2 : t) T cfg l C1' T' cfg',
      step C1 T cfg l C1' T' cfg' ->
      step (Pair C1 C2) T cfg l (Pair C1' C2) T' cfg'
    
    | PairC2 : forall (C1 C2 : t) T cfg l C2' T' cfg',
      step C2 T cfg l C2' T' cfg' ->
      step (Pair C1 C2) T cfg l (Pair C1 C2') T' cfg'

    | SendC : forall ThetaA' A e e' B T cfg T' cfg',
      Expr.step e (ChorEnv.find A T) cfg e' ThetaA' cfg' ->

      ChorEnv.Equal T' (Actor.Map.add A ThetaA' T) ->
      cfg' = cfg ->
      
      step (Send A e B) T cfg
           (Label.Loc A)
           (Send A e' B) T' cfg'

    | SendB : forall A v B T cfg T' cfg',

      Expr.Val v ->
      ChorEnv.Equal T' T ->
      cfg' = cfg ->

      step (Send A v B) T cfg
           (Label.Send A v B)
           (Loc B v) T' cfg'


  | EPRB : forall q1 q2 T0 A B T cfg C' T' cfg',

      C' = (Pair (Loc A (Expr.QRef q1)) (Loc B (Expr.QRef q2))) ->
      ChorEnv.epr A B T cfg = (q1, q2, T0, cfg') ->
      ChorEnv.Equal T' T0 ->

      step (EPR A B) T cfg
           (Label.EPR A B) 
           C' T' cfg'
  (* Do we also need EPRB'? *)

  | IfC : forall ThetaA' A e e' C1 C2 T cfg T' cfg',
      Expr.step e (ChorEnv.find A T) cfg e' ThetaA' cfg' ->

      ChorEnv.Equal T' (Actor.Map.add A ThetaA' T) ->
      cfg' = cfg ->
      
      step (If A e C1 C2) T cfg
           (Label.Loc A)
           (If A e' C1 C2) T' cfg'

  | IfB : forall A (C1 C2 : t) T cfg (b : bool) X C' T' cfg',

      (C' = if b then C1 else C2) ->
      Actor.FSet.Equal X (Actor.FSet.remove A (Actor.FSet.union (actors C1) (actors C2))) ->

      ChorEnv.Equal T' T ->
      cfg' = cfg ->

      step (If A (Expr.Bit b) C1 C2) T cfg
           (Label.If A b X)
           C' T' cfg'
  .


Lemma stepProper' : forall C Theta1 cfg l C' Theta1' cfg',
  Choreography.step C Theta1 cfg l C' Theta1' cfg' ->
  forall Theta2 Theta2',
    ChorEnv.Equal Theta1 Theta2 ->
    ChorEnv.Equal Theta1' Theta2' ->
    Choreography.step C Theta2 cfg l C' Theta2' cfg'.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep; intros Theta2 Theta2' Heq Heq';
    try rewrite Heq in *;
    try rewrite Heq' in *;
    try (econstructor; eauto; fail).
  * (* EPR case *)
    unfold ChorEnv.epr in *.
    destruct (Config.epr_cfg cfg) as [[q1' q2'] cfg0]
      eqn:Hcfg.
    inversion H0; subst; clear H0.
    eapply EPRB. eauto.
    {
      unfold ChorEnv.epr.
      rewrite Hcfg.
      reflexivity.
    }
    rewrite <- Heq.
    auto.
Qed.


Global Instance stepProper : Proper (eq ==> ChorEnv.Equal ==> eq ==> eq ==> eq ==> ChorEnv.Equal ==> eq ==> iff) (Choreography.step).
Proof.
  intros ? C ? Theta1 Theta2 HTheta ? cfg ? ? l ? ? C' ? Theta1' Theta2' HTheta' ? cfg' ?; subst.
  split; intros Hstep; eapply stepProper'; eauto.
  all: (symmetry; auto).
Qed.


Inductive multi_step : Choreography.t -> ChorEnv.t nat -> Config.t -> Choreography.t -> ChorEnv.t nat -> Config.t -> Prop :=
| Step0 : forall e Theta cfg, multi_step e Theta cfg e Theta cfg
| Step1 : forall e1 e2 e3 Theta1 Theta2 Theta3 cfg1 cfg2 cfg3 l,
  step e1 Theta1 cfg1 l e2 Theta2 cfg2 ->
  multi_step e2 Theta2 cfg2 e3 Theta3 cfg3 ->
  multi_step e1 Theta1 cfg1 e3 Theta3 cfg3.


(** Typing Relation *)
Inductive WellTyped :
  ChorEnv.t Expr.typ -> ChorEnv.t Expr.typ -> ChorEnv.t nat -> Choreography.t -> Typ.t -> Prop :=

(*
| WTVar : forall G D T A x (tau : Expr.typ),
  ~ Var.Map.In x (G!A) ->
  ChorEnv.Equal D (Actor.Map.singleton A (Var.Map.singleton x tau)) ->
  ChorEnv.Empty T ->

  WellTyped G D T (Choreography.Var A x) (Typ.Local A tau)
  *)

| WTLetIn : forall tau D1 D2 T1 T2 G' G1' D1' D' T G D p C1 C2 tau',
  WellTyped G D1 T1 C1 tau ->
  Pattern.WellTyped G1' D1' p tau ->
  WellTyped G' D' T2 C2 tau' ->

  ChorEnv.Partition D D1 D2 ->
  ChorEnv.Partition D' D1' D2 ->
  ChorEnv.Partition T T1 T2 ->
  ChorEnv.Partition G' G G1' ->
  
  WellTyped G D T (LetIn p C1 C2) tau'

| WTLoc : forall G D T A e tau,

  Expr.WellTyped (G!A) (D!A) (T!A) e tau ->

  ChorEnv.EmptyExcept (Actor.FSet.singleton A) D ->
  ChorEnv.EmptyExcept (Actor.FSet.singleton A) T ->

  WellTyped G D T (Loc A e) (Typ.Local A tau)

| WTUnit : forall G D T,
  ChorEnv.Empty D ->
  ChorEnv.Empty T ->
  WellTyped G D T Unit Typ.Unit

| WTPair : forall D1 D2 T1 T2 G D T C1 C2 tau1 tau2,

  WellTyped G D1 T1 C1 tau1 ->
  WellTyped G D2 T2 C2 tau2 ->

  ChorEnv.Partition D D1 D2 ->
  ChorEnv.Partition T T1 T2 ->

  WellTyped G D T (Pair C1 C2) (Typ.Pair tau1 tau2)

| WTSend : forall G D T A e B tau,

    Expr.WellTyped (G!A) (D!A) (T!A) e (Expr.BANG tau) ->

    ChorEnv.EmptyExcept (Actor.FSet.singleton A) D ->
    ChorEnv.EmptyExcept (Actor.FSet.singleton A) T ->

    WellTyped G D T (Choreography.Send A e B) (Typ.Local B (Expr.BANG tau))

| WTEPR : forall G D T A B,

    ChorEnv.Empty D ->
    ChorEnv.Empty T ->

    WellTyped G D T (Choreography.EPR A B) (Typ.Pair (Typ.Local A Expr.QUBIT) (Typ.Local B Expr.QUBIT))

| WTIf : forall D' T' DeltaA ThetaA G D T A e C1 C2 tau,

    Expr.WellTyped (G!A) DeltaA ThetaA e Expr.BIT ->
    WellTyped G D' T' C1 tau ->
    WellTyped G D' T' C2 tau ->

    ChorEnv.Partition D (Actor.Map.singleton A DeltaA) D' ->
    ChorEnv.Partition T (Actor.Map.singleton A ThetaA) T' ->

    WellTyped G D T (Choreography.If A e C1 C2) tau
.


Lemma WellTypedProper' : forall G D T C tau,
  WellTyped G D T C tau ->
  forall G' D' T',
  ChorEnv.Equal G G' ->
  ChorEnv.Equal D D' -> 
  ChorEnv.Equal T T' ->
  WellTyped G' D' T' C tau.
Proof.
  intros G D T C tau HWT.
  induction HWT; intros G0' D0' T0' HG HD HT;
    try (constructor;
      try rewrite <- HG;
      try rewrite <- HD;
      try rewrite <- HT;
      auto).
  * econstructor.
    { eapply IHHWT1; eauto; reflexivity. }
    { eauto. }
    { eapply IHHWT2; eauto; reflexivity. }
    { rewrite <- HD. eauto. }
    { eauto. }
    { rewrite <- HT; auto. }
    { rewrite <- HG; eauto. }

  * econstructor;
      try rewrite <- HD;
      try rewrite <- HT;
      eauto.
    { eapply IHHWT1; eauto; reflexivity. }
    { eapply IHHWT2; eauto; reflexivity. }

  * econstructor;
      try rewrite <- HG;
      try rewrite <- HD;
      try rewrite <- HT;
      eauto.
    { eapply IHHWT1; eauto; reflexivity. }
    { eapply IHHWT2; eauto; reflexivity. }
Qed.
    
Global Instance WellTypedProper :
  Proper (ChorEnv.Equal ==> ChorEnv.Equal ==> ChorEnv.Equal ==> eq ==> eq ==> iff) WellTyped.
Proof.
  intros G1 G2 HG D1 D2 HD T1 T2 HT ? e ? ? tau ?; subst.
  split; intros; eapply WellTypedProper'; eauto;
    symmetry; auto.
Qed.

