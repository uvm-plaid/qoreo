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
From Qoreo.Expr Require Expr Proofs.


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
    .

    Inductive WellFormed : Label.t -> Prop :=
    | WFLSend : forall A v B, A <> B -> WellFormed (Send A v B)
    | WFLEPR : forall A B, A <> B -> WellFormed (EPR A B)
    | WFLLoc : forall A, WellFormed (Loc A)
    .

    Definition actors (l : t) : Actor.FSet.t :=
        match l with
        | Send A _ B | EPR A B => Actor.FSet.add A (Actor.FSet.singleton B)
        | Loc A => Actor.FSet.singleton A
        end.
End Label.

Module Insn.
    Inductive t : Type :=

    | Send : Actor.t -> Expr.t -> Actor.t -> Var.t -> t
    | EPR : Actor.t -> Var.t -> Actor.t -> Var.t -> t

    | Let : Actor.t -> Var.t -> Expr.t -> t
    | LetBang : Actor.t -> Var.t -> Expr.t -> t
    | LetPair : Actor.t -> Var.t -> Var.t -> Expr.t -> t.


    Definition actors (I : t) : Actor.FSet.t :=
        match I with
        | Send A _ B _ | EPR A _ B _ => Actor.FSet.add A (Actor.FSet.singleton B)
        | Let A _ _ | LetBang A _ _ | LetPair A _ _ _ => Actor.FSet.singleton A
        end.


    Inductive WellFormed : t -> Prop :=
    | WFSend : forall A v B x,
      A <> B -> WellFormed (Send A v B x)
    | WFEPR : forall A x B y,
      A <> B -> WellFormed (EPR A x B y)
    | WFLet : forall A x e, WellFormed (Let A x e)
    | WFLetBang : forall A x e, WellFormed (LetBang A x e)
    | WFLetPair : forall A x1 x2 e, WellFormed (LetPair A x1 x2 e)
    .
    
    (* substitute the value v for A.x in I *)
    Definition subst (A : Actor.t) (x : Var.t) (v : Expr.t)  (I : t) : t :=
    match I with
    | Send B1 e B2 y => 
        (* Assume x <> y *)
        let e' := if Actor.eq_dec A B1 then Expr.subst x v e else e in
        Send B1 e' B2 y
    | EPR B1 y1 B2 y2 => EPR B1 y1 B2 y2
    | Let B y e =>
        let e' := if Actor.eq_dec A B then Expr.subst x v e else e in
        Let B y e'
    | LetBang B y e =>
        let e' := if Actor.eq_dec A B then Expr.subst x v e else e in
        LetBang B y e'
    | LetPair B y1 y2 e =>
        let e' := if Actor.eq_dec A B then Expr.subst x v e else e in
        LetPair B y1 y2 e'
    end.


    Lemma actors_subst : forall I B x v,
      Actor.FSet.Equal
        (actors (subst B x v I))
        (actors I).
    Proof.
      destruct I; intros; Actor.simplify.
    Qed.
    #[global] Hint Rewrite actors_subst : actor_db.

    Definition bindt : Type := Actor.t * Var.t.
    
    Definition bind_eq  (Ax : bindt) (By: bindt) : Prop := (fst Ax) = (fst By) /\ (snd Ax) = (snd By).

    Lemma beq : forall Ax By, (bind_eq Ax By) <-> ((fst Ax) = (fst By) /\ (snd Ax) = (snd By)).
      Proof.
        intros.
        split.
        { intros. unfold bind_eq in H. auto. }
        { intros. unfold bind_eq. auto. }
      Qed.
        
    Lemma nbeq : forall Ax By, ((fst Ax) <> (fst By) \/ (snd Ax) <> (snd By)) <-> ~(bind_eq Ax By).
    Proof.
      intros.
      split.
      { intros. unfold bind_eq. tauto. }
      { intros. unfold bind_eq in H. tauto. }
    Qed.

    Lemma nbeqlr : forall Ax By, ((fst Ax) <> (fst By) \/ (snd Ax) <> (snd By)) -> ~(bind_eq Ax By).
    Proof.
      intros.
      pose proof (nbeq Ax By) as Hnbeq.
      destruct Hnbeq as [HnbeqA _].
      apply HnbeqA.
      auto.
    Qed.
           
    Lemma bind_eq_symmetric : forall Ax By, bind_eq Ax By -> bind_eq By Ax.
    Proof.
      intros (A,x) (B,y) H.
      unfold bind_eq.
      unfold bind_eq in H.
      intuition.
    Qed.
           
    Lemma bind_neq_symmetric : forall Ax By, ~ bind_eq Ax By -> ~ bind_eq By Ax.
    Proof.
      intros (A,x) (B,y) H.
      unfold bind_eq.
      unfold bind_eq in H.
      intuition.
    Qed.
    
    Definition bind_eq_dec  (Ax : bindt) (By: bindt) : {bind_eq Ax By} + {~(bind_eq Ax By)} :=
      match ((Actor.eq_dec (fst Ax) (fst By)), (Var.eq_dec (snd Ax) (snd By))) with
      | (left pt1, left pt2) => left (conj pt1 pt2)
      | (right pt1, _) => right (nbeqlr Ax By (or_introl pt1))
      | (_, right pt2) => right (nbeqlr Ax By (or_intror pt2))
      end.

    (* Unwieldy but leaving as advanced technical example. *)
    (* Definition bind_eqb (Ax : bindt) (By: bindt) : bool :=
       match (bool_of_sumbool (bind_eq_dec Ax By)) with
       | exist _ x _ => x
       end. *)

    Definition bind_eqb (Ax : bindt) (By: bindt) : bool :=
      if (bind_eq_dec Ax By) then true else false.

    Lemma bind_eqb_true : forall Ax By, 
      bind_eqb Ax By = true <-> bind_eq Ax By.
    Proof.
      intros.
      split.
      {
        intros.
        pose proof (beq Ax By) as Hbeq.
        destruct Hbeq as [HbeqA HbeqB].
        apply HbeqB.
        unfold bind_eqb in H.
        (* NOTE destruction of dependent type with desired spec! *)
        destruct (bind_eq_dec Ax By) in H.
        {
          specialize (HbeqA b).
          auto.
        }
        { discriminate. }
      }
      {
        intros.
        unfold bind_eqb.
        destruct (bind_eq_dec Ax By).
        { reflexivity. }
        { contradiction. }
      }
    Qed.

    Lemma bind_eqb_false : forall Ax By, 
      bind_eqb Ax By = false <-> ~ bind_eq Ax By.
    Proof.
      intros.
      split.
      {
        intros.
        pose proof (nbeq Ax By) as Hnbeq.
        destruct Hnbeq as [HnbeqA HnbeqB].
        apply HnbeqA.
        unfold bind_eqb in H.
        (* NOTE destruction of dependent type with desired spec! *)
        destruct (bind_eq_dec Ax By) in H.
        { discriminate. }
        {
          apply HnbeqB in n.
          auto.
        }
      }
      {
        intros.
        unfold bind_eqb.
        destruct (bind_eq_dec Ax By).
        { contradiction. }
        { reflexivity. }
      }
    Qed.

    Lemma bind_eqb_symmetric : forall Ax By, bind_eqb Ax By = bind_eqb By Ax.
    Proof.
      intros.

      pose proof (bind_eq_symmetric By Ax) as Hbeqs.
      pose proof (bind_neq_symmetric By Ax) as Hbneqs.
      
      destruct (bind_eqb By Ax) eqn:Heqb.
      {
        pose proof (bind_eqb_true Ax By) as HbeqABt.
        destruct HbeqABt as [HbeqABtA HbeqABtB].
        pose proof (bind_eqb_true By Ax) as HbeqBAt.
        destruct HbeqBAt as [HbeqBAtA HbeqBAtB].
        
        apply HbeqABtB.
        specialize (HbeqBAtA Heqb).
        specialize (Hbeqs HbeqBAtA).
        auto.
      }
      {        
        pose proof (bind_eqb_false Ax By) as HbeqABf.
        destruct HbeqABf as [HbeqABfA HbeqABfB].
        pose proof (bind_eqb_false By Ax) as HbeqBAf.
        destruct HbeqBAf as [HbeqBAfA HbeqBAfB].
        
        apply HbeqABfB.        
        specialize (HbeqBAfA Heqb).
        specialize (Hbneqs HbeqBAfA).
        auto.
      }

    Qed.
    
    Definition rebound_in (A : Actor.t) (x : Var.t) (I : t) : bool :=
      match I with
      | Send B1 e B2 y => bind_eqb (A,x) (B2,y)    
      | EPR B1 y1 B2 y2 => (bind_eqb (A,x) (B1,y1)) || (bind_eqb (A,x) (B2,y2))
      | Let B y e => bind_eqb (A,x) (B,y) 
      | LetBang B y e => bind_eqb (A,x) (B,y) 
      | LetPair B y1 y2 e => (bind_eqb (A,x) (B,y1)) || (bind_eqb (A,x) (B,y2)) 
    end.

    Inductive stepC : 
              Insn.t -> ChorEnv.t nat -> Config.t ->
              Label.t ->
              Insn.t -> ChorEnv.t nat -> Config.t -> Prop :=
    | SendC : forall TA' A e B x T cfg e' T' cfg',
      Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->
      ChorEnv.Equal T' (Actor.Map.add A TA' T) ->
      stepC (Insn.Send A e B x) T cfg
            (Label.Loc A)
            (Insn.Send A e' B x) T' cfg'
    | LetC : forall TA' A x e T cfg e' T' cfg',
      Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->
      ChorEnv.Equal T' (Actor.Map.add A TA' T) ->
      stepC (Insn.Let A x e) T cfg
            (Label.Loc A)
            (Insn.Let A x e') T' cfg'
    | LetBangC : forall TA' A x e T cfg e' T' cfg',
      Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->
      ChorEnv.Equal T' (Actor.Map.add A TA' T) ->
      stepC (Insn.LetBang A x e) T cfg
            (Label.Loc A)
            (Insn.LetBang A x e') T' cfg'
    | LetPairC : forall TA' A x1 x2 e T cfg e' T' cfg',
      Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->
      ChorEnv.Equal T' (Actor.Map.add A TA' T) ->
      stepC (Insn.LetPair A x1 x2 e) T cfg
            (Label.Loc A)
            (Insn.LetPair A x1 x2 e') T' cfg'
    .
End Insn.

Module Choreography.
    (*Definition t := list Insn.t.*)

    (* type t = Empty | Seq of t * t *)
    Inductive t : Type :=
    | Empty : t
    | Do : Insn.t -> t -> t
    (* If A e C1 C2 C
        ==
       If A.e then C1 else C2 ; C *)
    | If : Actor.t -> Expr.t -> t -> t -> t -> t
    (* No selection tags *)
    .
    (* TOOD: update processes, update EPP *)

    Fixpoint seq (C1 C2 : t) : t :=
    match C1 with
    | Empty => C2
    | Do I0 C1' => Do I0 (seq C1' C2)
    | If A e C11 C12 C1' =>
      If A e C11 C12 (seq C1' C2)
    end.

    Fixpoint actors (C : t) : Actor.FSet.t :=
      match C with
      | Empty => Actor.FSet.empty
      | Do I0 C' => Actor.FSet.union (Insn.actors I0) (actors C')
      | If A e C1 C2 C0 => Actor.FSet.add A (Actor.FSet.union (actors C1) (Actor.FSet.union (actors C2) (actors C0)))
      end.
    
    Inductive WellFormed : t -> Prop :=
    | WFEmpty : WellFormed Empty
    | WFDo : forall I C,
      Insn.WellFormed I -> WellFormed C -> WellFormed (Do I C)
    | WFIf : forall A e C1 C2 C,
      WellFormed C1 ->
      WellFormed C2 ->
      WellFormed C ->
      WellFormed (If A e C1 C2 C)
    .

    Fixpoint subst (A : Actor.t) (x : Var.t) (v : Expr.t) (C : t) : t :=
      match C with
      | Empty => Empty
      | (Do Ins C') => 
        Do (Insn.subst A x v Ins)
           (if (Insn.rebound_in A x Ins)
            then C'
            else (subst A x v C'))
      | If B e C1 C2 C =>
        If B (if Actor.eq_dec A B then Expr.subst x v e else e)
             (subst A x v C1)
             (subst A x v C2)
             (subst A x v C)
      end.

    Lemma actors_subst : forall C A x v,
      Actor.FSet.Equal
        (actors (subst A x v C))
        (actors C).
    Proof.
      induction C as [ | I C | ]; intros A x v; simpl; Actor.simplify.
      * destruct (Insn.rebound_in A x I); try reflexivity.
        rewrite IHC; reflexivity.
      * rewrite IHC1, IHC2, IHC3. reflexivity.
    Qed.
    #[global] Hint Rewrite actors_subst : actor_db.
End Choreography.


(** Semantics **)

Inductive stepB : Choreography.t -> ChorEnv.t nat -> Config.t ->
                 Label.t ->
                 Choreography.t -> ChorEnv.t nat -> Config.t -> Prop :=
  | IfB : forall A (b : bool) C1 C2 C T cfg C' T' cfg',
    C' = Choreography.seq (if b then C1 else C2) C ->
    ChorEnv.Equal T' T ->
    cfg' = cfg ->
    stepB (Choreography.If A (Expr.Bit b) C1 C2 C) T cfg
          (Label.Loc A) (*??? do we need a new label that covers all actors in the if? *)
          C' T' cfg'

  | SendB : forall A v B x C refs refs' cfg C',
      C' = Choreography.subst B x v C ->
      ChorEnv.Equal refs refs' ->

      stepB (Choreography.Do (Insn.Send A (Expr.Bang v) B x) C) refs cfg
            (Label.Send A v B)
            C' refs' cfg

  | EPRB : forall q1 q2 T0 A x B y C T cfg C' T' cfg',
      ChorEnv.epr A B T cfg = (q1, q2, T0, cfg') ->
      ChorEnv.Equal T' T0 ->

      C' = Choreography.subst A x (Expr.QRef q1) (Choreography.subst B y (Expr.QRef q2) C) ->

      stepB (Choreography.Do (Insn.EPR A x B y) C) T cfg
            (Label.EPR A B) 
            C' T' cfg'

  | EPRB' : forall q1 q2 T0 A x B y C T cfg C' T' cfg',
      ChorEnv.epr B A T cfg = (q2, q1, T0, cfg') ->
      ChorEnv.Equal T' T0 ->

      C' = Choreography.subst A x (Expr.QRef q1) (Choreography.subst B y (Expr.QRef q2) C) ->

      stepB (Choreography.Do (Insn.EPR A x B y) C) T cfg
            (Label.EPR B A) 
            C' T' cfg'
    
  | LetB : forall A x v C refs refs' cfg C',
      Expr.Val v ->
      C' = Choreography.subst A x v C ->
      ChorEnv.Equal refs refs' ->
      stepB (Choreography.Do (Insn.Let A x v) C) refs cfg
            (Label.Loc A)
            C' refs' cfg

  | LetBangB : forall A x e0 C refs refs' cfg C',
      C' = Choreography.subst A x e0 C ->
      ChorEnv.Equal refs' refs ->
      stepB (Choreography.Do (Insn.LetBang A x (Expr.Bang e0)) C) refs cfg
            (Label.Loc A)
            C' refs' cfg

  | LetPairB : forall A x1 x2 v1 v2 C refs refs' cfg C',
      Expr.Val v1 -> Expr.Val v2 ->
      C' = Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C) ->
      ChorEnv.Equal refs' refs ->
      stepB  (Choreography.Do (Insn.LetPair A x1 x2 (Expr.Pair v1 v2)) C) refs cfg
            (Label.Loc A) 
            C' refs' cfg
.

(** NOTE: I had to change the EPR rule to ensure that the label is unordered *)
Inductive step : Choreography.t -> ChorEnv.t nat -> Config.t ->
                 Label.t ->
                 Choreography.t -> ChorEnv.t nat -> Config.t -> Prop :=

| StepC : forall I C T cfg l I' T' cfg',
  Insn.stepC I T cfg
             l
             I' T' cfg' ->
  step (Choreography.Do I C) T cfg
       l
       (Choreography.Do I' C) T' cfg'

| IfC : forall TA' A e C1 C2 C0 T cfg e' T' cfg',
  Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->
  ChorEnv.Equal T' (Actor.Map.add A TA' T) ->
  step (Choreography.If A e C1 C2 C0) T cfg
       (Label.Loc A)
       (Choreography.If A e' C1 C2 C0) T' cfg'

| StepB : forall C T cfg l C' T' cfg',
  stepB C T cfg
        l
        C' T' cfg' ->
  step  C T cfg
        l
        C' T' cfg'


(* delay *)
| Delay : forall I C T cfg C' T' cfg' l,
    step C T cfg l C' T' cfg' ->
    Actor.FSet.Empty (Actor.FSet.inter (Label.actors l) (Insn.actors I)) ->
    step (Choreography.Do I C) T cfg l (Choreography.Do I C') T' cfg'

| IfDelay : forall A e C1 C2 C T cfg C' T' cfg' l,
  step C T cfg
       l
       C' T' cfg' ->
  Actor.FSet.Empty (Actor.FSet.inter
      (Label.actors l)
      (Actor.FSet.add A (Actor.FSet.union (Choreography.actors C1) (Choreography.actors C2)))) ->
  step (Choreography.If A e C1 C2 C) T cfg
       l
       (Choreography.If A e C1 C2 C') T' cfg'
.

Lemma stepCProper' : forall I Theta1 cfg l I' Theta1' cfg',
  Insn.stepC I Theta1 cfg l I' Theta1' cfg' ->
  forall Theta2 Theta2',
    ChorEnv.Equal Theta1 Theta2 ->
    ChorEnv.Equal Theta1' Theta2' ->
    Insn.stepC I Theta2 cfg l I' Theta2' cfg'.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  destruct Hstep; intros ? ? Heq Heq';
  econstructor; try rewrite <- Heq; try rewrite <- Heq'; eauto.
Qed.

Global Instance stepCProper : Proper (eq ==> ChorEnv.Equal ==> eq ==> eq ==> eq ==> ChorEnv.Equal ==> eq ==> iff) (Insn.stepC).
Proof.
  intros ? C ? Theta1 Theta2 HTheta ? cfg ? ? l ? ? C' ? Theta1' Theta2' HTheta' ? cfg' ?; subst.
  split; intros Hstep.
  * eapply stepCProper'; eauto.
  * eapply stepCProper'; eauto. symmetry; auto. symmetry; auto.
Qed.


Lemma stepBProper' : forall C Theta1 cfg l C' Theta1' cfg',
  Choreography.stepB C Theta1 cfg l C' Theta1' cfg' ->
  forall Theta2 Theta2',
    ChorEnv.Equal Theta1 Theta2 ->
    ChorEnv.Equal Theta1' Theta2' ->
    Choreography.stepB C Theta2 cfg l C' Theta2' cfg'.
Proof.
  intros ? ? ? ? ? ? ? Hstep.
  induction Hstep; intros Theta2 Theta2' Heq Heq';
    try rewrite Heq in *;
    try rewrite Heq' in *;
    try (econstructor; eauto; fail).

  (* only EPR cases left *)
  * subst.

    apply (ChorEnv.chor_epr_eq Theta2) in H; auto.
    destruct H as [T0' [Heq'' H]].

    apply (Choreography.EPRB q1 q2 T0'); auto.
    { rewrite H0. rewrite Heq''. reflexivity. }

  * apply (ChorEnv.chor_epr_eq Theta2) in H; auto.
    destruct H as [T0' [Heq'' H]].

    apply (Choreography.EPRB' q1 q2 T0'); auto.
    {
      rewrite H0. rewrite Heq''. reflexivity.
    }
Qed.


Global Instance stepBProper : Proper (eq ==> ChorEnv.Equal ==> eq ==> eq ==> eq ==> ChorEnv.Equal ==> eq ==> iff) (Choreography.stepB).
Proof.
  intros ? C ? Theta1 Theta2 HTheta ? cfg ? ? l ? ? C' ? Theta1' Theta2' HTheta' ? cfg' ?; subst.
  split; intros Hstep; eapply stepBProper'; eauto.
  all: (symmetry; auto).
Qed.


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
Qed.


Global Instance stepProper : Proper (eq ==> ChorEnv.Equal ==> eq ==> eq ==> eq ==> ChorEnv.Equal ==> eq ==> iff) (Choreography.step).
Proof.
  intros ? C ? Theta1 Theta2 HTheta ? cfg ? ? l ? ? C' ? Theta1' Theta2' HTheta' ? cfg' ?; subst.
  split; intros Hstep; eapply stepProper'; eauto.
  all: (symmetry; auto).
Qed.


(** Typing Relation *)

Inductive WellTyped :
  ChorEnv.t Expr.typ -> ChorEnv.t Expr.typ -> ChorEnv.t nat -> Choreography.t -> Prop :=
  
| Nil : forall G D T, 
    ChorEnv.Empty D ->
    ChorEnv.Empty T ->
    WellTyped G D T Choreography.Empty
                                
| EPR : forall G D T A x B y C,
    A <> B ->
    WellTyped (ChorEnv.remove B y (ChorEnv.remove A x G))
      (ChorEnv.add B y Expr.QUBIT (ChorEnv.add A x Expr.QUBIT D)) T C ->

    ~ Var.Map.In x (ChorEnv.find A D) ->
    ~ Var.Map.In y (ChorEnv.find B D) ->

    WellTyped G D T (Choreography.Do (Insn.EPR A x B y) C)

| Send : forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A e tau B y C,
    A <> B ->
    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.BANG tau) ->
    WellTyped (ChorEnv.add B y tau G) (Actor.Map.add A DeltaA2 D) (Actor.Map.add A ThetaA2 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->

    WellTyped G D T (Choreography.Do (Insn.Send A e B y) C)

| LetBang : forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A x e tau C,

    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.BANG tau) ->
    WellTyped (ChorEnv.add A x tau G) (Actor.Map.add A DeltaA2 D) (Actor.Map.add A ThetaA2 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->

    WellTyped G D T (Choreography.Do (Insn.LetBang A x e) C)

| LetIn : forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A x e tau C,

    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e tau ->
    WellTyped (ChorEnv.remove A x G) (Actor.Map.add A (Var.Map.add x tau DeltaA2) D)
      (Actor.Map.add A ThetaA2 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x DeltaA2 ->
    WellTyped G D T (Choreography.Do (Insn.Let A x e) C)

| LetPair: forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A x1 x2 tau1 tau2 e C,

    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.Tensor tau1 tau2) ->
    WellTyped (ChorEnv.remove A x1 (ChorEnv.remove A x2 G))
      (Actor.Map.add A (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D)
      (Actor.Map.add A ThetaA2 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x1 DeltaA2 -> 
    ~ Var.Map.In x2 DeltaA2 ->
    x1 <> x2 ->

    WellTyped G D T (Choreography.Do (Insn.LetPair A x1 x2 e) C)

| If : forall DeltaA1 DeltaA2 DeltaA3 ThetaA1 ThetaA2 ThetaA3 DeltaA' ThetaA' G D T A e C1 C2 C,
  Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e Expr.BIT ->
  WellTyped G (Actor.Map.add A DeltaA2 D) (Actor.Map.add A ThetaA2 T) C1 ->
  WellTyped G (Actor.Map.add A DeltaA2 D) (Actor.Map.add A ThetaA2 T) C2 ->
  WellTyped G (Actor.Map.add A DeltaA3 D) (Actor.Map.add A ThetaA3 T) C ->

  (* D[A] == DeltaA1 ++ DeltaA2 ++ DeltaA3 *)
  Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA' ->
  Var.Map.Partition DeltaA' DeltaA2 DeltaA3 ->
  (* T[A] == ThetaA1 ++ ThetaA2 ++ ThetaA3 *)
  Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA' ->
  Var.Map.Partition ThetaA' ThetaA2 ThetaA3 ->


  WellTyped G D T (Choreography.If A e C1 C2 C)
.

Lemma WellTypedProper' : forall G D T C,
  WellTyped G D T C ->
  forall G' D' T',
  ChorEnv.Equal G G' ->
  ChorEnv.Equal D D' -> 
  ChorEnv.Equal T T' ->
  WellTyped G' D' T' C.
Proof.
  intros G D T C HWT.
  induction HWT; intros G' D' T' HG HD HT;
    try (constructor; auto; fail).
  * constructor.
    rewrite <- HD; auto.
    rewrite <- HT; auto.

  * constructor; auto.
    2:{ rewrite <- HD; auto. }
    2:{ rewrite <- HD; auto. }
    eapply  IHHWT; auto.
    { rewrite HG. reflexivity. }
    { rewrite HD. reflexivity. }

  * eapply (Send DeltaA1 DeltaA2 ThetaA1 ThetaA2); auto.
    + rewrite <- HG. eauto.
    + apply IHHWT.
      rewrite HG; reflexivity.
      rewrite HD; reflexivity.
      rewrite HT; reflexivity.
    + rewrite <- HD. auto.
    + rewrite <- HT. auto.

  * eapply (LetBang DeltaA1 DeltaA2 ThetaA1 ThetaA2);
      try apply IHHWT;
      try rewrite <- HG;
      try rewrite <- HD;
      try rewrite <- HT;
      eauto;
      reflexivity.

  * eapply (LetIn DeltaA1 DeltaA2 ThetaA1 ThetaA2);
      try apply IHHWT;
      try rewrite <- HG;
      try rewrite <- HD;
      try rewrite <- HT;
      eauto;
      reflexivity.

  * eapply (LetPair DeltaA1 DeltaA2 ThetaA1 ThetaA2);
      try apply IHHWT;
      try rewrite <- HG;
      try rewrite <- HD;
      try rewrite <- HT;
      eauto;
      reflexivity.

  * eapply (If DeltaA1 DeltaA2 DeltaA3 ThetaA1 ThetaA2 ThetaA3 DeltaA' ThetaA');
      try apply IHHWT1;
      try apply IHHWT2;
      try apply IHHWT3;
      try rewrite <- HG;
      try rewrite <- HD;
      try rewrite <- HT;
      eauto;
      reflexivity.

Qed.

Global Instance WellTypedProper :
  Proper (ChorEnv.Equal ==> ChorEnv.Equal ==> ChorEnv.Equal ==> eq ==> iff) WellTyped.
Proof.
  intros G1 G2 HG D1 D2 HD T1 T2 HT ? e ?; subst.
  split; intros; eapply WellTypedProper'; eauto;
    symmetry; auto.
Qed.


(*HERE**)




(** ** Type safety *)

Inductive multi_step : Choreography.t -> ChorEnv.t nat -> Config.t -> Choreography.t -> ChorEnv.t nat -> Config.t -> Prop :=
| Step0 : forall e Theta cfg, multi_step e Theta cfg e Theta cfg
| Step1 : forall e1 e2 e3 Theta1 Theta2 Theta3 cfg1 cfg2 cfg3 l,
  step e1 Theta1 cfg1 l e2 Theta2 cfg2 ->
  multi_step e2 Theta2 cfg2 e3 Theta3 cfg3 ->
  multi_step e1 Theta1 cfg1 e3 Theta3 cfg3.


