From Qoreo Require Import Base.
From Qoreo Require Expr.

From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms (* for Proper *).
From Stdlib Require Import Lia.


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
End Insn.

Module Choreography.
    Definition t := list Insn.t.

    Definition actors (C : t) : Actor.FSet.t :=
        List.fold_left (fun X I => Actor.FSet.union X (Insn.actors I)) C Actor.FSet.empty.

    Fixpoint subst (A : Actor.t) (x : Var.t) (v : Expr.t) (C : t) : t :=
      match C with
      | [] => []
      | (Ins :: C') => (Insn.subst A x v Ins)::(if (Insn.rebound_in A x Ins)
                                                then C' else (subst A x v C')) 
      end.
End Choreography.

Module Label.
    Inductive t :=
    | Send : Actor.t -> Expr.t -> Actor.t -> t
    | EPR  : Actor.t -> Actor.t -> t
    | Loc  : Actor.t -> t
    .


    Definition actors (l : t) : Actor.FSet.t :=
        match l with
        | Send A _ B | EPR A B => Actor.FSet.add A (Actor.FSet.singleton B)
        | Loc A => Actor.FSet.singleton A
        end.
End Label.

(** Semantics **)

(** NOTE: I had to change the EPR rule to ensure that the label is unordered *)
(** NOTE: I also changed the beta rules so there is a refs' equal to refs, not syntactically equal *)
Inductive step : Choreography.t -> ChorEnv.t nat -> Config.t ->
                 Label.t ->
                 Choreography.t -> ChorEnv.t nat -> Config.t -> Prop :=

| SendC : forall TA' A e B x C T cfg e' T' cfg',
    Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->

    ChorEnv.Equal T' (Actor.Map.add A TA' T) ->

    step  (Insn.Send A e B x :: C) T cfg
          (Label.Loc A)
          (Insn.Send A e' B x :: C) T' cfg'

| SendB : forall A v B x C refs refs' cfg C',
    C' = Choreography.subst B x v C ->
    ChorEnv.Equal refs refs' ->

    step  (Insn.Send A (Expr.Bang v) B x :: C) refs cfg
          (Label.Send A v B)
          C' refs' cfg

| EPRB : forall q1 q2 T0 A x B y C T cfg C' T' cfg',
    ChorEnv.epr A B T cfg = (q1, q2, T0, cfg') ->
    ChorEnv.Equal T' T0 ->

    C' = Choreography.subst A x (Expr.QRef q1) (Choreography.subst B y (Expr.QRef q2) C) ->

    step  (Insn.EPR A x B y :: C) T cfg
          (Label.EPR A B) 
          C' T' cfg'

| EPRB' : forall q1 q2 T0 A x B y C T cfg C' T' cfg',
    ChorEnv.epr B A T cfg = (q2, q1, T0, cfg') ->
    ChorEnv.Equal T' T0 ->

    C' = Choreography.subst A x (Expr.QRef q1) (Choreography.subst B y (Expr.QRef q2) C) ->

    step  (Insn.EPR A x B y :: C) T cfg
          (Label.EPR B A) 
          C' T' cfg'

| LetC : forall TA' A x e C T cfg e' T' cfg',
    Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->
    
    ChorEnv.Equal T' (Actor.Map.add A TA' T) ->

    step  (Insn.Let A x e :: C) T cfg
          (Label.Loc A)
          (Insn.Let A x e' :: C) T' cfg'

| LetB : forall A x v C refs refs' cfg C',
    Expr.Val v ->
    C' = Choreography.subst A x v C ->
    ChorEnv.Equal refs refs' ->
    step  (Insn.Let A x v :: C) refs cfg
          (Label.Loc A)
          C' refs' cfg

| LetBangC : forall TA' A x e C T cfg e' T' cfg',
    Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->

    ChorEnv.Equal T' (Actor.Map.add A TA' T) ->
    step  (Insn.LetBang A x e :: C) T cfg
          (Label.Loc A)
          (Insn.LetBang A x e' :: C) T' cfg'

| LetBangB : forall A x e0 C refs refs' cfg C',
    C' = Choreography.subst A x e0 C ->
    ChorEnv.Equal refs' refs ->
    step  (Insn.LetBang A x (Expr.Bang e0) :: C) refs cfg
          (Label.Loc A)
          C' refs' cfg

| LetPairC : forall TA' A x1 x2 e C T cfg e' T' cfg',
    Expr.step e (ChorEnv.find A T) cfg e' TA' cfg' ->

    ChorEnv.Equal T' (Actor.Map.add A TA' T) ->

    step  (Insn.LetPair A x1 x2 e :: C) T cfg
          (Label.Loc A)
          (Insn.LetPair A x1 x2 e' :: C) T' cfg'

| LetPairB : forall A x1 x2 v1 v2 C refs refs' cfg C',
    Expr.Val v1 -> Expr.Val v2 ->
    C' = Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C) ->
    ChorEnv.Equal refs' refs ->
    step  (Insn.LetPair A x1 x2 (Expr.Pair v1 v2) :: C) refs cfg
          (Label.Loc A) 
          C' refs' cfg

(* delay *)
| Delay : forall I C T cfg C' T' cfg' l,
    step C T cfg l C' T' cfg' ->
    Actor.FSet.Empty (Actor.FSet.inter (Label.actors l) (Insn.actors I)) ->
    step (I::C) T cfg l (I::C') T' cfg'
.

Lemma stepProper' : forall C Θ1 cfg l C' Θ1' cfg',
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

    apply (ChorEnv.chor_epr_eq Θ2) in H; auto.
    destruct H as [T0' [Heq'' H]].

    apply (Choreography.EPRB q1 q2 T0'); auto.
    { rewrite H0. rewrite Heq''. reflexivity. }

  * apply (ChorEnv.chor_epr_eq Θ2) in H; auto.
    destruct H as [T0' [Heq'' H]].

    apply (Choreography.EPRB' q1 q2 T0'); auto.
    {
      rewrite H0. rewrite Heq''. reflexivity.
    }
Qed.


Global Instance stepProper : Proper (eq ==> ChorEnv.Equal ==> eq ==> eq ==> eq ==> ChorEnv.Equal ==> eq ==> iff) (Choreography.step).
Proof.
  intros ? C ? Θ1 Θ2 HΘ ? cfg ? ? l ? ? C' ? Θ1' Θ2' HΘ' ? cfg' ?; subst.
  split; intros Hstep.
  * eapply stepProper'; eauto.
  * eapply stepProper'; eauto. symmetry; auto. symmetry; auto.
Qed.

Inductive WellTyped :
  ChorEnv.t Expr.typ -> ChorEnv.t Expr.typ -> ChorEnv.t nat -> Choreography.t -> Prop :=
  
| Nil : forall G D T, 
    ChorEnv.Empty D ->
    ChorEnv.Empty T ->
    WellTyped G D T nil
                                
| EPR : forall G D T A x B y C,
    A <> B ->
    WellTyped (ChorEnv.remove B y (ChorEnv.remove A x G))
      (ChorEnv.add B y Expr.QUBIT (ChorEnv.add A x Expr.QUBIT D)) T C ->

    ~ Var.Map.In x (ChorEnv.find A D) ->
    ~ Var.Map.In y (ChorEnv.find B D) ->

    WellTyped G D T ((Insn.EPR A x B y)::C)

| Send : forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A e tau B y C,
    A <> B ->
    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.BANG tau) ->
    WellTyped (ChorEnv.add B y tau G) (Actor.Map.add A DeltaA2 D) (Actor.Map.add A ThetaA2 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->

    WellTyped G D T ((Insn.Send A e B y)::C)

| LetBang : forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A x e tau C,

    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.BANG tau) ->
    WellTyped (ChorEnv.add A x tau G) (Actor.Map.add A DeltaA2 D) (Actor.Map.add A ThetaA2 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->

    WellTyped G D T ((Insn.LetBang A x e)::C)

| LetIn : forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A x e tau C,

    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e tau ->
    WellTyped (ChorEnv.remove A x G) (Actor.Map.add A (Var.Map.add x tau DeltaA2) D)
      (Actor.Map.add A ThetaA2 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x DeltaA2 ->
    WellTyped G D T ((Insn.Let A x e)::C)

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

    WellTyped G D T ((Insn.LetPair A x1 x2 e)::C)
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

Qed.

Global Instance WellTypedProper :
  Proper (ChorEnv.Equal ==> ChorEnv.Equal ==> ChorEnv.Equal ==> eq ==> iff) WellTyped.
Proof.
  intros G1 G2 HG D1 D2 HD T1 T2 HT ? e ?; subst.
  split; intros; eapply WellTypedProper'; eauto;
    symmetry; auto.
Qed.

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
    A <> B -> ~ ((Insn.bind_eqb (A,x) (B,y)) = true).
Proof.
  intros.
  pose proof (Insn.bind_eqb_false (A,x) (B,y)).
  destruct H0.
  pose proof (not_true_iff_false (Insn.bind_eqb (A, x) (B, y))).
  destruct H2.
  apply H3.
  apply H1.
  pose proof (Insn.nbeq (A,x) (B,y)).
  destruct H4.
  apply H4.
  simpl.
  auto.
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

(* A slew of Lemmas for manipulating environment mappings. *)

(* START *)

Lemma extension : forall A G x (tau : Expr.typ),
    ChorEnv.MapsTo A x tau G <-> Var.Map.MapsTo x tau (ChorEnv.find A G).
Proof.
  intros A G x tau.
  split.
  auto.
  auto.
Qed.

Lemma empty_dj : forall {X : Type} (CE1 : ChorEnv.t X) CE2 A,
    ChorEnv.Empty CE2 ->
    Var.Map.Properties.Disjoint (ChorEnv.find A CE1) (ChorEnv.find A CE2).
Proof.
  intros X CE1 CE2 A Hempty.
  intros z [Hin1 Hin2].
  unfold ChorEnv.Empty in Hempty.
  rewrite Hempty in Hin2.
  Var.simplify.
Qed.
    
Lemma nin_dj : forall  {X : Type} x (M1 : Var.Map.t X) M2,
    Var.Map.Properties.Disjoint M1 M2 ->
    Var.Map.In x M2 ->
    ~ Var.Map.In x M1.
Proof.
  intros X x M1 M2 Hdisj Hin1 Hin2.
  apply (Hdisj x); auto.
Qed.

Lemma remove_nin_dj : forall  {X : Type} x (M1 : Var.Map.t X) M2,
    Var.Map.Properties.Disjoint M1 (Var.Map.remove x M2) ->
    ~ Var.Map.In x M1 ->
    Var.Map.Properties.Disjoint M1 M2.
Proof.
  intros X x M1 M2 Hdisj Hin.
  intros z [Hin1 Hin2].
  Var.Map.Tactics.compare x z.
  {
    apply (Hdisj z).
    split; auto.
    Var.simplify.
  }
Qed.

Lemma partition_dj : forall  {X : Type} (M : Var.Map.t X) M1 M2 M3,
    Var.Map.Properties.Disjoint M M1 ->
    Var.Map.Partition M1 M2 M3  ->
    Var.Map.Properties.Disjoint M M2.
Proof.
  intros X M M1 M2 M3 Hdisj Hpart.
  Var.Map.Tactics.reflect_partition.
  Var.simplify.
Qed.

Lemma partition_concat_dj : forall  {X : Type} (M : Var.Map.t X) M1 M2 M3,
    Var.Map.Partition M1 M2 M3  ->
    Var.Map.Properties.Disjoint M M2 ->
    Var.Map.Properties.Disjoint M M3 ->
    Var.Map.Properties.Disjoint M M1.
Proof.
  intros.
  Var.Map.Tactics.reflect_partition.
  Var.simplify.
Qed.

(* follows by partition_dj in case A = B, immediate otherwise *)
Lemma partition_dj_env : forall  {X : Type} A B (CE1 : ChorEnv.t X) CE2 M1 M2,
    Var.Map.Properties.Disjoint (ChorEnv.find A CE1) (ChorEnv.find A CE2) ->
    Var.Map.Partition (ChorEnv.find B CE2) M1 M2 ->
    Var.Map.Properties.Disjoint (ChorEnv.find A CE1)
      (ChorEnv.find A (Actor.Map.add B M2 CE2)).
Proof.
  intros X A B CE1 CE2 M1 M2 Hdisj Hpart.
  Var.Map.Tactics.reflect_partition.
  Var.simplify.
  Actor.Map.Tactics.compare A B; auto.
  rewrite Heq in Hdisj.
  Var.simplify.
Qed.

Lemma remove_dj : forall  (M1 : Var.Map.t Expr.typ) M2 x tau,
    Var.Map.Properties.Disjoint (Var.Map.add x tau M1) M2 -> 
    Var.Map.Properties.Disjoint M1 M2.
Proof.
  intros M1 M2 x tau Hdisj.
  Var.simplify.
Qed.

Lemma remove_dj_env : forall (CE1 CE2 : ChorEnv.t Expr.typ) A B x,
    Var.Map.Properties.Disjoint (ChorEnv.find A CE1) (ChorEnv.find A CE2) -> 
    Var.Map.Properties.Disjoint
      (ChorEnv.find A (ChorEnv.remove B x CE1))
      (ChorEnv.find A CE2).
Proof.
  intros.
  intros D. intros [Hin1 Hin2].
  
  (* Because D in find A (remove B x CE1), we know A <> B *)
  assert (A <> B).
  {
    intros ?; subst.
    unfold ChorEnv.remove, ChorEnv.find in Hin1.
    Actor.simplify.
    destruct (Actor.Map.find B CE1) as [CB1 | ] eqn:HB1.
    2:{ Var.simplify. }
    Var.simplify.
    apply (H D). split; auto.
    unfold ChorEnv.find. rewrite HB1. auto.
  }
  Var.simplify.
  destruct (Actor.eq_dec A B) as [Heq | ].
  { unfold Actor.eq in Heq. subst; contradiction. }
  apply (H D); auto.
Qed.

Lemma remove_add_dj_env : forall (CE1 CE2 : ChorEnv.t Expr.typ) A B x tau,
    Var.Map.Properties.Disjoint (ChorEnv.find A CE1) (ChorEnv.find A CE2) ->
    Var.Map.Properties.Disjoint
      (ChorEnv.find A (ChorEnv.remove B x CE1))
      (ChorEnv.find A (ChorEnv.add B x tau CE2)).
Proof.
  intros.
  Var.simplify.
  Actor.Map.Tactics.compare A B; auto.
  {
    intros z [Hin1 Hin2].
    Var.simplify.
    destruct Hin2 as [? | Hin2]; [contradiction | ].
    apply (H z); auto.
  }
Qed.

Lemma add_empty_delta : forall A x tau (D : ChorEnv.t Expr.typ),
    ~ ChorEnv.Empty (ChorEnv.add A x tau D).
Proof.
  intros. intros Hempty.
  unfold ChorEnv.add in Hempty.
  unfold ChorEnv.Empty in Hempty.
  specialize (Hempty A).
  ChorEnv.simplify.
  specialize (Hempty x).
  Var.simplify.
Qed.

Lemma empty_is_empty : forall {X : Type} A,
    Var.Map.Empty (ChorEnv.find A (Actor.Map.empty (Var.Map.t X))).
Proof.
  intros.
  unfold ChorEnv.find.
  Actor.simplify.
  Var.simplify.
Qed.

Lemma empty_eq_env  : forall  {X : Type} (CE : ChorEnv.t X),
    Actor.Map.Empty CE ->
    ChorEnv.Equal CE (Actor.Map.empty (Var.Map.t X)).
Proof.
  intros.
  unfold ChorEnv.Equal.
  intros.
  unfold ChorEnv.find.
  Actor.simplify.
  rewrite H.
  Actor.simplify.
Qed.
  
Lemma empty_map_empty : forall {X : Type}, Var.Map.Empty (Var.Map.empty X).
Proof.
  intros.
  Var.simplify.
Qed.


Lemma find_add_env : forall {X : Type} A (CE : ChorEnv.t X),
    ChorEnv.Equal (Actor.Map.add A (ChorEnv.find A CE) CE) CE.
Proof.
  intros X A CE B.
  ChorEnv.simplify.
Qed.
#[global] Hint Rewrite @find_add_env : var_db.

Lemma empty_to_empty : forall  {X : Type} A (CE : ChorEnv.t X) (M : Var.Map.t X),
    Var.Map.Empty M ->
    Var.Map.Empty (ChorEnv.find A CE) -> 
    ChorEnv.Equal (Actor.Map.add A M CE) CE.
Proof.
  intros.
  ChorEnv.simplify.
  rewrite <- H0.
  ChorEnv.simplify.
Qed.

Lemma empty_to_empty_old : forall  {X : Type} A (M : Var.Map.t X),
    Var.Map.Empty M ->
    ChorEnv.Equal
      (Actor.Map.add A M (Actor.Map.empty (Var.Map.t X)))
      (Actor.Map.empty (Var.Map.t X)).
Proof.
  intros. 
  pose proof (H0 := Var.Map.Proofs.empty_map_equal M H).
  rewrite H0.
  intros D. ChorEnv.simplify.
Qed.

Lemma find_empty : forall {X : Type} A,
    (ChorEnv.find A (Actor.Map.empty (Var.Map.t X))) =  (Var.Map.empty X).
Proof.
  intros.
  unfold ChorEnv.find.
  Actor.simplify.
Qed.

Lemma empty_partition : forall (M M1 M2 : Var.Map.t Expr.typ),
    Var.Map.Empty M ->
    Var.Map.Partition M M1 M2 ->
    Var.Map.Empty M1.
Proof.
  intros; Var.simplify.
Qed.

Lemma lopsided_partition : forall {X : Type} (M M1 : Var.Map.t X),
    Var.Map.Partition M (Var.Map.empty X) M1 ->
    Var.Map.Equal M M1.
Proof.
  intros; Var.simplify.
Qed.

Lemma partition_lopsided : forall {X : Type} (M1 M2: Var.Map.t X),
    Var.Map.Partition M1 M1 M2 ->
    Var.Map.Equal M2 (Var.Map.empty X).
Proof.
  intros.
  rewrite Var.Map.Proofs.partition_concat in H.
  destruct H as [Hdisj Heq].
  intros z. specialize (Heq z).
  Var.simplify.
  destruct (Var.Map.find z M1) eqn:H1; auto.
  destruct (Var.Map.find z M2) eqn:H2; auto.
  exfalso. apply (Hdisj z).
  split; Var.solve.
Qed.

Lemma find_add : forall {X : Type} A M (CE : ChorEnv.t X),
    ChorEnv.find A (Actor.Map.add A M CE) = M.
Proof.
  intros.
  unfold ChorEnv.find.
  Actor.simplify.
Qed.

Lemma find_add_map : forall A x tau (CE : ChorEnv.t Expr.typ),
    Var.Map.Equal
      (ChorEnv.find A (ChorEnv.add A x tau CE))
      (Var.Map.add x tau (ChorEnv.find A CE)).
Proof.
  intros.
  unfold ChorEnv.find.
  unfold ChorEnv.add.
  Actor.simplify.
Qed.      


Lemma find_ab_neq1 : forall {X : Type} A B x tau (CE : ChorEnv.t X),
    A <> B ->
    (ChorEnv.find A (ChorEnv.add B x tau CE)) = (ChorEnv.find A CE).
Proof.
  intros X A B x tau CE Hneq.
  unfold ChorEnv.find. unfold ChorEnv.add.
  Actor.simplify.
Qed.

Lemma find_ab_neq2 : forall {X : Type} A B M (CE : ChorEnv.t X),
    A <> B ->
    (ChorEnv.find A (Actor.Map.add B M CE)) = (ChorEnv.find A CE).
Proof.
  intros.
  unfold ChorEnv.find.
  Actor.simplify.
Qed.

Lemma find_ab_neq3 : forall {X : Type} A B x (CE : ChorEnv.t X),
    A <> B ->
    (ChorEnv.find A (ChorEnv.remove B x CE)) = (ChorEnv.find A CE).
Proof.
  intros X A B x CE Hneq.
  unfold ChorEnv.find. unfold ChorEnv.remove.
  Actor.simplify.
Qed.

Lemma find_nbeq : forall (CE : ChorEnv.t Expr.typ) A x B y tau,
    Insn.bind_eqb (A, x) (B, y) = false -> 
    ~ Var.Map.In x (ChorEnv.find A CE) ->
    ~ Var.Map.In x (ChorEnv.find A (ChorEnv.add B y tau CE)).
Proof.
  intros CE A x B y tau Heq Hin.
  Var.simplify.
  unfold Insn.bind_eqb, Insn.bind_eq_dec in Heq; simpl in Heq.
  Actor.Map.Tactics.compare A B.
  * (* A = B*)
    Var.Map.Tactics.compare x y; try discriminate.
    (* x <> y *)
    Var.simplify.
  * (* A <> B *) auto.
Qed.

Lemma add_find : forall (CE : ChorEnv.t Expr.typ) A x tau,
    (ChorEnv.find A (ChorEnv.add A x tau CE)) = (Var.Map.add x tau (ChorEnv.find A CE)).
Proof.
  intros.
  unfold ChorEnv.find, ChorEnv.add.
  Actor.simplify.
Qed.

Lemma remove_find : forall (CE : ChorEnv.t Expr.typ) A x,
    (ChorEnv.find A (ChorEnv.remove A x CE)) = (Var.Map.remove x (ChorEnv.find A CE)).
Proof.
  intros.
  Var.simplify.
  Actor.simplify.
Qed.

Lemma add_remove : forall (CE : ChorEnv.t Expr.typ) M A x tau,
    Var.Map.MapsTo x tau M ->
    ChorEnv.Equal
      (ChorEnv.add A x tau (Actor.Map.add A (Var.Map.remove x M) CE))
      (Actor.Map.add A M CE).
Proof.
  intros.
  unfold ChorEnv.add.
  Var.simplify. Actor.simplify.
  Var.simplify.
  rewrite Var.Map.Proofs.add_mapsto; auto.
  apply ChorEnv.actor_map_Equal.
  Actor.simplify.
Qed.

Lemma nin_remove : forall (M : Var.Map.t Expr.typ) x,
    ~ (Var.Map.In x (Var.Map.remove x M)).
Proof.
  intros.
  Var.simplify.
Qed.

(* This is needed for dealing with classical variable shadowing *)
Lemma nin_remove_ce : forall (CE : ChorEnv.t Expr.typ) A x B y,
    ~ (Var.Map.In x (ChorEnv.find A CE)) ->
    ~ (Var.Map.In x (ChorEnv.find A (ChorEnv.remove B y CE))).
Proof.
  intros.
  Var.simplify. Actor.simplify.
  Var.simplify.
Qed.

Lemma nin_partition : forall x (M M1 M2 : Var.Map.t Expr.typ),
    ~ Var.Map.In x M ->
    Var.Map.Partition M M1 M2 ->
    ~ Var.Map.In x M1.
Proof.
  intros.
  pose proof (Var.Map.Proofs.partition_not_in_inversion Expr.typ M M1 M2 x H0) as Hpni.
  destruct Hpni as [Hpni _].
  destruct (Hpni H).
  auto.
Qed.

Lemma partition_remove_all : forall (CE1 : ChorEnv.t Expr.typ) CE2 CE3 A B x,
    Var.Map.Partition (ChorEnv.find A CE1) (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
    Var.Map.Partition (ChorEnv.find A (ChorEnv.remove B x CE1))
      (ChorEnv.find A (ChorEnv.remove B x CE2))
      (ChorEnv.find A (ChorEnv.remove B x CE3)).
Proof.
  intros.
  Var.simplify.
  Actor.simplify.
  Var.simplify.
Qed.
  
Lemma partition_remove : forall (Delta : Var.Map.t Expr.typ) Delta1 Delta2 x tau,
    Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
    ~ Var.Map.In x Delta ->
    ~ Var.Map.In x Delta1 ->
    Var.Map.Partition Delta Delta1 (Var.Map.remove x Delta2).
Proof.
  intros Delta Delta1 Delta2 x tau Hpart H H1.
  apply Var.Map.Proofs.partition_add_inversion in Hpart; auto.
  destruct Hpart as [[Hmapsto [Hin2 Hpart]] | [Hin1 [Hmapsto2 Hpart]]].
  * contradict H1. exists tau; auto.
  * auto.
Qed.  

Lemma remove_add : forall x tau (Delta1 : Var.Map.t Expr.typ) Delta2,
    ~ Var.Map.In x Delta1 ->
    Var.Map.Equal Delta2 (Var.Map.add x tau Delta1) ->
    Var.Map.Equal (Var.Map.remove x Delta2) Delta1.
Proof.
  intros.
  Var.simplify.
  apply Var.Map.Proofs.remove_not_in; auto.
Qed.

Lemma addadd1 : forall A (D : ChorEnv.t Expr.typ) Delta x tau,
    ChorEnv.Equal (Actor.Map.add A Delta (ChorEnv.add A x tau D)) (Actor.Map.add A Delta D).
Proof.
  intros.
  unfold ChorEnv.add.
  Actor.simplify. 
Qed.

Lemma addadd2 : forall {X : Type} A (T : ChorEnv.t X) Theta1 Theta2,
    ChorEnv.Equal (Actor.Map.add A Theta1 (Actor.Map.add A Theta2 T)) 
                  (Actor.Map.add A Theta1 T).
Proof.
  intros.
  Actor.simplify.
Qed.

Lemma addadd3 :  forall (CE : ChorEnv.t Expr.typ) A x tau B M,
  A <> B -> 
  ChorEnv.Equal (Actor.Map.add B M (ChorEnv.add A x tau CE))
                (ChorEnv.add A x tau (Actor.Map.add B M CE)).
Proof.
  intros.
  unfold ChorEnv.add.
  Var.simplify. Actor.simplify.
  rewrite Actor.Map.Proofs.add_neq_sym; auto.
  reflexivity.
Qed.

Lemma addadd4 :  forall {X : Type} (CE : ChorEnv.t X) A MA B MB,
  A <> B -> 
  ChorEnv.Equal (Actor.Map.add B MB (Actor.Map.add A MA CE))
                (Actor.Map.add A MA (Actor.Map.add B MB CE)).
Proof.
  intros.
  rewrite Actor.Map.Proofs.add_neq_sym; auto.
  reflexivity.
Qed.

Lemma addadd5 : forall (CE : ChorEnv.t Expr.typ) A x taux B y tauy,
    Insn.bind_eqb (B, y) (A, x) = false ->
    ChorEnv.Equal (ChorEnv.add A x taux (ChorEnv.add B y tauy CE))
                  (ChorEnv.add B y tauy (ChorEnv.add A x taux CE)).
Proof.
  intros.
  unfold Insn.bind_eqb, Insn.bind_eq_dec in H; simpl in H.
  Actor.simplify.
  2:{ unfold ChorEnv.add.
      rewrite Actor.Map.Proofs.add_neq_sym; auto.
      Var.simplify.
      Actor.simplify.
  }
  Var.simplify.
  unfold ChorEnv.add.
  repeat (Actor.simplify; Var.simplify).
  rewrite Var.Map.Proofs.add_neq_sym; auto.
  reflexivity.
Qed.

(* this lemma may help prove the preceding lemma. *)
Lemma addadd6 : forall {X : Type} x taux y tauy (M : Var.Map.t X),
    x <> y -> 
    Var.Map.Equal (Var.Map.add y tauy (Var.Map.add x taux M))
                  (Var.Map.add x taux (Var.Map.add y tauy M)).
Proof.
  intros.
  rewrite Var.Map.Proofs.add_neq_sym; auto.
  reflexivity.
Qed.

Lemma addadd8 : forall (CE : ChorEnv.t Expr.typ) A x tau M, 
    ChorEnv.Equal
      (Actor.Map.add A (Var.Map.add x tau M) CE)
      (ChorEnv.add A x tau (Actor.Map.add A M CE)).
Proof.
  intros.
  unfold ChorEnv.add.
  repeat (Var.simplify; Actor.simplify).
Qed.

Lemma addadd9 : forall (CE : ChorEnv.t Expr.typ) A x taux y tauy,
    y <> x ->
    ChorEnv.Equal (ChorEnv.add A x taux (ChorEnv.add A y tauy CE))
                  (ChorEnv.add A y tauy (ChorEnv.add A x taux CE)).
Proof.
  intros.
  assert (Insn.bind_eqb (A, y) (A, x) = false).
  destruct (Insn.bind_eqb_false (A, y) (A, x)).
  assert (~ Insn.bind_eq (A, y) (A, x)).
  unfold Insn.bind_eq.
  tauto.
  tauto.
  apply addadd5; auto.
Qed.

Lemma overwrite : forall (CE : ChorEnv.t Expr.typ) A x tau1 tau2,
    ChorEnv.Equal
      (ChorEnv.add A x tau1 (ChorEnv.add A x tau2 CE))
      (ChorEnv.add A x tau1 CE).
Proof.
  intros.
  unfold ChorEnv.add.
  repeat (Actor.simplify; Var.simplify).
Qed.

Lemma remrem :  forall (CE : ChorEnv.t Expr.typ) A x y,
    ChorEnv.Equal
      (ChorEnv.remove A x (ChorEnv.remove A y CE))
      (ChorEnv.remove A y (ChorEnv.remove A x CE)).      
Proof.
  intros.
  unfold ChorEnv.remove.
  repeat (Var.simplify; Actor.simplify).
  intros D. ChorEnv.simplify.
  rewrite Var.Map.Proofs.remove_swap.
  reflexivity.
Qed.

Lemma rmadd1 : forall (CE : ChorEnv.t Expr.typ) A x tau,
    ChorEnv.Equal
      (ChorEnv.remove A x (ChorEnv.add A x tau CE))
      (ChorEnv.remove A x CE).
Proof.
  intros.
  unfold ChorEnv.remove, ChorEnv.add.
  repeat (Actor.simplify; Var.simplify).
Qed.

Lemma rmadd2 : forall (CE : ChorEnv.t Expr.typ) A B x y tau,
    Insn.bind_eqb (A, x) (B, y) = false ->
    ChorEnv.Equal
      (ChorEnv.remove B y (ChorEnv.add A x tau CE))
      (ChorEnv.add A x tau (ChorEnv.remove B y CE)).
Proof.
  intros CE A B x y tau Heq.
  rewrite Insn.bind_eqb_false in Heq.
  unfold Insn.bind_eq in Heq; simpl in Heq.
  
  unfold ChorEnv.remove, ChorEnv.add.
  repeat (Actor.simplify; Var.simplify).

  rewrite Actor.Map.Proofs.add_neq_sym; auto.
  reflexivity.
Qed.

Lemma nin_mapl : forall (M : Var.Map.t Expr.typ)  x y tau,
    x <> y ->
    ~ Var.Map.In x M ->
    ~ Var.Map.In x (Var.Map.add y tau M).
Proof.
  intros.
  Var.solve.
Qed.

Lemma nin_mapr : forall (M : Var.Map.t Expr.typ)  x y tau,
    x <> y ->
    ~ Var.Map.In x (Var.Map.add y tau M) ->
    ~ Var.Map.In x M.
Proof.
  intros.
  Var.solve.
Qed.

Lemma nin_nxeq : forall (M : Var.Map.t Expr.typ)  x y tau,
    ~ Var.Map.In x (Var.Map.add y tau M) -> x <> y.
Proof.
  intros.
  Var.solve.
Qed.

(* contrapositive of nin_mapl with mapsto rewrite *)
Lemma map_in : forall (M : Var.Map.t Expr.typ)  x tau,
    Var.Map.MapsTo x tau M ->
    Var.Map.In x M.
Proof.
  intros.
  Var.solve.
Qed.
      

Lemma nin_nbeq : forall (CE : ChorEnv.t Expr.typ) A x tau B y,
    ~ Var.Map.In y (ChorEnv.find B (ChorEnv.add A x tau CE)) ->
    Insn.bind_eqb (A, x) (B, y) = false.
Proof.
  intros.
  apply Insn.bind_eqb_false.
  intros [? ?]; simpl in *; subst.
  repeat (Var.simplify; Actor.simplify).
Qed.
      

Lemma  contra_nin_nbeq : forall (CE : ChorEnv.t Expr.typ) A x tau B y,
    Insn.bind_eqb (A, x) (B, y) = true ->
    Var.Map.In y (ChorEnv.find B (ChorEnv.add A x tau CE)).
Proof.
  intros CE A x tau B y H.
  apply Insn.bind_eqb_true in H.
  unfold Insn.bind_eq in H; simpl in H.
  destruct H; subst.
  repeat (Var.simplify; Actor.simplify).
Qed.

Lemma in_add : forall (M : Var.Map.t Expr.typ)  x tau,
    Var.Map.In x (Var.Map.add x tau M).
Proof.
  intros.
  Var.simplify.
Qed.
    
Lemma in_beq : forall (CE : ChorEnv.t Expr.typ) A x tau,
    Var.Map.In x (ChorEnv.find A (ChorEnv.add A x tau CE)).
Proof.
  intros.
  pose proof (contra_nin_nbeq CE A x tau A x).
  destruct (Insn.bind_eqb_true (A, x) (A, x)).
  destruct (Insn.beq (A,x) (A,x)).
  assert (Insn.bind_eqb (A, x) (A, x) = true).
  apply H1.
  apply H3.
  simpl.
  auto.
  apply (H H4). 
Qed.

Lemma nin_nbeq_add1 : forall (CE : ChorEnv.t Expr.typ) A x B y tau,
    Insn.bind_eqb (A, x) (B, y) = false ->
    ~ Var.Map.In x (ChorEnv.find A CE) ->
      ~ Var.Map.In x (ChorEnv.find A (ChorEnv.add B y tau CE)).
Proof.
  intros CE A x B y tau Heq Hin.
  apply Insn.bind_eqb_false in Heq.
  unfold Insn.bind_eq in Heq; simpl in Heq.
  repeat (Var.simplify; Actor.simplify).
Qed.

Lemma nin_nbeq_add2 : forall (CE : ChorEnv.t Expr.typ) A x B y tau,
    Insn.bind_eqb (A, x) (B, y) = false ->
    ~ Var.Map.In x (ChorEnv.find A (ChorEnv.add B y tau CE))->
    ~ Var.Map.In x (ChorEnv.find A CE).
Proof.
  intros CE A x B y tau Heq Hin.
  apply Insn.bind_eqb_false in Heq.
  unfold Insn.bind_eq in Heq; simpl in Heq.
  repeat (Var.simplify; Actor.simplify).
Qed.

Lemma nin_nbeq_add3 : forall (CE : ChorEnv.t Expr.typ) A x taux B y tauy,
    Insn.bind_eqb (A, x) (B, y) = false ->
    ChorEnv.MapsTo A x taux CE ->
    ChorEnv.MapsTo A x taux (ChorEnv.add B y tauy CE).
Proof.
  intros CE A x taux B y tauy Heq Hin.
  apply Insn.bind_eqb_false in Heq.
  unfold Insn.bind_eq in Heq; simpl in Heq.
  unfold ChorEnv.MapsTo in *.
  repeat (Var.simplify; Actor.simplify).
  right. split; auto.
Qed.

Lemma ini : forall (Delta : Var.Map.t Expr.typ) Delta1 Delta2 x tau,
    Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
    ~ (Var.Map.In x Delta1) ->
    (Var.Map.MapsTo x tau Delta2).
Proof.
  intros Delta Delta1 Delta2 x tau Hpart Hin.
  Var.reflect_find.
  Var.Map.Tactics.reflect_partition.
  specialize (Heq x). Var.simplify.
  rewrite Hin in Heq.
  Var.solve.
Qed.

Lemma inin : forall (Delta : Var.Map.t Expr.typ) Delta1 Delta2 x tau,
    Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
    (Var.Map.In x Delta1) ->
    (Var.Map.MapsTo x tau Delta1).
Proof.
  intros ? ? ? ? ? Hpart Hin.
  Var.reflect_find.
  Var.Map.Tactics.reflect_partition.
  specialize (Heq x). Var.simplify.
  rewrite Hin in Heq. auto.
Qed.

Lemma nin : forall (Delta : Var.Map.t Expr.typ) Delta1' Delta1 Delta2 x tau,
    Var.Map.Equal (Var.Map.add x tau Delta1') Delta1 ->
    Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
    ~ (Var.Map.In x Delta) ->
    ~ (Var.Map.In x Delta1') ->
    ~ (Var.Map.In x Delta2) /\ Var.Map.Partition Delta Delta1' Delta2.
Proof.
  intros ? ? ? ? ? ? Heq Hpart Hnin Hnin1. Var.simplify.
  apply Var.Map.Proofs.partition_add_inversion in Hpart; auto.
  destruct Hpart as [[? [? ?]] | [Hcontra _]].
  2:{
    contradict Hcontra.
    Var.simplify.
  }
  split; auto.
  Var.simplify.
  rewrite Var.Map.Proofs.remove_not_in in H1; auto.
Qed.

Lemma mapsto_destruct : forall {X : Type} x tau (M : Var.Map.t X) ,
    Var.Map.MapsTo x tau M ->
    (exists M', Var.Map.Equal M (Var.Map.add x tau M') /\ ~ Var.Map.In x M').
Proof.
  intros.
  exists (Var.Map.remove x M).
  split.
  * Var.simplify. rewrite Var.Map.Proofs.add_mapsto; auto. reflexivity. 
  * Var.simplify.
Qed.

Lemma partitioning : forall  {X : Type} (M : Var.Map.t X) M0 M1 M2 M3,
    Var.Map.Partition M M1 M2 ->
    Var.Map.Partition M2 M0 M3 ->
    Var.Map.Partition (Var.Map.concat M1 M0) M1 M0 /\
      Var.Map.Partition (Var.Map.concat M1 M3) M1 M3 /\      
      Var.Map.Partition M (Var.Map.concat M1 M0) M3 /\
      Var.Map.Partition M M0 (Var.Map.concat M1 M3).
Proof.
  intros.
  Var.Map.Tactics.reflect_partition. Var.simplify.
  split; [ | split; [ | split] ].
  * Var.Map.Tactics.reflect_partition; auto; reflexivity.
  * Var.Map.Tactics.reflect_partition; auto; reflexivity.
  * Var.Map.Tactics.reflect_partition; Var.simplify.
    rewrite Var.Map.Proofs.concat_assoc. reflexivity.
  * apply Var.Map.Properties.Disjoint_sym in H; auto.
    Var.Map.Tactics.reflect_partition; Var.simplify.
    repeat rewrite Var.Map.Proofs.concat_assoc.
    rewrite (Var.Map.Proofs.concat_sym M0 M1); auto; try reflexivity.
Qed.

Lemma map_partition_map : forall x tau (M : Var.Map.t Expr.typ) M1 M2,
    Var.Map.MapsTo x tau M2 ->
    Var.Map.Partition M M1 M2 ->
    Var.Map.MapsTo x tau M.
Proof.
  intros x tau M M1 M2 HM2 Hpart.
  Var.Map.Tactics.reflect_partition.
  Var.solve.
  destruct (Var.Map.find x M1) eqn:HM1; auto.
  { (* x in M1 *)
    exfalso. apply (Hdisj x).
    split; Var.solve.
  }
Qed.

Lemma readd_eq: forall A x tau (CE : ChorEnv.t Expr.typ),
    Var.Map.MapsTo x tau (ChorEnv.find A CE) ->
    ChorEnv.Equal (ChorEnv.add A x tau CE) CE.
Proof.
  intros A x tau CE Hmapsto.
  unfold ChorEnv.add, ChorEnv.find in *.
  destruct (Actor.Map.find A CE) as [ctx | ] eqn:Hfind.
  2:{ Var.simplify. }
  ChorEnv.solve.
  unfold ChorEnv.find.
  rewrite Hfind. Var.solve.
Qed.

Lemma remove_add_partition : forall (CE1 CE2 CE3: ChorEnv.t Expr.typ) A B x tau,
    Var.Map.Partition (ChorEnv.find A CE1)
      (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
    Var.Map.MapsTo x tau (ChorEnv.find B CE1) ->
    Var.Map.Partition (ChorEnv.find A CE1)
      (ChorEnv.find A (ChorEnv.add B x tau CE2))
      (ChorEnv.find A (ChorEnv.remove B x CE3)).
Proof.
  intros ? ? ? ? ? ? ? Hpart Hmapsto.
  unfold ChorEnv.remove, ChorEnv.add, ChorEnv.find in *.
  Actor.simplify. Var.simplify.
    destruct (Actor.Map.find B CE1) as [ctx1 | ] eqn:HB1;
    destruct (Actor.Map.find B CE2) as [ctx2 | ] eqn:HB2;
    destruct (Actor.Map.find B CE3) as [ctx3 | ] eqn:HB3;
      Var.simplify.
  * Var.Map.Tactics.reflect_partition.
    2:{
      Var.simplify.
      intros D. Var.simplify.
      Var.reflect_find. auto.
    }

    rewrite Var.Map.MProofs.Proofs.disjoint_add_1.
    split; auto.
    { apply Var.Map.Proofs.disjoint_remove_2; auto. }
    Var.simplify.

  * Var.Map.Tactics.reflect_partition.
    2:{
      Var.simplify.
      intros y. Var.reflect_find; auto.
      destruct (Var.Map.find y ctx1); auto.
    }
    apply Var.Map.Proofs.disjoint_empty_2.

  * Var.Map.Tactics.reflect_partition.
    2:{
      Var.simplify.
      intros y. Var.reflect_find; auto.
    }
    Var.simplify. split; [ | intros [? ?]; contradiction].
    Var.simplify.
Qed.

  
Lemma map_subset_add' : forall A B y tau (CE1 : ChorEnv.t Expr.typ) CE2 CE3,
    ~ Var.Map.In y (ChorEnv.find B CE3) ->
    Var.Map.Partition (ChorEnv.find A CE1) (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
    Var.Map.Partition
      (ChorEnv.find A (ChorEnv.add B y tau CE1))
      (ChorEnv.find A (ChorEnv.add B y tau CE2)) (ChorEnv.find A CE3).
Proof.
  intros.
  Var.simplify.
  Actor.Map.Tactics.compare A B; subst; auto.
  apply Var.Map.Proofs.partition_add_l; auto.
Qed.

Lemma map_subset_add : forall A B y tau (CE1 : ChorEnv.t Expr.typ) CE2 CE3,
    Var.Map.Partition (ChorEnv.find A CE1) (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
    Var.Map.Partition
      (ChorEnv.find A (ChorEnv.add B y tau CE1))
      (ChorEnv.find A (ChorEnv.add B y tau CE2)) (ChorEnv.find A (ChorEnv.remove B y CE3)).
Proof.
  intros.
  Var.simplify.
  Actor.Map.Tactics.compare A B; subst; auto.
  Var.Map.Tactics.reflect_partition.
  * Var.simplify. 
    split; [ | intros [? ?]; try contradiction].
    intros z [Hin1 Hin2].
    Var.simplify.
    apply (Hdisj z); auto.
  * Var.simplify.
    rewrite Heq.
    Var.solve.
Qed.

Lemma add_mapsto : forall x (tau : Expr.typ) m,
    Var.Map.MapsTo x tau m ->
    Var.Map.Equal (Var.Map.add x tau m) m.
Proof.
  intros. Var.solve.
Qed.

Lemma rem_empty : forall {X : Type} A x,
    ChorEnv.Equal
      (ChorEnv.remove A x (Actor.Map.empty (Var.Map.t X)))
      (Actor.Map.empty (Var.Map.t X)).
Proof.
  intros.
  unfold ChorEnv.Equal.
  intro.
  unfold ChorEnv.remove.
  Var.simplify.
  Actor.simplify.
  Var.simplify.
Qed.

Lemma rem_empty2 : forall {X : Type} A x (CE : ChorEnv.t X),
    Var.Map.Empty (ChorEnv.find A CE) -> 
    ChorEnv.Equal (ChorEnv.remove A x CE) CE.
Proof.
  intros X A x CE H.
  intros B.
  ChorEnv.simplify.
  rewrite H.
  Var.simplify.
Qed.

Lemma members_dj : forall A B AS1 AS2,
    Actor.FSet.Empty (Actor.FSet.inter AS1 AS2) ->
    Actor.FSet.In A AS1 -> 
    Actor.FSet.In B AS2 ->
    A <> B.
Proof.
  intros A B AS1 AS2 Hinter HA HB Heq; subst.
  apply (Hinter B).
  Actor.simplify.
Qed.

Lemma inter_nin : forall A AS1 AS2,
    Actor.FSet.Empty (Actor.FSet.inter AS1 AS2) ->
    Actor.FSet.In A AS2 -> 
    ~ Actor.FSet.In A AS1.
Proof.
  intros A AS1 AS2 Hinter Hnin HH; subst.
  apply (Hinter A).
  Actor.simplify.
Qed.

Lemma singleton_nin : forall A B,
    ~ Actor.FSet.In A (Actor.FSet.singleton B) ->
    A <> B.
Proof.
  intros.
  Actor.simplify.
Qed.

Lemma concat_partition : forall {X : Type} (M1 M2 : Var.Map.t X),
    Var.Map.Properties.Disjoint M1 M2 ->
    Var.Map.Partition (Var.Map.concat M1 M2) M1 M2.
Proof.
  intros.
  Var.simplify.
Qed.

Lemma concat_partition_eq : forall {X : Type} (M M1 M2 : Var.Map.t X),
    Var.Map.Partition M M1 M2 ->
    Var.Map.Equal (Var.Map.concat M1 M2) M.
Proof.
  intros.
  pose proof (Var.Map.Proofs.partition_concat M M1 M2).
  destruct H0. 
  destruct (H0 H).
  rewrite <- H3.
  Var.simplify.
Qed.

Lemma dj_concat_dj : forall {X : Type} (M M1 M2 : Var.Map.t X),
    Var.Map.Properties.Disjoint M1 M ->
    Var.Map.Properties.Disjoint M2 M ->
    Var.Map.Properties.Disjoint M1 M2 ->
    Var.Map.Properties.Disjoint (Var.Map.concat M1 M) M2.
Proof.
  intros.
  Var.simplify.
Qed.

Lemma partition_concat_assoc : forall {X : Type} (M M1 M2 M3 : Var.Map.t X),
    Var.Map.Properties.Disjoint M1 (Var.Map.concat M2 M3) ->
    Var.Map.Properties.Disjoint M2 M3 ->
    Var.Map.Partition M M1 (Var.Map.concat M2 M3) ->
    Var.Map.Partition M (Var.Map.concat M3 M1) M2.
Proof.
  intros.
  Var.Map.Tactics.reflect_partition; Var.simplify.
  rewrite (Var.Map.Proofs.concat_sym M3 M1); auto with extra_var_db.
  rewrite <- Var.Map.Proofs.concat_assoc.
  rewrite (Var.Map.Proofs.concat_sym M2 M3); auto.
  reflexivity.
Qed.
(* STOP Easily(?) proven facts *)  

Lemma wt_disjoint : forall C A G D T,
    WellTyped G D T C ->
    Var.Map.Properties.Disjoint (ChorEnv.find A G) (ChorEnv.find A D).
Proof.
  intros C A.

  induction C as [| I C].

  (* Case Nil *)
  - intros G D T HWT.
    inversion HWT; subst.
    apply (empty_dj G D A H).

  - destruct I as [ A' e B y | A' y B z | A' y e | A' y e | A' y z e ].

    + intros G D T HWT.
      inversion HWT; subst.
      specialize (IHC
                    (ChorEnv.add B y tau G)
                    (Actor.Map.add A' DeltaA2 D)
                    (Actor.Map.add A' ThetaA2 T)
                    H9).

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.
      
      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
      
      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.
        rewrite -> (find_ab_neq1 A B y tau G H7) in IHC.
        rewrite -> (find_add A DeltaA2 D) in IHC.
        pose proof (Expr.wt_disjoint
                      (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.BANG tau) H8) as Hewtdj.
        
        apply (partition_concat_dj
                 (ChorEnv.find A G) (ChorEnv.find A D) DeltaA1 DeltaA2
                 H10 Hewtdj IHC).
      }
      (* Case A <> A' *)
      {
        rewrite -> (find_ab_neq2 A A' DeltaA2 D  HCasesAeqA'R) in IHC.

        assert (A = B \/ A <> B) as HCasesAeqB.
        tauto.
        
        destruct HCasesAeqB as [HCasesAeqBL | HCasesAeqBR].
        {
          rewrite <- HCasesAeqBL in *.
          unfold ChorEnv.add in IHC.
          rewrite (find_add A (Var.Map.add y tau (ChorEnv.find A G)) G) in IHC.
          apply (remove_dj (ChorEnv.find A G) (ChorEnv.find A D) y tau IHC).
        }
        {
          rewrite -> (find_ab_neq1 A B y tau G HCasesAeqBR) in IHC; auto.       
        }
      }

    + intros G D T HWT.
      inversion HWT; subst.
      specialize (IHC
                    (ChorEnv.remove B z (ChorEnv.remove A' y G))
                    (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A' y Expr.QUBIT D))
                    T H8).
      
      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.
      
      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
      
      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.
        rewrite -> (find_ab_neq1 A B z Expr.QUBIT (ChorEnv.add A y Expr.QUBIT D) H6) in IHC.
        unfold ChorEnv.remove in IHC at 1.
        
        rewrite -> 
          (find_ab_neq2 A B
             (Var.Map.remove z (ChorEnv.find B (ChorEnv.remove A y G)))
             (ChorEnv.remove A y G) H6)
          in IHC.

        pose proof (Var.Map.Proofs.disjoint_sym
                      (ChorEnv.find A (ChorEnv.remove A y G))
                      (ChorEnv.find A (ChorEnv.add A y Expr.QUBIT D))
                      IHC) as Hdjsym.

        unfold ChorEnv.add in Hdjsym.
        rewrite (find_add A (Var.Map.add y Expr.QUBIT (ChorEnv.find A D)) D) in Hdjsym.
        pose proof (remove_dj
                      (ChorEnv.find A D)
                      (ChorEnv.find A (ChorEnv.remove A y G))
                      y Expr.QUBIT Hdjsym) as Hrdj.
        rewrite -> (remove_find G A y) in Hrdj.
        apply (Var.Map.Proofs.disjoint_sym (ChorEnv.find A D) (ChorEnv.find A G)
                 (remove_nin_dj 
                    y (ChorEnv.find A D) (ChorEnv.find A G)
                    Hrdj H9)).
      }
      {
        assert (A = B \/ A <> B) as HCasesAeqB.
        tauto.
              
        destruct HCasesAeqB as [HCasesAeqBL | HCasesAeqBR].
              
        {
          rewrite <- HCasesAeqBL in *.
          
          unfold ChorEnv.remove in IHC at 1.
          
          rewrite (find_add A
                     (Var.Map.remove (elt:=Expr.typ) z (ChorEnv.find A (ChorEnv.remove A' y G)))
                     (ChorEnv.remove A' y G)) in IHC. 
          rewrite (add_find
                     (ChorEnv.add A' y Expr.QUBIT D)
                     A z Expr.QUBIT) in IHC. 
          unfold ChorEnv.remove in IHC.
          assert (A <> A'); auto.
          
          rewrite -> (find_ab_neq2 A A'
                        (Var.Map.remove y (ChorEnv.find A' G))
                        G H) in IHC.
          
          unfold ChorEnv.add in IHC.
          
          rewrite -> (find_ab_neq2 A A'
                        (Var.Map.add y Expr.QUBIT (ChorEnv.find A' D))
                        D H) in IHC.

          pose proof (Var.Map.Proofs.disjoint_sym
                        (Var.Map.remove (elt:=Expr.typ) z (ChorEnv.find A G))
                        (Var.Map.add z Expr.QUBIT (ChorEnv.find A D))
                        IHC) as HIHCsym.

          pose proof (remove_dj
                        (ChorEnv.find A D)
                        (Var.Map.remove (elt:=Expr.typ) z (ChorEnv.find A G))
                        z Expr.QUBIT HIHCsym) as Hrdj.

          apply (Var.Map.Proofs.disjoint_sym (ChorEnv.find A D) (ChorEnv.find A G)
                   (remove_nin_dj z (ChorEnv.find A D) (ChorEnv.find A G) Hrdj H10)).
        }
        {
          rewrite -> (find_ab_neq1
                        A B z Expr.QUBIT
                        (ChorEnv.add A' y Expr.QUBIT D)
                        HCasesAeqBR)  in IHC.
          rewrite -> (find_ab_neq1 A A' y Expr.QUBIT D HCasesAeqA'R) in IHC.

          unfold ChorEnv.remove in IHC.

          rewrite -> find_ab_neq2 in IHC; auto.
          rewrite -> find_ab_neq2 in IHC; auto.
        }
      }

    (* Case Let *)
    + intros G D T HWT.
      inversion HWT; subst.

      specialize (IHC
                    (ChorEnv.remove A' y G)
                    (Actor.Map.add A' (Var.Map.add y tau DeltaA2) D)
                    (Actor.Map.add A' ThetaA2 T)
                    H7).
      
      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.
      
      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
      
      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.
        rewrite -> find_add in IHC; auto.
        pose proof (Var.Map.Proofs.disjoint_sym
                      (ChorEnv.find A (ChorEnv.remove A y G))
                      (Var.Map.add y tau DeltaA2) IHC) as Hdjsym.
        pose proof (remove_dj DeltaA2 (ChorEnv.find A (ChorEnv.remove A y G)) y tau Hdjsym) as Hrdj.
        unfold ChorEnv.remove in Hrdj.
        rewrite -> find_add in Hrdj.        
        pose proof (remove_nin_dj y DeltaA2 
                      (ChorEnv.find A G)
                      Hrdj H10) as HCwtdj.
        
        pose proof (Expr.wt_disjoint
                      (ChorEnv.find A G) DeltaA1 ThetaA1 e tau H3) as Hewtdj.

        apply (partition_concat_dj
                 (ChorEnv.find A G) (ChorEnv.find A D) DeltaA1 DeltaA2
                 H8 Hewtdj (Var.Map.Proofs.disjoint_sym DeltaA2 (ChorEnv.find A G) HCwtdj)).
      }
      (* Case A <> A' *)
      {
        unfold ChorEnv.remove in IHC.
        rewrite -> find_ab_neq2 in IHC; auto.
        rewrite -> find_ab_neq2 in IHC; auto.
      }

      (* Case LetBang *)
      + intros G D T HWT.
        inversion HWT; subst.
      
        specialize (IHC
                      (ChorEnv.add A' y tau G)
                      (Actor.Map.add A' DeltaA2 D)
                      (Actor.Map.add A' ThetaA2 T)
                      H7).
      
        assert (A = A' \/ A <> A') as HCasesAeqA'.
        tauto.
        
        destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
        
        (* Case A = A' *)
        {
          rewrite <- HCasesAeqA'L in *.
          rewrite -> find_add in IHC; auto.

          unfold ChorEnv.add in IHC.
          rewrite -> find_add in IHC; auto.
          
          pose proof (remove_dj (ChorEnv.find A G) DeltaA2 y tau IHC) as HCwtdj.

          pose proof (Expr.wt_disjoint
                        (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.BANG tau) H6) as Hewtdj.

          apply (partition_concat_dj
                   (ChorEnv.find A G) (ChorEnv.find A D) DeltaA1 DeltaA2
                   H8 Hewtdj HCwtdj).
        }
        {
          unfold ChorEnv.add in IHC.
          rewrite -> find_ab_neq2 in IHC; auto.
          rewrite -> find_ab_neq2 in IHC; auto.
        }

      (* Case LetPair *)
      + intros G D T HWT.
        inversion HWT; subst.

        specialize (IHC
                      (ChorEnv.remove A' y (ChorEnv.remove A' z G))
                      (Actor.Map.add A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                      (Actor.Map.add A' ThetaA2 T) 
                      H5).
        
        assert (A = A' \/ A <> A') as HCasesAeqA'.
        tauto.
        
        destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
        
        (* Case A = A' *)
        {
          rewrite <- HCasesAeqA'L in *.
          rewrite -> find_add in IHC; auto.

          unfold ChorEnv.remove in IHC.
          rewrite -> find_add in IHC; auto.
          rewrite -> find_add in IHC; auto.

          pose proof (Var.Map.Proofs.disjoint_sym
                        (Var.Map.remove y (Var.Map.remove z (ChorEnv.find A G)))
                        (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) IHC) as Hdjsym.

          pose proof (remove_dj
                        (Var.Map.add z tau2 DeltaA2)
                        (Var.Map.remove y (Var.Map.remove z (ChorEnv.find A G)))
                        y tau1 Hdjsym) as HCwtdj1.
          pose proof (remove_dj
                        DeltaA2
                        (Var.Map.remove y (Var.Map.remove z (ChorEnv.find A G)))
                        z tau2 HCwtdj1) as HCwtdj2.
          clear HCwtdj1.
          pose proof (remove_nin_dj
                        y DeltaA2 (Var.Map.remove z (ChorEnv.find A G))
                        HCwtdj2 H11) as HCwtdj3.
          clear HCwtdj2.
          pose proof (remove_nin_dj
                        z DeltaA2 (ChorEnv.find A G)
                        HCwtdj3 H12) as HCwtdj.
          
          pose proof (Expr.wt_disjoint
                        (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.Tensor tau1 tau2) H4) as Hewtdj.

          apply (partition_concat_dj
                   (ChorEnv.find A G) (ChorEnv.find A D) DeltaA1 DeltaA2
                   H9 Hewtdj (Var.Map.Proofs.disjoint_sym DeltaA2 (ChorEnv.find A G) HCwtdj)).
        }          
        {
          
          unfold ChorEnv.remove in IHC.
          rewrite -> find_ab_neq2 in IHC; auto.
          rewrite -> find_ab_neq2 in IHC; auto.
          rewrite -> find_ab_neq2 in IHC; auto.
        }
Qed.

Lemma weakening_gen : forall C G D T G0,
    WellTyped G D T C ->
    forall G',
      (forall A0,
          (Var.Map.Partition (ChorEnv.find A0 G') (ChorEnv.find A0 G) (ChorEnv.find A0 G0)) /\
          (Var.Map.Properties.Disjoint (ChorEnv.find A0 G0) (ChorEnv.find A0 D))) ->
      WellTyped G' D T C.
Proof. 
  intros C. 
  induction C as [| I C IHC ].
  
  - intros G D T G0 HWT G' HE.
    inversion HWT; subst.
    apply Nil; auto.

  - destruct I as [ A e B y | A y B z | A y e | A y e | A y z e ].

    (* Case Send *)
    + intros G D T G0 HWT G' HE.
      inversion HWT; subst.

      destruct (HE A) as [HEA HEB].

      pose proof (partition_dj
                    (ChorEnv.find A G0) (ChorEnv.find A D) DeltaA1 DeltaA2 HEB H10) as HPDJ.
      
      pose proof (Expr.weakening_gen
                    (ChorEnv.find A G0) (ChorEnv.find A G)
                    DeltaA1 ThetaA1 e (Expr.BANG tau) H8 (ChorEnv.find A G') HEA HPDJ) as HEWG.

      eapply Send.     
      { auto. } 
      { eapply HEWG. }
      {
        apply (IHC
                   (ChorEnv.add B y tau G) (Actor.Map.add A DeltaA2 D)
                   (Actor.Map.add A ThetaA2 T) (ChorEnv.remove B y G0) H9 (ChorEnv.add B y tau G')).

        intros A0.
        destruct (HE A0) as [HEA0A HEA0B].
        split.
        { apply (map_subset_add A0 B y tau G' G G0 HEA0A). }
        {
          pose proof (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEA0B H10) as Hpdje. 
          apply (remove_dj_env G0 (Actor.Map.add A DeltaA2 D) A0 B y Hpdje).
        }
      }
      { auto. }
      { auto. }

    (* Case EPR *)
    + intros G D T G0 HWT G' HE.
      inversion HWT; subst.

      eapply EPR.
      { auto. }
      { 
        apply (IHC (ChorEnv.remove B z (ChorEnv.remove A y G))
                 (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A y Expr.QUBIT D))
                 T (ChorEnv.remove B z (ChorEnv.remove A y G0)) H8
                 (ChorEnv.remove B z (ChorEnv.remove A y G'))).
        intros A0.
        destruct (HE A0) as [HEA0A HEA0B].
        split.
        { 
          pose proof (partition_remove_all G' G G0 A0 A y HEA0A) as HEA0Ay.
          apply (partition_remove_all
                   (ChorEnv.remove A y G')
                   (ChorEnv.remove A y G)
                   (ChorEnv.remove A y G0)
                   A0 B z HEA0Ay).
        }
        {
          pose proof (remove_add_dj_env G0 D A0 A y (Expr.QUBIT) HEA0B) as HEA0By.
          apply (remove_add_dj_env (ChorEnv.remove A y G0) (ChorEnv.add A y Expr.QUBIT D)
                   A0 B z (Expr.QUBIT) HEA0By).
        }
      }
      { auto. }
      { auto. }

    + intros G D T G0 HWT G' HE.
      inversion HWT; subst.

      eapply LetIn.
      { 
        destruct (HE A) as [HEAA HEAB].

        pose proof (partition_dj (ChorEnv.find A G0) (ChorEnv.find A D)
                      DeltaA1 DeltaA2 HEAB H8) as Hpdj.            
        
        eapply (Expr.weakening_gen
                  (ChorEnv.find A G0)
                  (ChorEnv.find A G)
                  DeltaA1 ThetaA1 e tau H3
                  (ChorEnv.find A G')
                  HEAA Hpdj).
      }
      {
        eapply (IHC (ChorEnv.remove A y G)
                      (Actor.Map.add A (Var.Map.add y tau DeltaA2) D)
                      (Actor.Map.add A ThetaA2 T)
                      (ChorEnv.remove A y G0) H7
                      (ChorEnv.remove A y G')).

        intros A0.
        destruct (HE A0) as [HEA0A HEA0B].
        split.
        { apply (partition_remove_all G' G G0 A0 A y HEA0A). }
        { 
          pose proof (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEA0B H8) as Hpdje. 
          rewrite -> (addadd8 D A y tau DeltaA2).
          pose proof (remove_add_dj_env G0 (Actor.Map.add A DeltaA2 D) A0 A y tau Hpdje).
          auto.
        }
      }
      { auto. }
      { auto. }
      { auto. }

    (* Case LetBang *)
    + intros G D T G0 HWT G' HE.
      inversion HWT; subst.

      destruct (HE A) as [HEA HEB].

      pose proof (partition_dj
                    (ChorEnv.find A G0) (ChorEnv.find A D) DeltaA1 DeltaA2 HEB H8) as HPDJ.
      
      pose proof (Expr.weakening_gen
                    (ChorEnv.find A G0) (ChorEnv.find A G)
                    DeltaA1 ThetaA1 e (Expr.BANG tau) H6 (ChorEnv.find A G') HEA HPDJ) as HEWG.

      eapply LetBang.     
      { eauto. } 
      {
        apply (IHC
                 (ChorEnv.add A y tau G) (Actor.Map.add A DeltaA2 D)
                 (Actor.Map.add A ThetaA2 T) (ChorEnv.remove A y G0) H7 (ChorEnv.add A y tau G')).

        intros A0.
        destruct (HE A0) as [HEA0A HEA0B].
        split.
        { apply (map_subset_add A0 A y tau G' G G0 HEA0A). }
        {
          pose proof (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEA0B H8) as Hpdje. 
          apply (remove_dj_env G0 (Actor.Map.add A DeltaA2 D) A0 A y Hpdje).
        }
      }
      { auto. }
      { auto. }
      
    (* Case LetPair *)
    + intros G D T G0 HWT G' HE.
      inversion HWT; subst.

      eapply LetPair.
      { 
        destruct (HE A) as [HEAA HEAB].

        pose proof (partition_dj (ChorEnv.find A G0) (ChorEnv.find A D)
                      DeltaA1 DeltaA2 HEAB H9) as Hpdj.            
        
        eapply (Expr.weakening_gen
                  (ChorEnv.find A G0)
                  (ChorEnv.find A G)
                  DeltaA1 ThetaA1 e (Expr.Tensor tau1 tau2) H4
                  (ChorEnv.find A G')
                  HEAA Hpdj).
      }
      {
        eapply (IHC (ChorEnv.remove A y (ChorEnv.remove A z G))
                      (Actor.Map.add A  (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D) 
                      (Actor.Map.add A ThetaA2 T)
                      (ChorEnv.remove A y (ChorEnv.remove A z G0)) H5
                      (ChorEnv.remove A y (ChorEnv.remove A z G'))).

        intros A0.
        destruct (HE A0) as [HEA0A HEA0B].
        split.
        {
          pose proof (partition_remove_all G' G G0 A0 A z HEA0A) as HEA0Az.
          apply (partition_remove_all
                   (ChorEnv.remove A z G')
                   (ChorEnv.remove A z G)
                   (ChorEnv.remove A z G0)
                   A0 A y HEA0Az). 
        }
        {  
          rewrite -> (addadd8 D A y tau1 (Var.Map.add z tau2 DeltaA2)).
          rewrite -> (addadd8 D A z tau2 DeltaA2).
          pose proof (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEA0B H9) as Hpdje.
          pose proof (remove_add_dj_env G0 (Actor.Map.add A DeltaA2 D) A0 A z tau2 Hpdje) as Hpdjez.
          apply (remove_add_dj_env
                        (ChorEnv.remove A z G0)
                        (ChorEnv.add A z tau2 (Actor.Map.add A DeltaA2 D))
                        A0 A y tau1 Hpdjez).
        }
      }
      { auto. }
      { auto. }
      { auto. }
      { auto. }
      { auto. }
Qed.


Lemma wt_subst_bang : forall C tau G D T A x v,
    WellTyped (ChorEnv.add A x tau G) D T C ->
    Expr.WellTyped (Var.Map.empty _) (Var.Map.empty _) (Var.Map.empty _) v tau ->
    WellTyped G D T (Choreography.subst A x v C).
Proof.
    intros C. induction C as [| I C IHC ].
    
  (* Case C = Nil *)
    - intros tau G D T A x v HWT HWTV.
      unfold Choreography.subst.
      inversion HWT; subst.
      apply Nil; auto.

    (* Case C = I::C' *) 
    - intros tau G D T A x v HWT HWTV.
      destruct I as [ A' e B y | A' y B z | A' y e | A' y e | A' y z e ].

      (* Case Send *)
      + inversion HWT; subst.

        specialize (IHC tau
                      (ChorEnv.add B y tau0 G)
                      (Actor.Map.add A' DeltaA2 D)
                      (Actor.Map.add A' ThetaA2 T)
                      A x v).
        
        assert (A = A' \/ A <> A') as HCasesAeqA'.
        tauto.
        
        destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
        
        (* Case A = A' *)
        {
          rewrite <- HCasesAeqA'L in *.

          unfold ChorEnv.add in H8.
          rewrite -> find_add in H8.
          pose proof
            (Expr.wt_subst_bang e tau (ChorEnv.find A G) DeltaA1 ThetaA1 x v (Expr.BANG tau0)
            HWTV H8) as HEWTSB.

          - eapply Send; auto.

            {
              destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              { eauto. }
              { contradiction. }
            }

            { 
              fold Choreography.subst.
              unfold Insn.rebound_in.
              destruct (Insn.bind_eqb (A, x) (B, y)) eqn:Hbeq.
              { 
                destruct (beq A B x y) as [HbeqL _].
                destruct (HbeqL Hbeq) as [HABeq _].
                contradiction.
              }
              {
                rewrite addadd5 in H9; auto.
              }
            }

            { auto. }
            { auto. }
        }
        (* Case A <> A' *)
        {
          rewrite find_ab_neq1 in H8; auto.

          eapply Send; auto.
                   
          {
            destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. }
          }
            { 
              fold Choreography.subst.
              unfold Insn.rebound_in.
              destruct (Insn.bind_eqb (A, x) (B, y)) eqn:Hbeq.
              { 
                destruct (beq A B x y) as [HbeqL _].
                destruct (HbeqL Hbeq) as [HABeqL HABeqR].
                rewrite <- HABeqL in *.
                rewrite <- HABeqR in *.
                rewrite overwrite in H9.
                eauto.
              }
              {
                rewrite addadd5 in H9; auto.
              }
            }

            { auto. }
            
            { auto. }
        }

      (* Case EPR *)
      + inversion HWT; subst.
        
        assert (A = A' \/ A <> A') as HCasesAeqA'.
        tauto.
        
        destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
        
        (* Case A = A' *)
        {
          rewrite <- HCasesAeqA'L in *.

          eapply EPR; auto.

          {
            fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.EPR A y B z)) eqn:Hrin.
            {
              unfold Insn.rebound_in in Hrin.
              rewrite orb_true_iff in Hrin.
              destruct Hrin.
              {
                destruct (beq A A x y) as [HbeqL _].
                destruct (HbeqL H) as [_ HAAeqR].
                rewrite <- HAAeqR in *.
                rewrite rmadd1 in H8.
                auto.
              }
              {
                destruct (beq A B x z) as [HbeqL _].
                destruct (HbeqL H) as [HAAeqL _].
                contradiction.
              }
            }
            {
              unfold Insn.rebound_in in Hrin.
              rewrite orb_false_iff in Hrin.
              destruct Hrin as [HbeqA HbeqB].

              rewrite rmadd2 in H8; auto.
              rewrite rmadd2 in H8; auto.
              
              apply (IHC tau
                       (ChorEnv.remove B z (ChorEnv.remove A y G))
                       (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A y Expr.QUBIT D))
                       T A x v H8 HWTV).
            }
          }
        }
        {
          apply EPR; auto.
          
          {
            fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.EPR A' y B z)) eqn:Hrin.
            {
              unfold Insn.rebound_in in Hrin.
              rewrite orb_true_iff in Hrin.
              destruct Hrin.
              {
                destruct (beq A A' x y) as [HbeqL _].
                destruct (HbeqL H) as [HAAeqL _].
                contradiction.
              }
              {
                assert (Insn.bind_eqb (A, x) (A', y) <> true) as HnbeqAA'.
                apply (nbeq A A' x y HCasesAeqA'R).
                destruct (not_true_iff_false (Insn.bind_eqb (A, x) (A', y))) as [HntL _].
                pose proof (HntL HnbeqAA').
                destruct (beq A B x z) as [HbeqL _].
                destruct (HbeqL H) as [HABeqL HABeqR].
                rewrite <- HABeqL in *.
                rewrite <- HABeqR in *.
                rewrite -> rmadd2 in H8; auto.
                rewrite -> (rmadd1 (ChorEnv.remove A' y G) A x tau) in H8.
                auto.
              }
            }
            {
              unfold Insn.rebound_in in Hrin.
              rewrite orb_false_iff in Hrin.
              destruct Hrin as [HneqA HneqB].
              rewrite rmadd2 in H8; auto.
              rewrite rmadd2 in H8; auto.
              apply (IHC
                       tau 
                       (ChorEnv.remove B z (ChorEnv.remove A' y G))
                       (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A' y Expr.QUBIT D))
                       T A x v H8 HWTV).
            }
          }
        }

      (* Case Let *)
      +  inversion HWT; subst.
        
         assert (A = A' \/ A <> A') as HCasesAeqA'.
         tauto.
         
         destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
         
         (* Case A = A' *)
         {
           rewrite <- HCasesAeqA'L in *.
           
           eapply LetIn; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
             {
               unfold ChorEnv.add in H3.
               rewrite find_add in H3.
               pose proof
                 (Expr.wt_subst_bang e tau (ChorEnv.find A G) DeltaA1 ThetaA1 x v tau0
                    HWTV H3) as HEWTSB.
               eauto.
             }
             { contradiction. }
           }

           {
             fold Choreography.subst.
             unfold Insn.rebound_in.
             destruct (Insn.bind_eqb (A, x) (A, y)) eqn:Hbeq.
             { 
               destruct (beq A A x y) as [HbeqL _].
               destruct (HbeqL Hbeq) as [_ Heqxy].
               rewrite <- Heqxy in *.
               rewrite rmadd1 in H7.
               eauto.
             }
             {
               rewrite rmadd2 in H7; auto.
               apply (IHC tau
                        (ChorEnv.remove A y G)
                        (Actor.Map.add A (Var.Map.add y tau0 DeltaA2) D)
                        (Actor.Map.add A ThetaA2 T)
                        A x v H7 HWTV).
             }
           }

           { auto. }
           { auto. }
           { auto. }
         }
         {
           eapply LetIn; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
             { contradiction. }
             { 
               rewrite find_ab_neq1 in H3; auto.
               eauto.
             }
           }

           {
             fold Choreography.subst.
             unfold Insn.rebound_in.
             destruct (Insn.bind_eqb (A, x) (A', y)) eqn:Hbeq.
             { 
               destruct (beq A A' x y) as [HbeqL _].
               destruct (HbeqL Hbeq) as [HeqAB _].
               contradiction.
             }
             {
               rewrite rmadd2 in H7; auto.
               apply (IHC tau
                        (ChorEnv.remove A' y G)
                        (Actor.Map.add A' (Var.Map.add y tau0 DeltaA2) D)
                        (Actor.Map.add A' ThetaA2 T)
                        A x v H7 HWTV).
             }
           }

           { auto. }
           { auto. }
           { auto. }

         }

      (* Case LetBang *)
      +  inversion HWT; subst.
                 
         assert (A = A' \/ A <> A') as HCasesAeqA'.
         tauto.
         
         destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
         
         (* Case A = A' *)
         {
           rewrite <- HCasesAeqA'L in *.
           
           eapply LetBang; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
             {
               unfold ChorEnv.add in H6.
               rewrite find_add in H6.
               pose proof
                 (Expr.wt_subst_bang e tau (ChorEnv.find A G) DeltaA1 ThetaA1 x v (Expr.BANG tau0)
                    HWTV H6) as HEWTSB.
               eauto.
             }
             { contradiction. }
           }

           {
             fold Choreography.subst.
             unfold Insn.rebound_in.
             destruct (Insn.bind_eqb (A, x) (A, y)) eqn:Hbeq.
             { 
               destruct (beq A A x y) as [HbeqL _].
               destruct (HbeqL Hbeq) as [_ Heqxy].
               rewrite <- Heqxy in *.
               rewrite overwrite in H7.
               eauto.
             }
             {
               rewrite addadd5 in H7; auto.
               apply (IHC tau
                        (ChorEnv.add A y tau0 G)
                        (Actor.Map.add A DeltaA2 D)
                        (Actor.Map.add A ThetaA2 T)
                        A x v H7 HWTV).
             }
           }

           { auto. }
           { auto. }
         }
         {
           eapply LetBang; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
             { contradiction. }
             { 
               rewrite find_ab_neq1 in H6; auto.
               eauto.
             }
           }

           {
             fold Choreography.subst.
             unfold Insn.rebound_in.
             destruct (Insn.bind_eqb (A, x) (A', y)) eqn:Hbeq.
             { 
               destruct (beq A A' x y) as [HbeqL _].
               destruct (HbeqL Hbeq) as [HeqAB _].
               contradiction.
             }
             {
               rewrite addadd5 in H7; auto.
               apply (IHC tau
                        (ChorEnv.add A' y tau0 G)
                        (Actor.Map.add A' DeltaA2 D)
                        (Actor.Map.add A' ThetaA2 T)
                        A x v H7 HWTV).
             }
           }

           { auto. }
           { auto. }
         }

      (* Case LetPair *)
      + inversion HWT; subst.
        
        assert (A = A' \/ A <> A') as HCasesAeqA'.
        tauto.
        
        destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
        
        (* Case A = A' *)
        {
          rewrite <- HCasesAeqA'L in *.
          
          eapply LetPair; auto.
          
          {
            destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
            {
              unfold ChorEnv.add in H4.
              rewrite find_add in H4.
              pose proof
                (Expr.wt_subst_bang e tau
                   (ChorEnv.find A G) DeltaA1 ThetaA1
                   x v (Expr.Tensor tau1 tau2)
                   HWTV H4) as HEWTSB.
              eauto.
            }
            { contradiction. }
          }
          
          {
            fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.LetPair A y z e)) eqn:Hrbi.
            {
              unfold Insn.rebound_in in Hrbi.
              rewrite orb_true_iff in Hrbi.
              destruct Hrbi as [HrbiA | HrbiB].
              {
                rewrite remrem.
                rewrite remrem in H5.
                destruct (beq A A x y) as [HbeqL _].
                destruct (HbeqL HrbiA) as [_ Heqxy].
                rewrite <- Heqxy in *.
                rewrite rmadd1 in H5.
                eauto.
              }
              {
                destruct (beq A A x z) as [HbeqL _].
                destruct (HbeqL HrbiB) as [_ Heqxz].
                rewrite <- Heqxz in *.
                rewrite rmadd1 in H5.
                eauto.
              }                
            }
            {
              unfold Insn.rebound_in in Hrbi.
              rewrite orb_false_iff in Hrbi.
              destruct Hrbi as [HrbiA HrbiB].

              rewrite rmadd2 in H5; auto.
              rewrite rmadd2 in H5; auto.
               apply (IHC tau
                        (ChorEnv.remove A y (ChorEnv.remove A z G))
                        (Actor.Map.add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                        (Actor.Map.add A ThetaA2 T) 
                        A x v H5 HWTV).
            }
          }

          { auto. }
          { auto. }
          { auto. }
          { auto. }
        }
        {
          eapply LetPair; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
             { contradiction. }
             { 
               rewrite find_ab_neq1 in H4; auto.
               eauto.
             }
           }

           {
             fold Choreography.subst.
             destruct (Insn.rebound_in A x (Insn.LetPair A' y z e)) eqn:Hrbi.
             {
               unfold Insn.rebound_in in Hrbi.
               rewrite orb_true_iff in Hrbi.
               destruct Hrbi as [HrbiA | HrbiB].
               {
                 destruct (beq A A' x y) as [HbeqL _].
                 destruct (HbeqL HrbiA) as [HeqAB _].
                 contradiction.
               }
               {
                 destruct (beq A A' x z) as [HbeqL _].
                 destruct (HbeqL HrbiB) as [HeqAB _].
                 contradiction.                 
               }
             }
             {
               unfold Insn.rebound_in in Hrbi.
               rewrite orb_false_iff in Hrbi.
               destruct Hrbi as [HrbiA HrbiB].
               {
                 rewrite rmadd2 in H5; auto.
                 rewrite rmadd2 in H5; auto.
                 apply (IHC tau
                          (ChorEnv.remove A' y (ChorEnv.remove A' z G))
                          (Actor.Map.add A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                          (Actor.Map.add A' ThetaA2 T)
                          A x v H5 HWTV).
               }
             }
           }
           { auto. }
           { auto. }
           { auto. }
           { auto. }
         }
Qed.        

Lemma subst_not_in : forall C A x v G D T,
    WellTyped G D T C ->
    ~ (Var.Map.In x (ChorEnv.find A D)) ->
    ~ (Var.Map.In x (ChorEnv.find A G)) ->
    (Choreography.subst A x v C) = C.
Proof.
  intros C A x v. 

  induction C as [| I C].

  - intros G D T HWTC HninD HninG.
    simpl; auto.

  - intros G D T HWTC HninD HninG.
    destruct I as [ A' e B y | A' y B z | A' y e | A' y e | A' y z e ].

    (* Case Send *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.

      assert
        ((if Actor.FSet.MF.eq_dec A A' then Expr.subst x v e else e) = e) as Hgoale.
      {
        destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
        {
          subst.

          apply(Expr.subst_not_in e x v 
                  (ChorEnv.find A' G) DeltaA1 ThetaA1 (Expr.BANG tau)
                  H8 HninG
                  (nin_partition x (ChorEnv.find A' D) DeltaA1 DeltaA2 HninD H10)).
        }
        { auto. }
      }

      assert
        ((if Insn.rebound_in A x (Insn.Send A' e B y) then C else Choreography.subst A x v C) = C) as HgoalC.
      {
        unfold Insn.rebound_in.
        destruct (Insn.bind_eqb (A, x) (B, y)) eqn:Hbeq.
        {
          setoid_rewrite Hbeq.
          auto.
        }
        {
          setoid_rewrite Hbeq.

          specialize (IHC
                        (ChorEnv.add B y tau G)
                        (Actor.Map.add A' DeltaA2 D)
                        (Actor.Map.add A' ThetaA2 T)
                        H9).

          pose proof (find_nbeq G A x B y tau Hbeq HninG) as Hnbeq.

          assert (~ Var.Map.In x (ChorEnv.find A (Actor.Map.add A' DeltaA2 D))) as HninDadd.
          {
            assert (A = A' \/ A <> A') as HAA'eq.
            tauto.
            destruct HAA'eq as [HAA'eqL |  HAA'eqR].
            {
              rewrite <- HAA'eqL in *.
              rewrite find_add; auto.
              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A D) DeltaA1 DeltaA2 H10) as Hpart.
              apply (nin_partition x (ChorEnv.find A D) DeltaA2 DeltaA1 HninD Hpart).
            }
            {
              rewrite (find_ab_neq2 A A' DeltaA2 D HAA'eqR).
              auto.
            }
          }

          apply (IHC HninDadd Hnbeq).
        }
      }
      
      setoid_rewrite Hgoale.
      setoid_rewrite HgoalC.
      auto.

    (* Case EPR *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.

      assert
        ((if Insn.rebound_in A x (Insn.EPR A' y B z) then C else Choreography.subst A x v C) = C)
        as HgoalC.
      {
        destruct (Insn.rebound_in A x (Insn.EPR A' y B z)) eqn:Hrbi.
        { auto. }
        {
          unfold Insn.rebound_in in Hrbi.
          rewrite orb_false_iff in Hrbi.
          destruct Hrbi as [HrbiA HrbiB].
          
          specialize (IHC
                        (ChorEnv.remove B z (ChorEnv.remove A' y G))
                        (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A' y Expr.QUBIT D))
                        T
                        H8).

          pose proof (nin_remove_ce (ChorEnv.remove A' y G) A x B z
                        (nin_remove_ce G A x A' y HninG)) as HninGzy.

          pose proof (find_nbeq
                        (ChorEnv.add A' y Expr.QUBIT D)
                        A x B z Expr.QUBIT HrbiB
                        (find_nbeq D A x A' y Expr.QUBIT HrbiA HninD)) as HninDzy.

          apply (IHC HninDzy HninGzy).
        }
      }

      setoid_rewrite HgoalC; auto.

      (* Case Let *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.
      
      assert
        ((if Actor.FSet.MF.eq_dec A A' then Expr.subst x v e else e) = e) as Hgoale.
      {
        destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
        {
          subst.

          apply(Expr.subst_not_in e x v 
                  (ChorEnv.find A' G) DeltaA1 ThetaA1 tau
                  H3 HninG
                  (nin_partition x (ChorEnv.find A' D) DeltaA1 DeltaA2 HninD H8)).
        }
        { auto. }
      }

      assert
        ((if Insn.rebound_in A x (Insn.Let A' y e) then C else Choreography.subst A x v C) = C) as HgoalC.
      {
        unfold Insn.rebound_in.
        destruct (Insn.bind_eqb (A, x) (A', y)) eqn:Hbeq.
        {
          setoid_rewrite Hbeq.
          auto.
        }
        {
          setoid_rewrite Hbeq.

          specialize (IHC
                        (ChorEnv.remove A' y G)
                        (Actor.Map.add A' (Var.Map.add y tau DeltaA2) D) 
                        (Actor.Map.add A' ThetaA2 T)
                        H7).

          pose proof (nin_remove_ce G A x A' y HninG) as Hnbeq.

          assert (~ Var.Map.In x (ChorEnv.find A (Actor.Map.add A' (Var.Map.add y tau DeltaA2) D)))
            as HninDadd.
          {
            assert (A = A' \/ A <> A') as HAA'eq.
            tauto.
            destruct HAA'eq as [HAA'eqL |  HAA'eqR].
            {
              rewrite <- HAA'eqL in *.
              rewrite find_add; auto.

              
              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A D) DeltaA1 DeltaA2 H8) as Hpart.
              
              apply (nin_mapl DeltaA2 x y tau (nbeqeq A x y Hbeq)
                       (nin_partition x (ChorEnv.find A D) DeltaA2 DeltaA1 HninD Hpart)).
            }
            {
              rewrite (find_ab_neq2 A A' (Var.Map.add y tau DeltaA2) D HAA'eqR).
              auto.
            }
          }

          apply (IHC HninDadd Hnbeq).
        }
      }

      setoid_rewrite Hgoale.
      setoid_rewrite HgoalC.
      auto.

    (* Case LetBang *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.

      assert
        ((if Actor.FSet.MF.eq_dec A A' then Expr.subst x v e else e) = e) as Hgoale.
      {
        destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
        {
          subst.

          apply(Expr.subst_not_in e x v 
                  (ChorEnv.find A' G) DeltaA1 ThetaA1 (Expr.BANG tau)
                  H6 HninG
                  (nin_partition x (ChorEnv.find A' D) DeltaA1 DeltaA2 HninD H8)).
        }
        { auto. }
      }

      assert
        ((if Insn.rebound_in A x (Insn.LetBang A' y e) then C else Choreography.subst A x v C) = C) as HgoalC.
      {
        unfold Insn.rebound_in.
        destruct (Insn.bind_eqb (A, x) (A', y)) eqn:Hbeq.
        {
          setoid_rewrite Hbeq.
          auto.
        }
        {
          setoid_rewrite Hbeq.

          specialize (IHC
                        (ChorEnv.add A' y tau G)
                        (Actor.Map.add A' DeltaA2 D)
                        (Actor.Map.add A' ThetaA2 T)
                        H7).

          pose proof (find_nbeq G A x A' y tau Hbeq HninG) as Hnbeq.

          assert (~ Var.Map.In x (ChorEnv.find A (Actor.Map.add A' DeltaA2 D))) as HninDadd.
          {
            assert (A = A' \/ A <> A') as HAA'eq.
            tauto.
            destruct HAA'eq as [HAA'eqL |  HAA'eqR].
            {
              rewrite <- HAA'eqL in *.
              rewrite find_add; auto.
              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A D) DeltaA1 DeltaA2 H8) as Hpart.
              apply (nin_partition x (ChorEnv.find A D) DeltaA2 DeltaA1 HninD Hpart).
            }
            {
              rewrite (find_ab_neq2 A A' DeltaA2 D HAA'eqR).
              auto.
            }
          }

          apply (IHC HninDadd Hnbeq).
        }
      }
      
      setoid_rewrite Hgoale.
      setoid_rewrite HgoalC.
      auto.

    (* Case LetPair *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.
      
      assert
        ((if Actor.FSet.MF.eq_dec A A' then Expr.subst x v e else e) = e) as Hgoale.
      {
        destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
        {
          subst.

          apply(Expr.subst_not_in e x v 
                  (ChorEnv.find A' G) DeltaA1 ThetaA1 (Expr.Tensor tau1 tau2)
                  H4 HninG
                  (nin_partition x (ChorEnv.find A' D) DeltaA1 DeltaA2 HninD H9)).
        }
        { auto. }
      }

      assert
        ((if Insn.rebound_in A x (Insn.LetPair A' y z e) then C else Choreography.subst A x v C) = C) as HgoalC.
      {
        destruct (Insn.rebound_in A x (Insn.LetPair A' y z e)) eqn:Hrbi.
        { auto. }        
        {
          unfold Insn.rebound_in in Hrbi.
          rewrite orb_false_iff in Hrbi.
          destruct Hrbi as [HrbiA HrbiB].
          {
            specialize (IHC
                          (ChorEnv.remove A' y (ChorEnv.remove A' z G))
                          (Actor.Map.add A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                          (Actor.Map.add A' ThetaA2 T)                          
                          H5).

            pose proof (nin_remove_ce (ChorEnv.remove A' z G) A x A' y
                          (nin_remove_ce G A x A' z HninG)) as HninGzy.

            assert (~ Var.Map.In x
                      (ChorEnv.find A
                         (Actor.Map.add A'
                            (Var.Map.add y tau1
                               (Var.Map.add z tau2 DeltaA2)) D)))
              as HninDadd.
            {
              assert (A = A' \/ A <> A') as HAA'eq.
              tauto.
              destruct HAA'eq as [HAA'eqL |  HAA'eqR].
              {
                rewrite <- HAA'eqL in *.
                rewrite find_add; auto.

                pose proof (nbeqeq A x y HrbiA) as Hnexy.
                pose proof (nbeqeq A x z HrbiB) as Hnexz.
                
                pose proof (@Var.Map.Properties.Partition_sym _
                              (ChorEnv.find A D) DeltaA1 DeltaA2 H9) as Hpart.

                pose proof (nin_partition x (ChorEnv.find A D) DeltaA2 DeltaA1 HninD Hpart) as HninDA2.

                apply (nin_mapl (Var.Map.add z tau2 DeltaA2) x y tau1 Hnexy
                              (nin_mapl DeltaA2 x z tau2 Hnexz HninDA2)).
              }
              {
                rewrite (find_ab_neq2 A A' (Var.Map.add y tau1  (Var.Map.add z tau2 DeltaA2)) D HAA'eqR).
                auto.
              }
            }
            
            apply (IHC HninDadd HninGzy).
          }
        }
      }
      
      setoid_rewrite Hgoale.
      setoid_rewrite HgoalC.
      auto.
Qed.

Lemma wt_subst_lin : forall C ThetaA1 ThetaA2 tau G D T A x v,
    Expr.WellTyped (Var.Map.empty _) (Var.Map.empty _) ThetaA1 v tau ->
    WellTyped G (ChorEnv.add A x tau D) (Actor.Map.add A ThetaA2 T) C ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x (ChorEnv.find A G) ->
    ~ Var.Map.In x (ChorEnv.find A D) ->
    WellTyped G D T (Choreography.subst A x v C).
Proof.
  intros C. induction C as [| I C IHC ].

  (* Case C = Nil is not possible. *)
  - intros ThetaA1 ThetaA2 tau G D T A x v Hv HC HinG HinD HninD.
    inversion HC; subst.
    pose proof (add_empty_delta A x tau D).
    contradiction.
    
  (* Case C = I::C' *) 
  - intros ThetaA1 ThetaA2 tau G D T A x v Hv HC HinT HninG HninD.
    destruct I as [ A' e B y | A' y B z | A' y e | A' y e | A' y z e ].

    (* Case Send *)
    + inversion HC. subst.

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.
        
        assert (Var.Map.In x DeltaA1 \/ ~ Var.Map.In x DeltaA1) as HESL.
        tauto.

        destruct HESL as [HinDA | HninDA]. 
        (* Case x in e *)          
        {
          (* prepare witness for expression e typing and partioning facts. *)
          rewrite -> (add_find D A x tau) in H10.
          pose proof (inin (ChorEnv.find A D) DeltaA1 DeltaA2
                        x tau H10 HinDA) as Hinin.
          destruct (mapsto_destruct x tau DeltaA1 Hinin) as [DeltaA1' HDA'].
          destruct HDA' as [HDA'A HDA'B].
          rewrite -> HDA'A in H8.
          pose proof 
            (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
               (Var.Map.concat ThetaA1 ThetaA0) x v (Expr.BANG tau0) Hv H8) as HWTS.
          rewrite -> (find_add A ThetaA2 T) in H11.
          
          (* partioning facts. *)
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H11)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          (* e typing witness. *)
          specialize (HWTS HPartitionA HninG HDA'B).
          
          (* prepare witness for choreography C typing *)
          rewrite -> (addadd1 A D DeltaA2 x tau) in H9.
          rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H9.
          
          (* prepare hypotheses for partitioning requirements *)
          assert (H : Var.Map.Equal (Var.Map.add x tau DeltaA1') DeltaA1).
          { symmetry. auto. }
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau H H10 HninD HDA'B) as Hnin.
          pose proof (subst_not_in
                        C A x v
                        (ChorEnv.add B y tau0 G)
                        (Actor.Map.add A DeltaA2 D)
                        (Actor.Map.add A ThetaA3 T)
                        H9) as HCSL.
          rewrite -> (find_add A DeltaA2 D) in HCSL.
          destruct Hnin as [HninA HninB].
          
          (* prove main goal in subcases *)
          - eapply Send.
            
            + auto.
              
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              { eauto. }
              { contradiction. }
              
            + fold Choreography.subst.
              destruct (Insn.rebound_in A x) eqn:Heq.
              {
                assert (~ (Insn.rebound_in A x (Insn.Send A e B y) = true)).
                simpl.
                eapply (nbeq A B x y H7).
                contradiction.
              }
              {
                rewrite (find_ab_neq1 A B y tau0 G H7) in HCSL.
                specialize (HCSL HninA HninG).
                rewrite -> HCSL.
                eauto.
              }
              
            + auto.
              
            + auto.
        }
        (* case x not in e *)
        {
          pose proof (Expr.subst_not_in e x v
                        (ChorEnv.find A G) DeltaA1 ThetaA0 (Expr.BANG tau0)
                        H8 HninG HninDA) as Hesubst.
          rewrite -> (add_find D A x tau) in H10.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H10 HninDA) as Hini.

          (* partioning facts *)
          rewrite -> (find_add A ThetaA2 T) in H11.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H11)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          
          (* prove main goal in subcases *)
          - eapply Send.
            
            + auto.
              
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              {
                rewrite -> Hesubst.
                eauto.
              }
              { auto. }
              
            + fold Choreography.subst.
              destruct (Insn.rebound_in A x (Insn.Send A e B y)) eqn:Heq.
              { 
                assert (~ (Insn.rebound_in A x (Insn.Send A e B y) = true)).
                simpl.
                apply (nbeq A B x y H7).
                contradiction.
              }
              {
                (* specialize and apply IH *)
                specialize (IHC ThetaA1 ThetaA3 tau
                              (ChorEnv.add B y tau0 G)
                              (Actor.Map.add A (Var.Map.remove x DeltaA2) D)
                              (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T)
                              A x v
                              Hv).
                assert (IHWT : WellTyped (ChorEnv.add B y tau0 G)
                                         (ChorEnv.add A x tau (Actor.Map.add A
                                            (Var.Map.remove (elt:=Expr.typ) x DeltaA2) D))
                                         (Actor.Map.add A ThetaA3
                                            (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T))
                                         C).
                {
                  eapply WellTypedProper; eauto.
                  + reflexivity.
                  + 
                    rewrite add_remove; auto.
                    unfold ChorEnv.add.
                    rewrite addadd2.
                    reflexivity.
                  + rewrite addadd2. rewrite addadd2. reflexivity. 
                }
                specialize (IHC IHWT).
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                specialize (IHC HPartitionB).
                rewrite -> (find_ab_neq1 A B y tau0 G H7) in IHC.
                specialize (IHC HninG).
                rewrite -> (find_add A (Var.Map.remove (elt:=Expr.typ) x DeltaA2) D) in IHC.
                specialize (IHC (nin_remove DeltaA2 x)).
                eauto.
              }
              
            + apply (partition_remove (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H10 HninD HninDA).
              
            + auto.
        }
      }
      (* Case A <> A' *)
      {
        - eapply Send.

          + auto.

          + destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. }

          + fold Choreography.subst.          
            rewrite -> (addadd3 D A x tau A' DeltaA2) in H9; auto.
            
            destruct (Insn.rebound_in A x (Insn.Send A' e B y)) eqn:Heq.
            {
              assert  (~ Insn.rebound_in A x (Insn.Send A' e B y) = true).

              unfold Insn.rebound_in.
              destruct (Insn.bind_eqb_false (A,x) (B,y)) as [HBEQA HBEQB].
              destruct (not_true_iff_false (Insn.bind_eqb (A, x) (B, y))) as [HNTFA HNTFB].
              apply HNTFB.
              apply HBEQB.

              pose proof (wt_disjoint C A
                            (ChorEnv.add B y tau0 G)
                            (ChorEnv.add A x tau (Actor.Map.add A' DeltaA2 D))
                            (Actor.Map.add A' ThetaA3 (Actor.Map.add A ThetaA2 T))
                            H9) as HWTDJ.

              assert (A = B \/ A <> B) as HCasesAeqB.
              tauto.
              
              destruct HCasesAeqB as [HCasesAeqBL | HCasesAeqBR].
              
              {
                rewrite <- HCasesAeqBL in *.
                assert (A <> A'); auto.
                pose proof (nin_dj x
                              (ChorEnv.find A (ChorEnv.add A y tau0 G))
                              (ChorEnv.find A (ChorEnv.add A x tau (Actor.Map.add A' DeltaA2 D)))
                              HWTDJ
                              (in_beq (Actor.Map.add A' DeltaA2 D) A x tau)) as Hnindj.
                rewrite -> (add_find G A y tau0) in Hnindj.
                pose proof (nin_nxeq (ChorEnv.find A G) x y tau0 Hnindj).
                apply (Insn.nbeqlr (A,x) (A,y)).
                auto.
              }
              {
                apply (Insn.nbeqlr (A,x) (B,y)).
                auto.
              }

              contradiction.
            }
            {
              (* specialize and apply IH *)
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H9.
              specialize (IHC ThetaA1 ThetaA2 tau
                            (ChorEnv.add B y tau0 G)
                            (Actor.Map.add A' DeltaA2 D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hv H9).
              rewrite -> (find_ab_neq2 A A' ThetaA3 T HCasesAeqA'R) in IHC.
              rewrite -> (find_ab_neq2 A A' DeltaA2 D HCasesAeqA'R) in IHC.
              simpl in Heq.
              pose proof (find_nbeq G A x B y tau0 Heq HninG) as HninG'.
              eapply (IHC HinT HninG' HninD).
            }

          + rewrite -> (find_ab_neq1 A' A x tau D) in H10; auto.

          + rewrite -> (find_ab_neq2 A' A ThetaA2 T) in H11; auto.
      }

    (* Case EPR *)
    + inversion HC. subst.
      pose proof (nin_nbeq D A x tau A' y H9) as HninAA'.
      pose proof (nin_nbeq D A x tau B z H10) as HninAB.
      rewrite -> (addadd5 D A' y Expr.QUBIT A x tau HninAA') in H8.
      rewrite -> (addadd5 (ChorEnv.add A' y Expr.QUBIT D) B z Expr.QUBIT A x tau HninAB) in H8.
      
      pose proof (nin_nbeq_add1 D A x A' y Expr.QUBIT HninAA' HninD) as HaddAA'.
      pose proof (nin_nbeq_add1 (ChorEnv.add A' y Expr.QUBIT D) A x B z
                    Expr.QUBIT HninAB HaddAA') as HaddAB.

      pose proof (nin_remove_ce G A x A' y HninG) as HninGy.
      pose proof (nin_remove_ce (ChorEnv.remove A' y G) A x B z HninGy) as HninGyz.

      (* specialize and apply IH *)
      specialize (IHC ThetaA1 ThetaA2 tau (ChorEnv.remove B z (ChorEnv.remove A' y G))
                    (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A' y Expr.QUBIT D))
                    T A x v Hv H8 HinT HninGyz HaddAB).

      eapply EPR; auto.

      fold Choreography.subst.
      destruct (Insn.rebound_in A x (Insn.EPR A' y B z)) eqn:Heq.      
      {
        simpl in Heq.
        destruct (Insn.bind_eqb (A, x) (A', y)) eqn:H.
        {
          setoid_rewrite -> HninAA' in H.
          discriminate.
        }
        {
          simpl in Heq.
          setoid_rewrite -> HninAB in Heq.
          discriminate.
        }
      }

      auto.
      
      setoid_rewrite <- (Insn.bind_eqb_symmetric (A', y) (A, x)) in HninAA'.
      apply (nin_nbeq_add2 D A' y A x tau HninAA') in H9.
      auto.
      
      setoid_rewrite <- (Insn.bind_eqb_symmetric (B, z) (A, x)) in HninAB.
      apply (nin_nbeq_add2 D B z A x tau HninAB) in H10.
      auto.

    (* Case Let *)
    + inversion HC; subst.

      pose proof (nin_remove_ce G A x A' y HninG) as HninGy.   

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.

        assert (Var.Map.In x DeltaA1 \/ ~ Var.Map.In x DeltaA1) as HESL.
        tauto.

        destruct HESL as [HinDA | HninDA].
        (* Case x in e *) 
        {
          (* prepare witness for expression e typing and partioning facts. *)
          rewrite -> (add_find D A x tau) in H8.
          pose proof (inin (ChorEnv.find A D) DeltaA1 DeltaA2
                        x tau H8 HinDA) as Hinin.
          destruct (mapsto_destruct x tau DeltaA1 Hinin) as [DeltaA1' HDA'].
          destruct HDA' as [HDA'A HDA'B].
          rewrite -> HDA'A in H3.
          pose proof
            (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
               (Var.Map.concat ThetaA1 ThetaA0) x v tau0 Hv H3) as HWTS.
          pose proof (find_add A ThetaA2 T) as HFA.
          rewrite -> HFA in H9.
          (* partioning facts. *)
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          (* e typing witness. *)
          specialize (HWTS HPartitionA HninG HDA'B).

          (* prepare witness for choreography C typing *)
          rewrite -> (addadd1 A D (Var.Map.add y tau0 DeltaA2) x tau) in H7. 
          rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H7.

          (* prepare hypotheses for partitioning requirements *)
          assert (Var.Map.Equal (Var.Map.add x tau DeltaA1') DeltaA1).
          { symmetry. auto. }
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau H H8 HninD HDA'B) as Hnin.
          pose proof (subst_not_in
                        C A x v
                        (ChorEnv.remove A y G)
                        (Actor.Map.add A  (Var.Map.add y tau0 DeltaA2) D)
                        (Actor.Map.add A ThetaA3 T)
                        H7) as HCSL.
          rewrite -> (find_add A (Var.Map.add y tau0 DeltaA2) D) in HCSL.
          destruct Hnin as [HninA HninB].

          (* prove main goal in subcases *)
          - eapply LetIn.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              { eauto. }
              { contradiction. }
              
            + fold Choreography.subst.
              destruct (Insn.rebound_in A x) eqn:Heq.
              {
                eauto.
              }
              {
                unfold Insn.rebound_in in Heq.
                specialize (HCSL
                              (nin_mapl DeltaA2 x y tau0 (nbeqeq A x y Heq) HninA)
                              (nin_remove_ce G A x A y HninG)).
                rewrite -> HCSL.
                eauto.
              }
              
            + auto.
              
            + auto.

            + auto.
        }
        (* case x not in e *)
        {
          pose proof (Expr.subst_not_in e x v
                        (ChorEnv.find A G) DeltaA1 ThetaA0 tau0
                        H3 HninG HninDA) as Hesubst.
          rewrite -> (add_find D A x tau) in H8.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H8 HninDA) as Hini.

          (* (de)construct environment for typing C *)
          pose proof (mapsto_destruct x tau DeltaA2 Hini) as HDA2.
          destruct HDA2 as [DeltaA2'].
          destruct H as [HDA2A HDA2B].

          (* partioning facts. *)
          rewrite -> (find_add A ThetaA2 T) in H9.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9) 
            as HPartition.                
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          
          (* prove main goal in subcases *)
          - eapply LetIn.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              {
                rewrite -> Hesubst.
                eauto.
              }
              { auto. }

            + fold Choreography.subst.
              destruct (Insn.rebound_in A x (Insn.Let A y e)) eqn:Heq.
              (* impossible case x = y *)
              {
                (* Note to ces: This case is provable constructively as follows, but instantiates
                   existential variables that falsify the hypotheses for subsequent case. *)
                (*
                  rewrite -> (addadd1 A D (Var.Map.add y tau0 DeltaA2) x tau) in H7.
                  rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H7.
                  eauto.
                 *)
                pose proof (beqeq A x y Heq).
                pose proof (map_in DeltaA2 x tau Hini).
                rewrite <- H in H10.
                contradiction.
              }
              (* case x <> y *)
              {
                (* prepare C typing. *)
                rewrite -> (addadd1 A D (Var.Map.add y tau0 DeltaA2) x tau) in H7.
                rewrite -> HDA2A in H7.
                rewrite -> (addadd6 x tau y tau0 DeltaA2') in H7.
                rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H7.
                
                               
                (* specialize and apply IH. *)
                specialize (IHC ThetaA1 ThetaA3 tau
                              (ChorEnv.remove A y G)
                              (Actor.Map.add A (Var.Map.add y tau0 DeltaA2') D)
                              (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T)
                              A x v Hv).
                
                unfold ChorEnv.add in IHC.
                rewrite -> (find_add A (Var.Map.add y tau0 DeltaA2') D) in IHC.
                rewrite -> (addadd2 A D (Var.Map.add x tau (Var.Map.add y tau0 DeltaA2'))) in IHC.
                rewrite -> (addadd2 A T ThetaA3 (Var.Map.concat ThetaA1 ThetaA3)) in IHC.
                specialize (IHC H7).

                unfold Insn.rebound_in in Heq.
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                specialize (IHC HPartitionB HninGy
                              (nin_mapl DeltaA2' x y tau0 (nbeqeq A x y Heq) HDA2B)).                

                eauto.

                apply (nbeqeq A x y Heq).
              }
              
            + pose proof (partition_remove (ChorEnv.find A D) DeltaA1 DeltaA2 x tau
                            H8 HninD HninDA).
              rewrite -> (remove_add x tau DeltaA2' DeltaA2 HDA2B HDA2A) in H.
              auto.

            + auto.

            + rewrite -> HDA2A in H10.
              pose proof (nin_mapr DeltaA2' y x tau (nin_nxeq DeltaA2' y x tau H10) H10).
              auto.
        }
      }
      (* Case A <> A' *)
      {
        - eapply LetIn.
          
          + destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. } 
            
          + fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.Let A' y e)) eqn:Heq.
            {
              unfold Insn.rebound_in in Heq.
              pose proof (beq A A' x y).
              destruct H.
              specialize (H Heq).
              destruct H.
              contradiction.
            }
            {
              (* prepare C typing *)
              rewrite -> (addadd3 D A x tau A' (Var.Map.add y tau0 DeltaA2) HCasesAeqA'R) in H7.
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H7.
              
              (* specialize and apply IH *)
              specialize (IHC ThetaA1 ThetaA2 tau (ChorEnv.remove A' y G)
                            (Actor.Map.add A' (Var.Map.add y tau0 DeltaA2) D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hv H7).
 
              rewrite -> (find_ab_neq2 A A' ThetaA3 T HCasesAeqA'R) in IHC.
              rewrite -> (find_ab_neq2 A A' (Var.Map.add y tau0 DeltaA2) D HCasesAeqA'R) in IHC.
              specialize (IHC HinT HninGy HninD).
              eauto.
            }

            + assert (A' <> A).
              auto.
              rewrite -> (find_ab_neq1 A' A x tau D H) in H8.
              auto.

            + assert (A' <> A).
              auto.
              rewrite -> (find_ab_neq2 A' A ThetaA2 T H) in H9.
              auto.

            + auto.
      }

    (* Case LetBang *)
    + inversion HC; subst.

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.

        rewrite -> (addadd1 A D DeltaA2 x tau) in H7.
        rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H7.
        
        assert (Var.Map.In x DeltaA1 \/ ~ Var.Map.In x DeltaA1) as HESL.
        tauto.

        (* Case x in e *) 
        destruct HESL as [HinDA | HninDA].   
        {          
          (* prepare witness for expression e typing and partioning facts. *)
          rewrite -> (add_find D A x tau) in H8.
          pose proof (inin (ChorEnv.find A D) DeltaA1 DeltaA2
                        x tau H8 HinDA) as Hinin.
          destruct (mapsto_destruct x tau DeltaA1 Hinin) as [DeltaA1' HDA'].
          destruct HDA' as [HDA'A HDA'B].
          rewrite -> HDA'A in H6.
          
          (* partioning facts. *)
          rewrite -> (find_add A ThetaA2 T) in H9.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          assert (H : Var.Map.Equal (Var.Map.add x tau DeltaA1') DeltaA1).
          { symmetry; auto. }
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau H H8 HninD HDA'B) as Hnin.
          destruct Hnin as [HninA HninB].
               
          eapply LetBang.
          
          + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
            {
            
              pose proof
                (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
                   (Var.Map.concat ThetaA1 ThetaA0) x v (Expr.BANG tau0)
                   Hv H6 HPartitionA HninG HDA'B) as HWTS.
              eauto.
            }
            {
              contradiction.
            }

          +  fold Choreography.subst.
             destruct (Insn.rebound_in A x) eqn:Heq.
             { eauto. }
             {
               pose proof (subst_not_in
                             C A x v
                             (ChorEnv.add A y tau0 G)
                             (Actor.Map.add A DeltaA2 D)
                             (Actor.Map.add A ThetaA3 T)
                             H7) as HCSL.
               rewrite -> (find_add A DeltaA2 D) in HCSL.
               specialize (HCSL HninA (find_nbeq G A x A y tau0 Heq HninG)).
               rewrite -> HCSL.
               eauto.
             }
             
          + auto.

          + auto.
        }
        (* case x not in e *)
        {
          pose proof (Expr.subst_not_in e x v 
                        (ChorEnv.find A G) DeltaA1 ThetaA0 (Expr.BANG tau0)
                        H6 HninG HninDA) as Hesubst.
          rewrite -> (add_find D A x tau) in H8.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H8 HninDA) as Hini.
          
          (* (de)construct environment for typing C *)
          pose proof (mapsto_destruct x tau DeltaA2 Hini) as HDA2.
          destruct HDA2 as [DeltaA2'].
          destruct H as [HDA2A HDA2B].
          
          (* partioning facts. *)
          rewrite -> (find_add A ThetaA2 T) in H9.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          
          (* prove main goal in subcases *)
          - eapply LetBang.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              {
                rewrite -> Hesubst.
                eauto.
              }
              { auto. }
              
            + fold Choreography.subst.
              (* impossible case due to env disjointness *)
              destruct (Insn.rebound_in A x (Insn.LetBang A y e)) eqn:Heq.
              {
                unfold Insn.rebound_in in Heq.
                pose proof (beqeq A x y Heq).
                rewrite <- H in *.

                pose proof (wt_disjoint C A (ChorEnv.add A x tau0 G) (Actor.Map.add A DeltaA2 D)
                              (Actor.Map.add A ThetaA3 T) H7) as Hwtdj.
                rewrite (find_add A DeltaA2 D) in Hwtdj.

                pose proof (nin_dj x (ChorEnv.find A (ChorEnv.add A x tau0 G)) DeltaA2
                              Hwtdj (map_in DeltaA2 x tau Hini)) as Hcontra1.
                pose proof (in_beq G A x tau0) as Hcontra2.
                contradiction.
              }
              {          
                rewrite -> HDA2A in H7.
                rewrite -> (addadd8 D A x tau DeltaA2') in H7.

                (* specialize and apply IH *)
                specialize (IHC ThetaA1 ThetaA3 tau
                              (ChorEnv.add A' y tau0 G)
                              (Actor.Map.add A DeltaA2' D)
                              (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T)
                              A x v
                              Hv).

                rewrite <- HCasesAeqA'L in IHC.
                rewrite -> (addadd2 A T ThetaA3 (Var.Map.concat ThetaA1 ThetaA3)) in IHC.
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                rewrite -> (find_add A DeltaA2' D) in IHC.
                pose proof (nin_nbeq_add1 G A x A y tau0 Heq HninG) as HninGy.
                
                specialize (IHC H7 HPartitionB HninGy HDA2B).

                eauto.
              }

            +  assert (Var.Map.Equal (Var.Map.add x tau DeltaA2') DeltaA2) as Hdel.
               { symmetry. auto. }
               pose proof (@Var.Map.Properties.Partition_sym _
                             (Var.Map.add x tau (ChorEnv.find A D)) DeltaA1 DeltaA2 H8) as Hpart.
               pose proof (nin
                             (ChorEnv.find A D) DeltaA2' DeltaA2 DeltaA1
                             x tau Hdel Hpart HninD HDA2B) as Hnin.
               destruct Hnin as [HninA HninB].
               pose proof (@Var.Map.Properties.Partition_sym _
                             (ChorEnv.find A D) DeltaA2' DeltaA1 HninB).
               auto.

            + auto.
        }
      }
      (* Case A <> A' *)
      {
        - eapply LetBang.
          
          + destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. } 
            
          + fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.LetBang A' y e)) eqn:Heq.
            {
              unfold Insn.rebound_in in Heq.
              pose proof (beq A A' x y).
              destruct H.
              specialize (H Heq).
              destruct H.
              contradiction.
            }
            {
              (* prepare C typing *)
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H7.
              rewrite -> (addadd3 D A x tau A' DeltaA2 HCasesAeqA'R) in H7.

              (* specialize and apply IH *)
              specialize (IHC ThetaA1 ThetaA2 tau
                            (ChorEnv.add A' y tau0 G)
                            (Actor.Map.add A' DeltaA2 D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hv H7).
              rewrite -> (find_ab_neq2 A A' ThetaA3 T HCasesAeqA'R) in IHC.
              rewrite -> (find_ab_neq2 A A' DeltaA2 D HCasesAeqA'R) in IHC.
              simpl in Heq.
              pose proof (find_nbeq G A x A' y tau0 Heq HninG) as HninG'.
              eapply (IHC HinT HninG' HninD).
            }

            + assert (A' <> A).
              auto.
              rewrite -> (find_ab_neq1 A' A x tau D H) in H8.
              auto.

            + assert (A' <> A).
              auto.
              rewrite -> (find_ab_neq2 A' A ThetaA2 T H) in H9.
              auto.
      }
      
      (* Case LetPair *)
    + inversion HC; subst.

      pose proof (nin_remove_ce G A x A' z HninG) as HninGz.
      pose proof (nin_remove_ce (ChorEnv.remove A' z G) A x A' y HninGz) as HninGzy.
      
      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.

        rewrite -> (addadd1 A D (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) x tau) in H5.
        rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H5.
        
        assert (Var.Map.In x DeltaA1 \/ ~ Var.Map.In x DeltaA1) as HESL.
        tauto.

        destruct HESL as [HinDA | HninDA].
        (* Case x in e *)
        {
          (* prepare witness for expression e typing and partioning facts. *)
          rewrite -> (add_find D A x tau) in H9.
          pose proof (inin (ChorEnv.find A D) DeltaA1 DeltaA2
                        x tau H9 HinDA) as Hinin.
          destruct (mapsto_destruct x tau DeltaA1 Hinin) as [DeltaA1' HDA'].
          destruct HDA' as [HDA'A HDA'B].
          rewrite -> HDA'A in H4.
          pose proof
            (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
               (Var.Map.concat ThetaA1 ThetaA0) x v (Expr.Tensor tau1 tau2) Hv H4) as HWTS.
          pose proof (find_add A ThetaA2 T) as HFA.
          rewrite -> HFA in H10.
          (* partioning facts. *)
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H10)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          (* e typing witness. *)
          specialize (HWTS HPartitionA HninG HDA'B).

          (* prepare hypotheses for partitioning requirements *)
          assert (Var.Map.Equal (Var.Map.add x tau DeltaA1') DeltaA1).
          { symmetry. auto. }
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau H H9 HninD HDA'B) as Hnin.
          pose proof (subst_not_in
                        C A x v
                        (ChorEnv.remove A y (ChorEnv.remove A z G))
                        (Actor.Map.add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                        (Actor.Map.add A ThetaA3 T)
                        H5) as HCSL.
          rewrite -> (find_add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D) in HCSL.
          destruct Hnin as [HninA HninB].

          (* prove main goal in subcases *)
          - eapply LetPair.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              { eauto. }
              { contradiction. }
              
            + fold Choreography.subst.
              destruct (Insn.rebound_in A x) eqn:Heq.
              {
                eauto.
              }
              {
                unfold Insn.rebound_in in Heq.

                (* NOTE: nice boolean eq rewrite Lemma from Bool.Bool *)
                rewrite orb_false_iff in Heq.
                destruct Heq as [HeqA HeqB].
                
                pose proof (nin_mapl DeltaA2 x z tau2 (nbeqeq A x z HeqB) HninA) as Hninz.
                specialize (HCSL (nin_mapl (Var.Map.add z tau2 DeltaA2)
                                    x y tau1 (nbeqeq A x y HeqA) Hninz) HninGzy).

                rewrite -> HCSL.
                eauto.
              }
              
            + auto.
              
            + auto.

            + auto.

            + auto.

            + auto.
        }
        (* case x not in e *)
        {
          pose proof (Expr.subst_not_in e x v
                        (ChorEnv.find A G) DeltaA1 ThetaA0 (Expr.Tensor tau1 tau2)
                        H4 HninG HninDA) as Hesubst.
          rewrite -> (add_find D A x tau) in H9.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H9 HninDA) as Hini.

          (* (de)construct environment for typing C *)
          pose proof (mapsto_destruct x tau DeltaA2 Hini) as HDA2.
          destruct HDA2 as [DeltaA2'].
          destruct H as [HDA2A HDA2B].

          (* partioning facts. *)
          rewrite -> (find_add A ThetaA2 T) in H10.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H10) 
            as HPartition.                
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          
          (* prove main goal in subcases *)
          - eapply LetPair.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              {
                rewrite -> Hesubst.
                eauto.
              }
              { auto. }

            + fold Choreography.subst.
              destruct (Insn.rebound_in A x (Insn.LetPair A y z e)) eqn:Heq.
              (* impossible case x = y *)
              {
                unfold Insn.rebound_in in Heq.

                (* NOTE: nice boolean eq rewrite Lemma from Bool.Bool *)
                rewrite orb_true_iff in Heq.
                destruct Heq as [HeqA | HeqB].
                {
                  pose proof (beqeq A x y HeqA).
                  rewrite <- H in *.
                  pose proof (map_in DeltaA2 x tau Hini).
                  contradiction.
                }
                {
                  pose proof (beqeq A x z HeqB).
                  pose proof (map_in DeltaA2 x tau Hini).
                  rewrite <- H in H12.
                  contradiction.
                }
              }
              (* case x <> y,z *)
              {
                unfold Insn.rebound_in in Heq.
                rewrite orb_false_iff in Heq.
                destruct Heq as [HeqA HeqB].
                pose proof (nbeqeq A x y HeqA).
                pose proof (nbeqeq A x z HeqB).
                
                (* prepare C typing. *)
                rewrite -> HDA2A in H5.                
                rewrite -> (addadd6 x tau z tau2 DeltaA2' H0) in H5.
                rewrite -> (addadd6 x tau y tau1 (Var.Map.add z tau2 DeltaA2') H) in H5.
                rewrite -> (addadd8 D A x tau (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2'))) in H5.

                specialize (IHC ThetaA1 ThetaA3 tau
                              (ChorEnv.remove A y (ChorEnv.remove A z G))
                              (Actor.Map.add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2')) D)
                              (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T)
                              A x v Hv).

                rewrite -> (addadd2 A T ThetaA3 (Var.Map.concat ThetaA1 ThetaA3)) in IHC.
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                rewrite -> (find_add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2')) D) in IHC.

               
                pose proof (nin_mapl DeltaA2' x z tau2 H0 HDA2B) as Hninz.
                pose proof (nin_mapl (Var.Map.add z tau2 DeltaA2') x y tau1 H Hninz) as Hniny.
                
                specialize (IHC H5 HPartitionB HninGzy Hniny).
                eauto.
              }

            + pose proof (partition_remove (ChorEnv.find A D) DeltaA1 DeltaA2 x tau
                            H9 HninD HninDA).
              rewrite -> (remove_add x tau DeltaA2' DeltaA2 HDA2B HDA2A) in H.
              auto.

            + auto.

            + rewrite -> HDA2A in H11.
              pose proof (nin_mapr DeltaA2' y x tau (nin_nxeq DeltaA2' y x tau H11) H11).
              auto.

            + rewrite -> HDA2A in H12.
              pose proof (nin_mapr DeltaA2' z x tau (nin_nxeq DeltaA2' z x tau H12) H12).
              auto.

            + auto.
        }
      }
      (* Case A <> A' *)
      {
        - eapply LetPair.

          + destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. } 

          + fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.LetPair A' y z e)) eqn:Heq.
            {
              unfold Insn.rebound_in in Heq.
              rewrite orb_true_iff in Heq.
              destruct Heq as [Heqxy | Heqxz].
              {
                pose proof (beq A A' x y).
                destruct H as [HA HB].
                specialize (HA Heqxy).
                destruct HA.
                contradiction.
              }
              {
                pose proof (beq A A' x z).
                destruct H as [HA HB].
                specialize (HA Heqxz).
                destruct HA.
                contradiction.
              }
            }
            { 
              (* prepare C typing *)
              rewrite -> (addadd3 D A x tau A'
                            (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) HCasesAeqA'R) in H5.
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H5.
              
              (* specialize and apply IH *)
              specialize (IHC ThetaA1 ThetaA2 tau (ChorEnv.remove A' y (ChorEnv.remove A' z G))
                            (Actor.Map.add A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hv H5).
 
              rewrite -> (find_ab_neq2 A A' ThetaA3 T HCasesAeqA'R) in IHC.
              rewrite -> (find_ab_neq2 A A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2))
                            D HCasesAeqA'R) in IHC.

              specialize (IHC HinT HninGzy HninD).
              eauto.
            }

          + assert (A' <> A).
            auto.
            rewrite -> (find_ab_neq1 A' A x tau D H) in H9.
            auto.
            
          + assert (A' <> A).
            auto.
            rewrite -> (find_ab_neq2 A' A ThetaA2 T H) in H10.
            auto.
            
          + auto.

          + auto.

          + auto.
      }
Qed.

Definition WellScoped (T : ChorEnv.t nat) (cfg : Config.t) : Prop :=
  forall A, Config.WellScoped (ChorEnv.find A T) cfg.

Lemma ws_partition : forall M M1 M2 cfg,
    Config.WellScoped M cfg ->
    Var.Map.Partition M M1 M2 ->
    Config.WellScoped M1 cfg.
Proof.
  intros M M1 M2 cfg [H H'] Hpart.
  split; auto.
  intros x Hin.
  apply H'.
  Var.Map.Tactics.reflect_partition.
  Var.simplify.
Qed.

Lemma ws_partition_env : forall A T ThetaA1 ThetaA2 cfg,
    WellScoped T cfg ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    WellScoped (Actor.Map.add A ThetaA1 T) cfg.
Proof.
  intros A T ThetaA1 ThetaA2 cfg Hws Hpart.
  intros B. ChorEnv.simplify.
  eapply ws_partition; eauto.
Qed.

Lemma bangty_inversion : forall Gamma Delta Theta e tau,
    Expr.WellTyped Gamma Delta Theta (Expr.Bang e) (Expr.BANG tau) ->
    Expr.WellTyped Gamma Delta Theta e tau /\
      Var.Map.Equal Delta (Var.Map.empty Expr.typ) /\
      Var.Map.Equal Theta (Var.Map.empty nat).
Proof.
  intros. 
  inversion H; subst.
  split; auto.
  split.
  Var.simplify.
  Var.simplify.
Qed.

Lemma qref_ty : forall Gamma Delta Theta q idx,
    Var.Map.Empty Delta ->
    Var.Map.Singleton q idx Theta ->
    Expr.WellTyped Gamma Delta Theta (Expr.QRef q) Expr.QUBIT.
Proof.
  intros.
  eapply Expr.WTQRef; eauto.
Qed.

Lemma fresh_empty : forall T,
  Var.fresh (Var.Map.empty T) = 0.
Proof.
  intros. unfold Var.fresh.
  rewrite Var.Map.Properties.fold_spec_right.
  simpl.
  auto.
Qed.

Lemma fresh_add : forall T (m : Var.Map.t T) x v,
  ~ Var.Map.In x m ->
  Var.fresh (Var.Map.add x v m) = max (x+1) (Var.fresh m).
Proof.
  intros.
  unfold Var.fresh.
  rewrite Var.Map.Properties.fold_add; auto.
  
  + fold (Var.fresh m).
    destruct (PeanoNat.Nat.leb (Var.fresh m) x) eqn:Hleb.
    - apply PeanoNat.Nat.leb_le in Hleb.
      rewrite max_l; auto.
      lia.

    - rewrite PeanoNat.Nat.leb_nle in Hleb.
      rewrite max_r; auto.
      lia.

  + clear m x v H.
    intros ? x ? ? ? ? ? z ?; subst; auto.
  + clear m x v H.
    intros z1 z2 v1 v2 w Hneq.
    repeat match goal with
    | [ H : context[PeanoNat.Nat.leb ?x ?y] |- _ ] =>
      let H := fresh "H" in
      destruct (PeanoNat.Nat.leb x y) eqn:H;
      try rewrite PeanoNat.Nat.leb_le in *;
      try rewrite PeanoNat.Nat.leb_nle in *
    | [ |- context[PeanoNat.Nat.leb ?x ?y] ] =>
      let H := fresh "H" in
      destruct (PeanoNat.Nat.leb x y) eqn:H;
      try rewrite PeanoNat.Nat.leb_le in *;
      try rewrite PeanoNat.Nat.leb_nle in *
    end;
    try lia.
Qed.

Lemma fresh_upper_bound : forall T (m : Var.Map.t T),
  forall x, Var.Map.In x m ->
    Var.fresh m > x.
Proof.
  intros T m.
  induction m using Var.Map.Properties.map_induction;
    intros y Hin.
  * Var.simplify.
  * Var.simplify.
  rewrite fresh_add; auto.
  destruct Hin; subst.
  { try lia. }
  apply IHm1 in H0. lia. 
Qed.

Lemma fresh_not_in : forall T (m : Var.Map.t T) x,
  x = Var.fresh m ->
  ~ Var.Map.In x m.
Proof.
  intros. subst.
  intros Hin.
  apply fresh_upper_bound in Hin.
  lia.
Qed.

Lemma step_weakening : forall C T1 cfg l C' T1' cfg' T2 T2' Theta A,
    step C T1 cfg l C' T1' cfg' ->
    Var.Map.Partition (ChorEnv.find A T2) Theta (ChorEnv.find A T1) ->
    Var.Map.Partition (ChorEnv.find A T2') Theta (ChorEnv.find A T1') ->
    step C T2 cfg l C' T2' cfg'.
Admitted.

Lemma epr_inversion : forall A B T1 cfg1 q1 q2 T2 cfg2,
    A <> B ->
    ChorEnv.epr A B T1 cfg1 = (q1, q2, T2, cfg2) ->
    WellScoped T1 cfg1 ->
    (exists idx1 idx2,
        Var.Map.Partition (ChorEnv.find A T2) (ChorEnv.find A T1)
	  (Var.Map.add q1 idx1 (Var.Map.empty _)) /\
        Var.Map.Partition (ChorEnv.find B T2) (ChorEnv.find B T1)
	  (Var.Map.add q2 idx2 (Var.Map.empty _))) /\
      ChorEnv.Equal T1
        (Actor.Map.add B (ChorEnv.find B T1) (
             Actor.Map.add A (ChorEnv.find A T1) T2)).
Proof.
  intros A B T1 cfg1 q1 q2 T2 cfg2 Heq Hepr HWS.
  unfold ChorEnv.epr in Hepr.
  destruct (Config.epr_cfg cfg1) as [[idx1 idx2] cfg'] eqn:Eqnepr.
  inversion Hepr; subst; clear Hepr.

  (*
  remember (Var.fresh (ChorEnv.find A T1)) as q1 eqn:Hq1.
  remember (Var.fresh (ChorEnv.find B (ChorEnv.add A q1 idx1 T1))) as q2 eqn:Hq2.
  *)

  split.
  2:{
    intros D.
    ChorEnv.simplify.
  }
  exists q1, q2.
  assert (~ Var.Map.In q1 (ChorEnv.find A T1)).
  {
    intros Hin.
    inversion Eqnepr; subst; clear Eqnepr.
    unfold WellScoped in HWS.
    apply (Config.wf_qrefs _ cfg1) in Hin; auto.
    lia.
  }
  assert (~ Var.Map.In q2 (ChorEnv.find B T1)).
  {
    intros Hin.
    inversion Eqnepr; subst; clear Eqnepr.
    unfold WellScoped in HWS.
    apply (Config.wf_qrefs _ cfg1) in Hin; auto.
    lia.
  }
  split.
  {
    ChorEnv.simplify.
    apply Var.Map.Proofs.partition_add_r; auto with var_db.
  }
  {
    ChorEnv.simplify.
    apply Var.Map.Proofs.partition_add_r; auto with var_db.
  }
Qed.
   
Lemma nilnostep : forall T cfg l C' T' cfg',
    ~ step [] T cfg l C' T' cfg'. 
Proof.
  intros.
  intros Habsurd.
  inversion Habsurd.
Qed.

Lemma epr_partition : forall T1 Theta2 A B T cfg q1 q2 T' cfg' D,
  ChorEnv.epr A B T cfg = (q1, q2, T', cfg') ->
  D <> A -> D <> B ->
  (Var.Map.Partition (ChorEnv.find D T) (ChorEnv.find D T1) Theta2) ->
  (forall D0, D0 <> D -> Var.Map.Equal (ChorEnv.find D0 T1) (ChorEnv.find D0 T)) ->
  exists T1', ChorEnv.epr A B T1 cfg = (q1, q2, T1', cfg') /\
              Var.Map.Partition (ChorEnv.find D T') (ChorEnv.find D T1') Theta2 /\
              (forall D0, D0 <> D -> Var.Map.Equal (ChorEnv.find D0 T1') (ChorEnv.find D0 T')).
Proof.
  intros T1 Theta2 A B T cfg q1 q2 T' cfg' D Hepr HA HB Hpart Heq.
  unfold ChorEnv.epr in Hepr.
  destruct (Config.epr_cfg cfg) as [[idx1 idx2] cfg0] eqn:Hcfg0.
  unfold ChorEnv.epr. rewrite Hcfg0.
  inversion Hepr; subst; clear Hepr.
  eexists.
  split; [reflexivity | ].
  split.
  + ChorEnv.simplify.
  + intros D0 ?.
    ChorEnv.simplify.
    { rewrite Heq; auto; try reflexivity. }
    { rewrite Heq; auto; try reflexivity. }
    { rewrite Heq; auto; try reflexivity. }
Qed.

Definition Step_partition_pairs (T1 T1' T2 T2' : ChorEnv.t nat) :=
  forall A Theta,
    Var.Map.Partition (ChorEnv.find A T1) (ChorEnv.find A T1') Theta ->
    Var.Map.Partition (ChorEnv.find A T2) (ChorEnv.find A T2') Theta.

Lemma spps_on : forall A Theta1 Theta2 (T1 T2 T3 : ChorEnv.t nat),
    Step_partition_pairs T1 (Actor.Map.add A Theta2 T1) T2 T3 ->
    Var.Map.Partition (ChorEnv.find A T1) Theta1 Theta2 ->
    ChorEnv.Equal T3 (Actor.Map.add A (ChorEnv.find A T3) T2) /\
      Var.Map.Partition (ChorEnv.find A T2) Theta1 (ChorEnv.find A T3).
Proof.
  intros.  
  unfold Step_partition_pairs in H.
  split.
  {
    unfold ChorEnv.Equal.
    intro.
    assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
    tauto.
    {
      rewrite <- HAeqA0 in *.
      rewrite find_add.
      Var.simplify.
    }
    {
      specialize (H A0 (Var.Map.empty _)).
      rewrite find_ab_neq2 in H; auto.
      rewrite find_ab_neq2; auto.
      assert (Var.Map.Partition (ChorEnv.find A0 T1) (ChorEnv.find A0 T1) (Var.Map.empty nat)).
      apply Var.Map.Proofs.partition_empty_r.
      specialize (H H1).
      apply Var.Map.Proofs.partition_empty2_eq in H.
      rewrite H.
      Var.simplify.
    }
  }
  {
    specialize (H A Theta1).
    rewrite find_add in H.
    specialize (H (@Var.Map.Properties.Partition_sym _ (ChorEnv.find A T1) Theta1 Theta2 H0)).
    pose proof (@Var.Map.Properties.Partition_sym _
                  (ChorEnv.find A T2) (ChorEnv.find A T3) Theta1 H).
    auto.
  }
Qed.

Definition Partition_except l (T1 T2 : ChorEnv.t nat) :=
  (forall A,
    ~ Actor.FSet.In A (Label.actors l) ->
    exists Theta,
      Var.Map.Partition (ChorEnv.find A T1) (ChorEnv.find A T2) Theta) /\
    (forall A,
      Actor.FSet.In A (Label.actors l) ->
      Var.Map.Equal (ChorEnv.find A T1) (ChorEnv.find A T2)).

(* Probably not needed *)
Lemma ws_partition_except : forall l (T1 T2 : ChorEnv.t nat) cfg,
    WellScoped T1 cfg ->
    Partition_except l T1 T2 ->
    WellScoped T2 cfg.
Proof.
  intros l T1 T2 cfg Hws [Hpart Heq] A.
  specialize (Hws A). destruct Hws as [Hwf Hws].
  split; auto.
  intros z Hz.

  (* If A is in actors(l) then we're done *)

  (* If not...then z is still in find A T1 *)
  apply Hws.
  destruct (Actor.Map.FSetProofs.in_dec A (Label.actors l)) as [Hin | Hin].
  + rewrite Heq; auto.
  + apply Hpart in Hin.
    destruct Hin as [Theta Hpart'].
    Var.Map.Tactics.reflect_partition.
    rewrite Heq0.
    Var.simplify.
Qed.


Lemma epr_part' : forall T1 A B T cfg q1 q2 T' cfg',
  ChorEnv.epr A B T cfg = (q1, q2, T', cfg') ->
  Partition_except (Label.EPR A B) T T1 ->
  WellScoped T cfg ->
  exists T1', ChorEnv.epr A B T1 cfg = (q1, q2, T1', cfg') /\
              Step_partition_pairs T T1 T' T1'.
Proof.
  intros T1 A B T cfg q1 q2 T' cfg' Hepr [Hpart Heq] HWS.
  unfold ChorEnv.epr in *.
  destruct (Config.epr_cfg cfg) as [[idx1 idx2] cfg0] eqn:Hcfg.
  inversion Hepr; subst; clear Hepr.
  exists (ChorEnv.add B q2 q2 (ChorEnv.add A q1 q1 T1)).
  split; auto.
  intros D ThetaD HpartD.
  assert (Hin1 : ~ Var.Map.In q1 ThetaD).
  {
    assert (Hin : ~ Var.Map.In q1 (ChorEnv.find D T)).
      {
        intros Hin.
        eapply Config.wf_qrefs in Hin; eauto.
        inversion Hcfg; subst; clear Hcfg.
        lia.
      }
      intros HinD.
      apply Hin.
      Var.Map.Tactics.reflect_partition.
      rewrite Heq0.
      Var.simplify.
  }
  assert (Hin2 : ~ Var.Map.In q2 ThetaD).
  {
    assert (Hin : ~ Var.Map.In q2 (ChorEnv.find D T)).
      {
        intros Hin.
        eapply Config.wf_qrefs in Hin; eauto.
        inversion Hcfg; subst; clear Hcfg.
        lia.
      }
      intros HinD.
      apply Hin.
      Var.Map.Tactics.reflect_partition.
      rewrite Heq0.
      Var.simplify.
  }
  ChorEnv.simplify.
  + (* A = D *)
    apply Var.Map.Proofs.partition_add_l; auto.
    apply Var.Map.Proofs.partition_add_l; auto.

  + (* B = D *)
    apply Var.Map.Proofs.partition_add_l; auto.
  
  + (* D <> A, D <> B *)
    apply Var.Map.Proofs.partition_add_l; auto.
Qed.


Lemma partition_functional_2 : forall T (M M1 M2 M2' : Var.Map.t T),
  Var.Map.Partition M M1 M2 -> Var.Map.Partition M M1 M2' ->
  Var.Map.Equal M2 M2'.
Proof.
  intros T M M1 M2 M2' Hpart Hpart'.
  Var.Map.Tactics.reflect_partition.
  Var.reflect_find.
  specialize (Heq z).
  Var.simplify.
  destruct (Var.Map.find z M1) as [v | ] eqn:H1; auto.
  destruct (Var.Map.find z M2) eqn:H2.
  {
    exfalso.
    apply (Hdisj0 z). split; Var.solve.
  }
  destruct (Var.Map.find z M2') eqn:H2'; auto.
  {
    exfalso.
    apply (Hdisj z). split; Var.solve.
  }
Qed.

Lemma delay_inversion : forall C1 T1 cfg1 l C2 T2 cfg2,
    step C1 T1 cfg1 l C2 T2 cfg2 ->
    WellScoped T1 cfg1 ->    
    forall G D T1',
      Partition_except l T1 T1' ->
      WellTyped G D T1' C1 ->
      exists T2',
        step C1 T1' cfg1 l C2 T2' cfg2 /\
          Step_partition_pairs T1 T1' T2 T2'.
Proof.
  intros C1 T1 cfg1 l C2 T2 cfg2 Hstep.
  induction Hstep.

  (* Case SendC *)
  - intros HWS G D T1' HPex HWT.

    inversion HWT; subst.

    unfold Partition_except in HPex.
    destruct HPex as [HPexA HPexB].
    
    exists (Actor.Map.add A TA' T1').
    split.
    {
      eapply SendC.
      {
        assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
        { unfold Label.actors; Actor.simplify. }          
        specialize (HPexB A HAinl).
        rewrite <- HPexB.
        eauto.
      }
      {
        assert (ChorEnv.Equal (Actor.Map.add A TA' T1') (Actor.Map.add A TA' T1')).
        Var.simplify.
        eauto.
      }
    }
    {
      unfold Step_partition_pairs.
      intros.
      rewrite H0.
      
      assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
      tauto.
      {
        assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
        { unfold Label.actors; Actor.simplify. }          
        specialize (HPexB A HAinl).   
        rewrite <- HAeqA0 in *.
        rewrite HPexB in H1.
        pose proof (partition_lopsided  (ChorEnv.find A T1') Theta H1) as Hpl. 
        rewrite find_add.
        rewrite find_add.
        rewrite Hpl.
        apply Var.Map.Proofs.partition_empty_r; auto.
      }
      {
        rewrite find_ab_neq2; auto.
        rewrite find_ab_neq2; auto.
      }
    }

  (* Case SendB *)
  - intros HWS G D T1' Hpart HWT.

    inversion HWT; subst.

    exists T1'.
    split.
    {
      apply SendB.
      { Var.simplify. }
      { Var.simplify. }
    }
    {
      unfold Step_partition_pairs.
      intros.
      rewrite H0 in H.
      auto.
    }
    
    - (* EPR *)
      intros HWS G D T1' Hpart HWT.
      inversion HWT; subst; clear HWT.

      (* T[A] = T1'[A] *)
      (* T[B] = T1'[B] *)
      (* for other D: T[D] = T1'[D],ThetaD *)

      edestruct (epr_part' T1') as [T1'' [Hepr' Hpart']]; eauto.

      exists T1''. split; auto.
      {
        econstructor; eauto.
        reflexivity.
      }
      {
        unfold Step_partition_pairs. intros.
        rewrite H0.
        apply Hpart'; auto.
      }


    - (* EPR' *)
      intros HWS G D T1' Hpart HWT.
      inversion HWT; subst; clear HWT.

      (* T[A] = T1'[A] *)
      (* T[B] = T1'[B] *)
      (* for other D: T[D] = T1'[D],ThetaD *)

      edestruct (epr_part' T1') as [T1'' [Hepr' Hpart']]; eauto.

      exists T1''. split; auto.
      {
        econstructor; eauto.
        reflexivity.
      }
      {
        unfold Step_partition_pairs. intros.
        rewrite H0.
        apply Hpart'; auto.
      }
      
    (* Case LetC *)
    - intros HWS G D T1' HPex HWT.
      
      inversion HWT; subst.

      unfold Partition_except in HPex.
      destruct HPex as [HPexA HPexB].
      
      exists (Actor.Map.add A TA' T1').
      split.
      {
        eapply LetC.
        {
          assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
          { unfold Label.actors; Actor.simplify. }          
          specialize (HPexB A HAinl).
          rewrite <- HPexB.
          eauto.
        }
        {
          assert (ChorEnv.Equal (Actor.Map.add A TA' T1') (Actor.Map.add A TA' T1')).
          Var.simplify.
          eauto.
        }
      }
      {
        unfold Step_partition_pairs.
        intros.
        rewrite H0.
        
        assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
        tauto.
        {
          assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
          { unfold Label.actors; Actor.simplify. }          
          specialize (HPexB A HAinl).   
          rewrite <- HAeqA0 in *.
          rewrite HPexB in H1.
          pose proof (partition_lopsided  (ChorEnv.find A T1') Theta H1) as Hpl. 
          rewrite find_add.
          rewrite find_add.
          rewrite Hpl.
          apply Var.Map.Proofs.partition_empty_r; auto.
        }
        {
          rewrite find_ab_neq2; auto.
          rewrite find_ab_neq2; auto.
        }
      }
      
    (* Case LetB *)
    - intros HWS G D T1' Hpart HWT.
      
      inversion HWT; subst.
      
      exists T1'.
      split.
      {
        apply LetB.
        { Var.simplify. }
        { Var.simplify. }
        { Var.simplify. }
      }
      {
        unfold Step_partition_pairs.
        intros.
        rewrite H1 in H0.
        auto.
      }
      
    (* Case LetBangC *)
    - intros HWS G D T1' HPex HWT.
      
      inversion HWT; subst.
      
      unfold Partition_except in HPex.
      destruct HPex as [HPexA HPexB].
      
      exists (Actor.Map.add A TA' T1').
      split.
      {
        eapply LetBangC.
        {
          assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
          { unfold Label.actors; Actor.simplify. }          
          specialize (HPexB A HAinl).
          rewrite <- HPexB.
          eauto.
        }
        {
          assert (ChorEnv.Equal (Actor.Map.add A TA' T1') (Actor.Map.add A TA' T1')).
          Var.simplify.
          eauto.
        }
      }
      {
        unfold Step_partition_pairs.
        intros.
        rewrite H0.
        
        assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
        tauto.
        {
          assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
          { unfold Label.actors; Actor.simplify. }          
          specialize (HPexB A HAinl).   
          rewrite <- HAeqA0 in *.
          rewrite HPexB in H1.
          pose proof (partition_lopsided  (ChorEnv.find A T1') Theta H1) as Hpl. 
          rewrite find_add.
          rewrite find_add.
          rewrite Hpl.
          apply Var.Map.Proofs.partition_empty_r; auto.
        }
        {
          rewrite find_ab_neq2; auto.
          rewrite find_ab_neq2; auto.
        }
      }
      
    (* Case LetBangB *)
    - intros HWS G D T1' Hpart HWT.
      
      inversion HWT; subst.
      
      exists T1'.
      split.
      {
        apply LetBangB.
        { Var.simplify. }
        { Var.simplify. }
      }
      {
        unfold Step_partition_pairs.
        intros.
        rewrite <- H0 in H.
        auto.
      }
    (* Case LetPairC *)
    - intros HWS G D T1' HPex HWT.
      
      inversion HWT; subst.
      
      unfold Partition_except in HPex.
      destruct HPex as [HPexA HPexB].
      
      exists (Actor.Map.add A TA' T1').
      split.
      {
        eapply LetPairC.
        {
          assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
          { unfold Label.actors; Actor.simplify. }          
          specialize (HPexB A HAinl).
          rewrite <- HPexB.
          eauto.
        }
        {
          assert (ChorEnv.Equal (Actor.Map.add A TA' T1') (Actor.Map.add A TA' T1')).
          Var.simplify.
          eauto.
        }
      }
      {
        unfold Step_partition_pairs.
        intros.
        rewrite H0.
        
        assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
        tauto.
        {
          assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
          { unfold Label.actors; Actor.simplify. }          
          specialize (HPexB A HAinl).   
          rewrite <- HAeqA0 in *.
          rewrite HPexB in H1.
          pose proof (partition_lopsided  (ChorEnv.find A T1') Theta H1) as Hpl. 
          rewrite find_add.
          rewrite find_add.
          rewrite Hpl.
          apply Var.Map.Proofs.partition_empty_r; auto.
        }
        {
          rewrite find_ab_neq2; auto.
          rewrite find_ab_neq2; auto.
        }
      }
      
    (* Case LetPairB *)
    - intros HWS G D T1' Hpart HWT.
      
      inversion HWT; subst.
      
      exists T1'.
      split.
      {
        apply LetPairB.
        { Var.simplify. }
        { Var.simplify. }
        { Var.simplify. }
        { Var.simplify. }
      }
      {
        unfold Step_partition_pairs.
        intros.
        rewrite <- H2 in H1.
        auto.
      }
      
    (* Case Delay *)
    - intros HWS G D T1' HPex HWT.
      
      inversion HWT; subst.
      
      + (* I = EPR *)
        apply IHHstep in H3; auto.
        destruct H3 as [T2' [IHstep IHpart]].
        eexists.
        split.
        { econstructor; eauto. }
        auto.

      + (* I = Send *)
        destruct HPex as [HPpart HPeq].

        assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
        { intros Hin. apply (H A). simpl. Actor.simplify. }
        apply HPpart in Hin.
        destruct Hin as [ThetaA HpartA].

        apply IHHstep in H4; auto.
        2:{
          split.
          {
            intros D0 HD0.
            apply HPpart in HD0.
            destruct HD0 as [ThetaD0 Hpart0].
            Actor.Map.Tactics.compare D0 A.
            {
              ChorEnv.simplify.
              assert (Heq : Var.Map.Equal (ChorEnv.find D0 T) (Var.Map.concat (Var.Map.concat ThetaA1 ThetaA2) ThetaD0)).
              {
                Var.Map.Tactics.reflect_partition. rewrite Heq. rewrite Heq1. reflexivity.
              }
              assert (Hdisj : Var.Map.Properties.Disjoint ThetaA1 ThetaD0).
              {
                Var.Map.Tactics.reflect_partition.
                rewrite Heq2 in *.
                Var.simplify.
              }

              
              exists (Var.Map.concat ThetaD0 ThetaA1).
              rewrite Heq.
              Var.Map.Tactics.reflect_partition;
                rewrite Heq2 in *;
                Var.simplify.
              {
                split; auto. apply Var.Map.Proofs.disjoint_sym; auto.
              }
              {
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- (Var.Map.Proofs.concat_assoc).
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaD0);
                  auto.
                reflexivity.
              }
            }
            { (* D0 <> A *)
              exists ThetaD0.
              ChorEnv.simplify.
            }
          }
          {
            intros D0 HD0.
            assert (D0 <> A).
            { inversion 1; subst. apply (H A). simpl. Actor.simplify. }
            ChorEnv.simplify.
          }
        }
        
        destruct H4 as [T2' [IHstep IHpart]].

        Var.Map.Tactics.reflect_partition.
        rewrite Heq0 in *.
        ChorEnv.simplify.

        
        eexists.
        split.
        { 
          econstructor; eauto.
          (* Know: C / (T1',A[ThetaA2]) -l-> C' / T2' *)
          (* A ∉ l *)
          (* WTS exists T2'', C / T1' -l-> C' / ??? *)
          (* Because A ∉ l, we know exists ThetaA, T[A] == T1'[A]+ThetaA *)

          (* step_weakening says that because
             T1'[A] == ThetaA1 ++ ThetaA2 == ThetaA1 ++ (T1',A[ThetaA2])[A],
             and C / (T1',A[ThetaA2]) -l-> C' / T2',
             then whenever ???[A] = ThetaA1 ++ T2'[A],
             then we can conclude that C / T1' -l-> C' / ???
          *)
          eapply step_weakening with (A := A)
                                     (T1 := Actor.Map.add A ThetaA2 T1')
                                     (T2' := Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
            eauto.
          { rewrite Heq0. ChorEnv.simplify.
            Var.Map.Tactics.reflect_partition; [ | reflexivity ]; auto.
          }
          {
            unfold Step_partition_pairs in IHpart.
            specialize (IHpart A).

            (* ALERT *)
            assert (Var.Map.Partition (ChorEnv.find A T') (ChorEnv.find A T2') (Var.Map.concat ThetaA ThetaA1)).
            {
              (* ALERT KEY!!! *)
              apply IHpart.
              ChorEnv.simplify.

              rewrite Heq.
              { (*associativity and symmetry *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }
            ChorEnv.simplify.
          }
        }
        { (* Step_partition_pairs *)
          intros D0 ThetaD0 HpartD0.
          unfold Step_partition_pairs in IHpart.
          Actor.Map.Tactics.compare D0 A.
          { (* D0 = A *)
            assert (HeqAD : Var.Map.Equal ThetaD0 ThetaA).
            {
              eapply partition_functional_2; eauto.
              rewrite Heq0 in *; Var.simplify.
            }
            rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.

            assert (HpartD0 : Var.Map.Partition (ChorEnv.find D0 T') (ChorEnv.find D0 T2')
                                (Var.Map.concat ThetaA1 ThetaA)).
            {
              apply IHpart.
              ChorEnv.simplify.
              rewrite Heq.
              { (* associativity and commutativity *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }

            ChorEnv.simplify.
            {
              rewrite Heq2.
              (*commutativity and associativity*)
                rewrite (Var.Map.Proofs.concat_sym); auto.
                2:{ Var.simplify. }
                repeat rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA); auto.
                2:{ auto with extra_var_db. }
                reflexivity.
            }
            
          }
          { (* D0 <> A *)
            ChorEnv.simplify.
            apply IHpart.
            ChorEnv.simplify.
          }

        }

      + (* I = LetBang *)
        assert (Actor.FSet.In A (Insn.actors (Insn.LetBang A x e))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.

        assert (Partition_except l T (Actor.Map.add A ThetaA2 T1')) as HPex'.
        {
          unfold Partition_except in HPex.
          destruct HPex as [HPexA HPexB].
          
          unfold Partition_except.
          split.
          {
            intros.
            assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
            tauto.
            {
              rewrite <- HAeqA0 in *.
              rewrite find_add; auto.

              destruct (HPexA A H0) as [Theta HPexAninl].

              exists (Var.Map.concat Theta ThetaA1).

              destruct
                (partitioning
                   (ChorEnv.find A T) ThetaA1 Theta (ChorEnv.find A T1') ThetaA2
                   (@Var.Map.Properties.Partition_sym _
                      (ChorEnv.find A T) (ChorEnv.find A T1') Theta HPexAninl)
                   H8) as [HPartA [HPartB [HPartC HPartD]]].

              apply
                (@Var.Map.Properties.Partition_sym _
                   (ChorEnv.find A T) (Var.Map.concat Theta ThetaA1) ThetaA2 HPartC).
            }
            {
              destruct (HPexA A0 H0) as [Theta HPexAninl].
              rewrite find_ab_neq2; eauto.
            }
          }
          {
            intros.
            specialize (HPexB A0 H0).
            pose proof (members_dj A0 A
                          (Label.actors l)
                          (Insn.actors (Insn.LetBang A x e)) H H0 HAinI).
            rewrite find_ab_neq2; auto.
          }
        }

        specialize (IHHstep HWS
                      (ChorEnv.add A x tau G)
                      (Actor.Map.add A DeltaA2 D)
                      (Actor.Map.add A ThetaA2 T1')
                      HPex' H3).

        destruct IHHstep as [T2 [IHHstepA IHHstepB]].

        pose proof IHHstepB as HSPP.
        pose proof IHHstepB as HSPP2.
        unfold Step_partition_pairs in IHHstepB.
        unfold Partition_except in HPex'.
        destruct HPex' as [HPex'A HPex'B].

        destruct (HPex'A A (inter_nin A (Label.actors l)
                              (Insn.actors (Insn.LetBang A x e)) H HAinI)) as [ThetaEx1 Hpart1].

        rewrite find_add in Hpart1.
        specialize (IHHstepB A ThetaEx1).
        rewrite find_add in IHHstepB.
        specialize (IHHstepB Hpart1).

        specialize (HSPP A ThetaEx1).
        rewrite find_add in HSPP.
        specialize (HSPP Hpart1).

        destruct HPex as [HPexA HPexB].
        specialize (HPexA A (inter_nin A (Label.actors l)
                               (Insn.actors (Insn.LetBang A x e)) H HAinI)) as [ThetaEx2 Hpart2].

        pose proof Hpart1 as HACCUMULATE.

        destruct (Var.Map.Proofs.partition_concat (ChorEnv.find A T) (ChorEnv.find A T1') ThetaEx2) as [Hpc2 _].
        destruct (Hpc2 Hpart2) as [Hdj2 Haccume2]; clear Hpc2.
        destruct (Var.Map.Proofs.partition_concat (ChorEnv.find A T1') ThetaA1 ThetaA2) as [Hpc3 _].
        destruct (Hpc3 H8) as [Hdj3 Haccume3]; clear Hpc3.

        rewrite Haccume3 in Haccume2.
        rewrite Haccume2 in HACCUMULATE.
        rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2 Hdj3) in HACCUMULATE.
        rewrite <- Var.Map.Proofs.concat_assoc in HACCUMULATE.
        rewrite Haccume3 in Hdj2.
                 
        pose proof
          (Var.Map.Proofs.disjoint_sym (Var.Map.concat ThetaA1 ThetaA2) ThetaEx2 Hdj2) as Hdj4.
        rewrite Var.Map.Proofs.concat_disjoint in Hdj4.
        destruct Hdj4 as [Hgoal1 Hgoal2].

        assert (Var.Map.Properties.Disjoint (Var.Map.concat ThetaA1 ThetaEx2) ThetaA2) as Hnomono1.
        {
          apply dj_concat_dj.
          apply (Var.Map.Proofs.disjoint_sym ThetaEx2 ThetaA1 Hgoal1).
          apply (Var.Map.Proofs.disjoint_sym ThetaEx2 ThetaA2 Hgoal2).
          auto.
        }

        pose proof (concat_partition ThetaA2 (Var.Map.concat ThetaA1 ThetaEx2)
                      (Var.Map.Proofs.disjoint_sym (Var.Map.concat ThetaA1 ThetaEx2)
                         ThetaA2 Hnomono1)) as Hnomono2.

        pose proof (partition_functional_2 nat
                      (Var.Map.concat ThetaA2 (Var.Map.concat ThetaA1 ThetaEx2))
                      ThetaA2 ThetaEx1 (Var.Map.concat ThetaA1 ThetaEx2)
                      HACCUMULATE Hnomono2) as Hnomono3.

        rewrite Hnomono3 in HSPP.
        
        destruct (Var.Map.Proofs.partition_concat
                    (ChorEnv.find A T') (ChorEnv.find A T2) (Var.Map.concat ThetaA1 ThetaEx2)) as [Hpc1 _].
        destruct (Hpc1 HSPP) as [Hdj1 Haccume1]; clear Hpc1.

        rewrite Var.Map.Proofs.concat_disjoint in Hdj1.
        destruct Hdj1 as [Hnomono4 _].
        apply Var.Map.Proofs.disjoint_sym in Hnomono4; auto.

        pose proof (concat_partition ThetaA1 (ChorEnv.find A T2) Hnomono4) as Hcrux.
        
        pose proof (step_weakening
                      C (Actor.Map.add A ThetaA2 T1') cfg l C' T2 cfg'
                      T1'
                      (Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2)) T2)
                      ThetaA1 A IHHstepA) as Hsw.

        
        rewrite find_add in Hsw; auto.
        rewrite find_add in Hsw; auto.

        specialize (Hsw H8 Hcrux).

        exists (Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2)) T2).
        split.
        {
          apply Delay.
          { auto. }
          { auto. }
        }
        {          
          unfold Step_partition_pairs.
          intros A0 ThetaEx0 Hspps.
          assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
          tauto.
          {
            rewrite <- HAeqA0 in *.
            rewrite find_add; auto.

            unfold Step_partition_pairs in HSPP2.

            specialize (HSPP2 A).

            assert (Var.Map.Partition
                      (ChorEnv.find A T)
                      (ChorEnv.find A (Actor.Map.add A ThetaA2 T1'))
                      (Var.Map.concat ThetaEx0 ThetaA1)) as Hcrux2.
            {
              rewrite find_add; auto.

              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A T) (ChorEnv.find A T1') ThetaEx0 Hspps) as Hspps_sym.

              pose proof (partitioning
                            (ChorEnv.find A T) ThetaA1 ThetaEx0 (ChorEnv.find A T1') ThetaA2
                            Hspps_sym H8) as [HpA [HpB [HpC HpD]]].

              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A T) (Var.Map.concat ThetaEx0 ThetaA1) ThetaA2
                            HpC) as HpC_sym.
              auto.
            }
            specialize (HSPP2 (Var.Map.concat ThetaEx0 ThetaA1) Hcrux2).
            rewrite find_add in Hcrux2.

            assert (Var.Map.Properties.Disjoint ThetaEx0 ThetaA1).
            {
              destruct (Var.Map.Proofs.partition_concat
                          (ChorEnv.find A T) (ChorEnv.find A T1') ThetaEx0) as [Hpc _].
              destruct (Hpc Hspps) as [HpcA _].
              pose proof (@Var.Map.Properties.Disjoint_sym _
                            (ChorEnv.find A T1') ThetaEx0 HpcA) as HpcA_sym.
              apply (partition_dj ThetaEx0 (ChorEnv.find A T1') ThetaA1 ThetaA2 HpcA_sym H8).
            }

            destruct (Var.Map.Proofs.partition_concat
                        (ChorEnv.find A T') (ChorEnv.find A T2)
                        (Var.Map.concat ThetaEx0 ThetaA1)) as [Hpc _].
            destruct (Hpc HSPP2) as [HpcA _].
            
            apply (partition_concat_assoc
                     (ChorEnv.find A T') (ChorEnv.find A T2)
                     ThetaEx0 ThetaA1 HpcA H0 HSPP2).
          }
          {
            rewrite find_ab_neq2; auto.
            unfold Step_partition_pairs in HSPP2.
            specialize (HSPP2 A0).
            rewrite find_ab_neq2 in HSPP2; auto.
          }
        }

      + (* I = Let *)
        destruct HPex as [HPpart HPeq].

        assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
        { intros Hin. apply (H A). simpl. Actor.simplify. }
        apply HPpart in Hin.
        destruct Hin as [ThetaA HpartA].

        apply IHHstep in H3; auto.
        2:{
          split.
          {
            intros D0 HD0.
            apply HPpart in HD0.
            destruct HD0 as [ThetaD0 Hpart0].
            Actor.Map.Tactics.compare D0 A.
            {
              ChorEnv.simplify.
              assert (Heq : Var.Map.Equal (ChorEnv.find D0 T) (Var.Map.concat (Var.Map.concat ThetaA1 ThetaA2) ThetaD0)).
              {
                Var.Map.Tactics.reflect_partition. rewrite Heq. rewrite Heq1. reflexivity.
              }
              assert (Hdisj : Var.Map.Properties.Disjoint ThetaA1 ThetaD0).
              {
                Var.Map.Tactics.reflect_partition.
                rewrite Heq2 in *.
                Var.simplify.
              }

              
              exists (Var.Map.concat ThetaD0 ThetaA1).
              rewrite Heq.
              Var.Map.Tactics.reflect_partition;
                rewrite Heq2 in *;
                Var.simplify.
              {
                split; auto. apply Var.Map.Proofs.disjoint_sym; auto.
              }
              {
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- (Var.Map.Proofs.concat_assoc).
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaD0);
                  auto.
                reflexivity.
              }
            }
            { (* D0 <> A *)
              exists ThetaD0.
              ChorEnv.simplify.
            }
          }
          {
            intros D0 HD0.
            assert (D0 <> A).
            { inversion 1; subst. apply (H A). simpl. Actor.simplify. }
            ChorEnv.simplify.
          }
        }
        
        destruct H3 as [T2' [IHstep IHpart]].

        Var.Map.Tactics.reflect_partition.
        rewrite Heq0 in *.
        ChorEnv.simplify.

        
        eexists.
        split.
        { 
          econstructor; eauto.
          (* Know: C / (T1',A[ThetaA2]) -l-> C' / T2' *)
          (* A ∉ l *)
          (* WTS exists T2'', C / T1' -l-> C' / ??? *)
          (* Because A ∉ l, we know exists ThetaA, T[A] == T1'[A]+ThetaA *)

          (* step_weakening says that because
             T1'[A] == ThetaA1 ++ ThetaA2 == ThetaA1 ++ (T1',A[ThetaA2])[A],
             and C / (T1',A[ThetaA2]) -l-> C' / T2',
             then whenever ???[A] = ThetaA1 ++ T2'[A],
             then we can conclude that C / T1' -l-> C' / ???
          *)
          eapply step_weakening with (A := A)
                                     (T1 := Actor.Map.add A ThetaA2 T1')
                                     (T2' := Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
            eauto.
          { rewrite Heq0. ChorEnv.simplify.
            Var.Map.Tactics.reflect_partition; [ | reflexivity ]; auto.
          }
          {
            unfold Step_partition_pairs in IHpart.
            specialize (IHpart A).

            (* ALERT *)
            assert (Var.Map.Partition (ChorEnv.find A T') (ChorEnv.find A T2') (Var.Map.concat ThetaA ThetaA1)).
            {
              (* ALERT KEY!!! *)
              apply IHpart.
              ChorEnv.simplify.

              rewrite Heq.
              { (*associativity and symmetry *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }
            ChorEnv.simplify.
          }
        }
        { (* Step_partition_pairs *)
          intros D0 ThetaD0 HpartD0.
          unfold Step_partition_pairs in IHpart.
          Actor.Map.Tactics.compare D0 A.
          { (* D0 = A *)
            assert (HeqAD : Var.Map.Equal ThetaD0 ThetaA).
            {
              eapply partition_functional_2; eauto.
              rewrite Heq0 in *; Var.simplify.
            }
            rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.

            assert (HpartD0 : Var.Map.Partition
                                (ChorEnv.find D0 T') (ChorEnv.find D0 T2') (Var.Map.concat ThetaA1 ThetaA)).
            {
              apply IHpart.
              ChorEnv.simplify.
              rewrite Heq.
              { (* associativity and commutativity *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }

            ChorEnv.simplify.
            {
              rewrite Heq2.
              (*commutativity and associativity*)
                rewrite (Var.Map.Proofs.concat_sym); auto.
                2:{ Var.simplify. }
                repeat rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA); auto.
                2:{ auto with extra_var_db. }
                reflexivity.
            }
            
          }
          { (* D0 <> A *)
            ChorEnv.simplify.
            apply IHpart.
            ChorEnv.simplify.
          }

        }

      + (* I = LetPair *)
        destruct HPex as [HPpart HPeq].

        assert (Hin : ~ Actor.FSet.In A (Label.actors l)).
        { intros Hin. apply (H A). simpl. Actor.simplify. }
        apply HPpart in Hin.
        destruct Hin as [ThetaA HpartA].

        apply IHHstep in H3; auto.
        2:{
          split.
          {
            intros D0 HD0.
            apply HPpart in HD0.
            destruct HD0 as [ThetaD0 Hpart0].
            Actor.Map.Tactics.compare D0 A.
            {
              ChorEnv.simplify.
              assert (Heq : Var.Map.Equal (ChorEnv.find D0 T) (Var.Map.concat (Var.Map.concat ThetaA1 ThetaA2) ThetaD0)).
              {
                Var.Map.Tactics.reflect_partition. rewrite Heq. rewrite Heq1. reflexivity.
              }
              assert (Hdisj : Var.Map.Properties.Disjoint ThetaA1 ThetaD0).
              {
                Var.Map.Tactics.reflect_partition.
                rewrite Heq2 in *.
                Var.simplify.
              }

              
              exists (Var.Map.concat ThetaD0 ThetaA1).
              rewrite Heq.
              Var.Map.Tactics.reflect_partition;
                rewrite Heq2 in *;
                Var.simplify.
              {
                split; auto. apply Var.Map.Proofs.disjoint_sym; auto.
              }
              {
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- (Var.Map.Proofs.concat_assoc).
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaD0);
                  auto.
                reflexivity.
              }
            }
            { (* D0 <> A *)
              exists ThetaD0.
              ChorEnv.simplify.
            }
          }
          {
            intros D0 HD0.
            assert (D0 <> A).
            { inversion 1; subst. apply (H A). simpl. Actor.simplify. }
            ChorEnv.simplify.
          }
        }
        
        destruct H3 as [T2' [IHstep IHpart]].

        Var.Map.Tactics.reflect_partition.
        rewrite Heq0 in *.
        ChorEnv.simplify.

        
        eexists.
        split.
        { 
          econstructor; eauto.
          (* Know: C / (T1',A[ThetaA2]) -l-> C' / T2' *)
          (* A ∉ l *)
          (* WTS exists T2'', C / T1' -l-> C' / ??? *)
          (* Because A ∉ l, we know exists ThetaA, T[A] == T1'[A]+ThetaA *)

          (* step_weakening says that because
             T1'[A] == ThetaA1 ++ ThetaA2 == ThetaA1 ++ (T1',A[ThetaA2])[A],
             and C / (T1',A[ThetaA2]) -l-> C' / T2',
             then whenever ???[A] = ThetaA1 ++ T2'[A],
             then we can conclude that C / T1' -l-> C' / ???
          *)
          eapply step_weakening with (A := A)
                                     (T1 := Actor.Map.add A ThetaA2 T1')
                                     (T2' := Actor.Map.add A (Var.Map.concat ThetaA1 (ChorEnv.find A T2')) T2');
            eauto.
          { rewrite Heq0. ChorEnv.simplify.
            Var.Map.Tactics.reflect_partition; [ | reflexivity ]; auto.
          }
          {
            unfold Step_partition_pairs in IHpart.
            specialize (IHpart A).

            (* ALERT *)
            assert (Var.Map.Partition (ChorEnv.find A T') (ChorEnv.find A T2') (Var.Map.concat ThetaA ThetaA1)).
            {
              (* ALERT KEY!!! *)
              apply IHpart.
              ChorEnv.simplify.

              rewrite Heq.
              { (*associativity and symmetry *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }
            ChorEnv.simplify.
          }
        }
        { (* Step_partition_pairs *)
          intros D0 ThetaD0 HpartD0.
          unfold Step_partition_pairs in IHpart.
          Actor.Map.Tactics.compare D0 A.
          { (* D0 = A *)
            assert (HeqAD : Var.Map.Equal ThetaD0 ThetaA).
            {
              eapply partition_functional_2; eauto.
              rewrite Heq0 in *; Var.simplify.
            }
            rewrite HeqAD in *; clear ThetaD0 HeqAD HpartD0.

            assert (HpartD0 : Var.Map.Partition
                                (ChorEnv.find D0 T') (ChorEnv.find D0 T2') (Var.Map.concat ThetaA1 ThetaA)).
            {
              apply IHpart.
              ChorEnv.simplify.
              rewrite Heq.
              { (* associativity and commutativity *)
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA2); auto.
                rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA1 ThetaA); auto.
                reflexivity.
              }
            }

            ChorEnv.simplify.
            {
              rewrite Heq2.
              (*commutativity and associativity*)
                rewrite (Var.Map.Proofs.concat_sym); auto.
                2:{ Var.simplify. }
                repeat rewrite <- Var.Map.Proofs.concat_assoc.
                rewrite (Var.Map.Proofs.concat_sym ThetaA); auto.
                2:{ auto with extra_var_db. }
                reflexivity.
            }
            
          }
          { (* D0 <> A *)
            ChorEnv.simplify.
            apply IHpart.
            ChorEnv.simplify.
          }
        }
Qed.

(* Defined this helper function Partition_on to mean that find A T == find A T1 ++ ThetaA2 
  and for all other B <> A, find B T = find B T1
*)
Definition Partition_on {X} A (T T1 : ChorEnv.t X) ThetaA2 :=
  Var.Map.Partition (ChorEnv.find A T) (ChorEnv.find A T1) ThetaA2 
  /\
  forall B, A <> B -> Var.Map.Equal (ChorEnv.find B T1) (ChorEnv.find B T).

Lemma step_inversion' : forall C1 T1 cfg1 l C2 T2 cfg2,
    step C1 T1 cfg1 l C2 T2 cfg2 ->
    WellScoped T1 cfg1 ->
    forall G D T1' A0 Theta,
      ~ Actor.FSet.In A0 (Label.actors l) ->
      WellTyped G D T1' C1 ->
      Partition_on A0 T1 T1' Theta ->
      exists T2',
        step C1 T1' cfg1 l C2 T2' cfg2 /\
          Partition_on A0 T2 T2' Theta.

Proof.
  intros C T cfg l C' T' cfg' Hstep.
  induction Hstep; intros HWS Gamma Delta T1 A0 Theta Hnin HWT [Hpart HT1];
    simpl in Hnin; Actor.simplify. 
  * (* SendC *)
    setoid_replace (ChorEnv.find A T) with (ChorEnv.find A T1) in H.
    2:{
      rewrite <- HT1; auto.
      reflexivity.
    }
    eexists. split.
    { econstructor; eauto. reflexivity. }
    split.
    {
      rewrite H0.
      ChorEnv.simplify.
    }
    {
      intros B0 HB0.
      rewrite H0.
      ChorEnv.simplify.
    }

  * (* SendB *) 
    eexists. split.
    { econstructor; eauto. reflexivity. }
    split.
    { rewrite <- H0. auto. }
    intros B0 HB0.
    rewrite <- H0.
    apply HT1; auto.

  * (* epr *) 
    eapply epr_partition in H; eauto.
    destruct H as [T1' [Hepr [Hpart' Heq']]].
    eexists.
    split.
    {
      econstructor; eauto. reflexivity.
    }
    split; auto.
    { rewrite H0; auto. }
    {
      intros.
      rewrite H0; auto.
    }

  * (* epr' *) 
    eapply epr_partition in H; eauto.
    destruct H as [T1' [Hepr [Hpart' Heq']]].
    eexists.
    split.
    {
      econstructor; eauto. reflexivity.
    }
    split; auto.
    { rewrite H0; auto. }
    { intros. rewrite H0; auto. }

  * (*LetC*)
    eexists. split.
    {
      econstructor; eauto. 2:{ reflexivity. }
      rewrite HT1; eauto.
    }
    split; intros; rewrite H0; ChorEnv.simplify.

  * (*LetB*)
    
    eexists. split.
    { econstructor; eauto. reflexivity. }
    split; intros; rewrite <- H1; auto.

  * (*LetBangC*) 
    eexists. split.
    {
      econstructor; eauto. 2:{ reflexivity. }
      rewrite HT1; eauto.
    }
    split; intros; rewrite H0; ChorEnv.simplify.

  * (*LetBangB*)
    
    eexists. split.
    { econstructor; eauto. reflexivity. }
    split; intros; rewrite H0; auto.

  * (*LetPairC*) 
    eexists. split.
    {
      econstructor; eauto. 2:{ reflexivity. }
      rewrite HT1; eauto.
    }
    split; intros; rewrite H0; ChorEnv.simplify.

  * (*LetPairB*)
    eexists. split.
    { econstructor; eauto. reflexivity. }
    split; intros; rewrite H2; auto.

  * (* Delay *)

    (* Cases on the typing judgment of I::C*)
    inversion HWT; subst; clear HWT.
    + (* I = EPR *) admit.
    + (* I = Send *) admit.

    + (* I = LetBang *) 
      assert (~ Actor.FSet.In A (Label.actors l)).
      { intros Hin. apply (H A). simpl. Actor.simplify. }

      (* Step weakening lemma here... *)

      specialize (IHHstep HWS
                    (ChorEnv.add A x tau Gamma)
                    (Actor.Map.add A DeltaA2 Delta)
                    (Actor.Map.add A ThetaA2 T1)
                    A
                    (ChorEnv.find A (Actor.Map.add A0
                                       (Var.Map.concat Theta ThetaA1)
                                       (Actor.Map.add A ThetaA1 T)))
                    H0 H3).

      assert (Partition_on A T (Actor.Map.add A ThetaA2 T1)
                (ChorEnv.find A (Actor.Map.add A0
                                   (Var.Map.concat Theta ThetaA1)
                                   (Actor.Map.add A ThetaA1 T)))) as Hpo.
      {
        unfold Partition_on.
        split.
        {
          assert (A0 <> A \/ A0 = A) as [AneqA0 | AeqA0].
          tauto.
          {
            rewrite find_add; auto.
            rewrite find_ab_neq2; auto.
            specialize (HT1 A AneqA0).
            rewrite <- HT1.
            rewrite find_add; auto.
            apply @Var.Map.Properties.Partition_sym; auto.  
          }
          {
            rewrite AeqA0 in *.
            rewrite find_add; auto.
            rewrite find_add; auto.
            destruct (partitioning
                          (ChorEnv.find A T) ThetaA1 Theta (ChorEnv.find A T1) ThetaA2
                          (@Var.Map.Properties.Partition_sym _
                             (ChorEnv.find A T) (ChorEnv.find A T1) Theta Hpart) H8) as [_ [_ [Hpart2 _]]].
            apply (@Var.Map.Properties.Partition_sym _
                     (ChorEnv.find A T) (Var.Map.concat Theta ThetaA1) ThetaA2 Hpart2).
          }
        }
        {
          intros.
          rewrite find_ab_neq2; auto.
          specialize (HT1 B).
          admit.
        }
      }
      
      
      admit.

    + (* I = Let *) admit.
    + (* I = LetPair *) admit.
    
Admitted.

Lemma step_inversion : forall C1 T1 cfg1 l C2 T2 cfg2,
    step C1 T1 cfg1 l C2 T2 cfg2 ->
    WellScoped T1 cfg1 ->
    forall G D T1' A Theta,
      ~ Actor.FSet.In A (Label.actors l) ->
      WellTyped G D T1' C1 ->
      Var.Map.Partition (ChorEnv.find A T1) (ChorEnv.find A T1') Theta ->
      ChorEnv.Equal (Actor.Map.add A (ChorEnv.find A T1) T1') T1 ->
      exists T2',
        step C1 T1' cfg1 l C2 T2' cfg2 /\
          Var.Map.Partition (ChorEnv.find A T2) (ChorEnv.find A T2') Theta /\
          ChorEnv.Equal (Actor.Map.add A (ChorEnv.find A T2') T2) T2'.
Proof.
  intros ? ? ? ? ? ? ? Hstep HWS G D T1' A Theta Hnin HWT Hpart Heq.
  eapply step_inversion' in Hstep; eauto.
  2:{ split; eauto. intros. rewrite <- Heq. ChorEnv.simplify. }
  destruct Hstep as [T2' [Hstep [Hpart' Heq']]].
  exists T2'. split; auto.
  split; auto.
  { intros B. ChorEnv.simplify.
    symmetry. apply Heq'; auto.
  }
Qed.

Theorem preservation : forall G D T1 C1,
    WellTyped G D T1 C1 ->
    forall cfg1 l C2 T2 cfg2, 
      step C1 T1 cfg1 l C2 T2 cfg2 ->
      WellScoped T1 cfg1 ->
        (forall A, Actor.FSet.In A (Label.actors l) ->
                   Var.Map.Empty (ChorEnv.find A G) /\  Var.Map.Empty (ChorEnv.find A D)) ->   
        WellTyped G D T2 C2.
Proof.
  intros G D T1 C1 HWT.
  induction HWT.

  (* Case Nil *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.
    apply nilnostep in HStep.
    contradiction.

  (* Case EPR *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case EPRB *) 
    + assert (Actor.FSet.In A (Label.actors (Label.EPR A B))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      assert (Actor.FSet.In B (Label.actors (Label.EPR A B))) as HBinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      destruct (Hemptiness B HBinl) as [HBGempty HBDempty].
      
      destruct (epr_inversion A B T cfg1 q1 q2 T0 cfg2 H H13 Hscoped) as [HeprA HeprB].
      destruct HeprA as [idx1 [idx2]].
      destruct H2 as [HeprAA HeprAB].
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q1 idx1 (Var.Map.empty _))
                    q1 idx1 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q1 idx1)) as Hq1ty.
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q2 idx2 (Var.Map.empty _))
                    q2 idx2 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q2 idx2)) as Hq2ty.
      
      rewrite rem_empty2 in HWT; auto.
      rewrite rem_empty2 in HWT; auto.
      rewrite HeprB in HWT.
      
      pose proof (wt_subst_lin
                    C
                    (Var.Map.add q2 idx2 (Var.Map.empty nat))
                    (ChorEnv.find B T)
                    Expr.QUBIT
                    G
                    (ChorEnv.add A x Expr.QUBIT D)
                    (Actor.Map.add A (ChorEnv.find A T) T0)
                    B y
                    (Expr.QRef q2)
                    Hq2ty HWT) as HwtCAx.
      
      rewrite find_ab_neq1 in HwtCAx; auto.
      rewrite find_ab_neq2 in HwtCAx; auto.
      
      assert (~ Var.Map.In x (ChorEnv.find A G)) as HxninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      assert (~ Var.Map.In y (ChorEnv.find B G)) as HyninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find B G) HBGempty).
      Var.simplify.
      
      specialize (HwtCAx
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find B T0)
                       (ChorEnv.find B T)
                       (Var.Map.add q2 idx2 (Var.Map.empty nat))
                       HeprAB)
                    HyninG H1).
      
      pose proof (wt_subst_lin
                    (Choreography.subst B y (Expr.QRef q2) C)
                    (Var.Map.add q1 idx1 (Var.Map.empty nat))
                    (ChorEnv.find A T)
                    Expr.QUBIT
                    G
                    D
                    T0
                    A x
                    (Expr.QRef q1)
                    Hq1ty HwtCAx) as HwtCBy.
      
      rewrite H14.
      apply (HwtCBy
               (@Var.Map.Properties.Partition_sym _
                  (ChorEnv.find A T0)
                  (ChorEnv.find A T)
                  (Var.Map.add q1 idx1 (Var.Map.empty nat))
                  HeprAA)
               HxninG H0).
      
      rewrite find_ab_neq3; auto.

    (* Case EPRB' *) 
    + assert (Actor.FSet.In A (Label.actors (Label.EPR B A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      assert (Actor.FSet.In B (Label.actors (Label.EPR B A))) as HBinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      destruct (Hemptiness B HBinl) as [HBGempty HBDempty].

      assert (B <> A) as HBneA; auto.
      destruct (epr_inversion B A T cfg1 q2 q1 T0 cfg2 HBneA H13 Hscoped) as [HeprA HeprB].
      destruct HeprA as [idx1 [idx2]].
      destruct H2 as [HeprAA HeprAB].
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q1 idx2 (Var.Map.empty _))
                    q1 idx2 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q1 idx2)) as Hq1ty.
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q2 idx1 (Var.Map.empty _))
                    q2 idx1 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q2 idx1)) as Hq2ty.
      
      rewrite rem_empty2 in HWT; auto.
      rewrite rem_empty2 in HWT; auto.
      rewrite HeprB in HWT.
      rewrite addadd4 in HWT; auto.
      
      pose proof (wt_subst_lin
                    C
                    (Var.Map.add q2 idx1 (Var.Map.empty nat))
                    (ChorEnv.find B T)
                    Expr.QUBIT
                    G
                    (ChorEnv.add A x Expr.QUBIT D)
                    (Actor.Map.add A (ChorEnv.find A T) T0)
                    B y
                    (Expr.QRef q2)
                    Hq2ty HWT) as HwtCBy.
      
      rewrite find_ab_neq1 in HwtCBy; auto.
      rewrite find_ab_neq2 in HwtCBy; auto.
      
      assert (~ Var.Map.In x (ChorEnv.find A G)) as HxninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      assert (~ Var.Map.In y (ChorEnv.find B G)) as HyninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find B G) HBGempty).
      Var.simplify.
      
      specialize (HwtCBy
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find B T0)
                       (ChorEnv.find B T)
                       (Var.Map.add q2 idx1 (Var.Map.empty nat))
                       HeprAA)
                    HyninG H1).
      
      pose proof (wt_subst_lin
                    (Choreography.subst B y (Expr.QRef q2) C)
                    (Var.Map.add q1 idx2 (Var.Map.empty nat))
                    (ChorEnv.find A T)
                    Expr.QUBIT
                    G
                    D
                    T0
                    A x
                    (Expr.QRef q1)
                    Hq1ty HwtCBy) as HwtCAx.
      
      rewrite H14.
      apply (HwtCAx
               (@Var.Map.Properties.Partition_sym _
                  (ChorEnv.find A T0)
                  (ChorEnv.find A T)
                  (Var.Map.add q1 idx2 (Var.Map.empty nat))
                  HeprAB)
               HxninG H0).
      
      rewrite find_ab_neq3; auto.

    (* Case Delay/EPR *) 
    + assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (ChorEnv.find A0 (ChorEnv.remove B y (ChorEnv.remove A x G))) /\
                   Var.Map.Empty (ChorEnv.find A0
                                    (ChorEnv.add B y Expr.QUBIT (ChorEnv.add A x Expr.QUBIT D)))) as Hih.
      {
        intros A0 HA0inl.
        
        assert (Actor.FSet.In A (Insn.actors (Insn.EPR A x B y))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        assert (Actor.FSet.In B (Insn.actors (Insn.EPR A x B y))) as HBinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.EPR A x B y))
                      H11 HA0inl HAinI).
        
        pose proof (members_dj A0 B
                      (Label.actors l)
                      (Insn.actors (Insn.EPR A x B y))
                      H11 HA0inl HBinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        {
          rewrite find_ab_neq3; auto.
          rewrite find_ab_neq3; auto.
        }
        {
          rewrite find_ab_neq1; auto.
          rewrite find_ab_neq1; auto.                    
        }
      }

      specialize (IHHWT cfg1 l C' T2 cfg2 H4 Hscoped Hih).

      apply EPR.
      { auto. }
      { auto. }
      { auto. }
      { auto. }

  (* Case Send *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.
   
    (* Case SendC *)
    + unfold  WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in H1.
      
      assert (Var.Map.Empty (Var.Map.M.empty Expr.typ)) as Hee.
      Var.simplify.
      
      pose proof (empty_partition (Var.Map.M.empty Expr.typ) DeltaA1 DeltaA2 Hee H1) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H0.
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H0.
      

      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H14
                    ThetaA1 ThetaA2 (Expr.BANG tau) Hscoped H0 H2) as Hsi.
      
      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].
      
      eapply Send.
      { auto. }
      { 
        eapply Expr.WellTyped_preservation.
        { rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty); eauto. }
        { rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty); Var.simplify. }
        { Var.simplify. }
        { apply (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H2). }
        { eauto. }
      }
      {
        rewrite H15.
        rewrite addadd2.
        eauto.
      }
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty).
        rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H1.
        auto.
      }
      {
        rewrite H15.
        rewrite find_add; auto.
      }
   
    (* Case SendB *)
    + rewrite <- H15 in *.

      assert (Actor.FSet.In A (Label.actors (Label.Send A v B))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      assert (Actor.FSet.In B (Label.actors (Label.Send A v B))) as HBinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      destruct (Hemptiness B HBinl) as [HBGempty HBDempty].
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H0.
      destruct (bangty_inversion (Var.Map.empty Expr.typ) DeltaA1 ThetaA1 v tau H0)
        as [HbangA [HbangB HbangC]].
      rewrite HbangB in *.
      rewrite HbangC in *.

      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in H1.
      pose proof (@Var.Map.Properties.Partition_sym _
                    (Var.Map.empty Expr.typ) (Var.Map.empty Expr.typ) DeltaA2 H1) as Hpart.
      pose proof (empty_partition
                    (Var.Map.empty Expr.typ) DeltaA2 (Var.Map.empty Expr.typ)
                    empty_map_empty Hpart) as Hep.
      eapply wt_subst_bang; eauto.
      
      rewrite <- (lopsided_partition (ChorEnv.find A T) ThetaA2 H2) in HWT.
      rewrite find_add_env in HWT; auto.
      rewrite empty_to_empty in HWT; auto.
   
    (* Case Delay/Send *)
    + assert (Var.Map.Partition (ChorEnv.find A T)
                (ChorEnv.find A (Actor.Map.add A ThetaA2 T)) ThetaA1) as Hsipart.
      {
        rewrite find_add; auto.
        apply @Var.Map.Properties.Partition_sym; auto.
      }
                        
      assert (ChorEnv.Equal
                (Actor.Map.add A (ChorEnv.find A T) (Actor.Map.add A ThetaA2 T)) T) as Hsieq.
      {
        rewrite addadd2; auto.
        rewrite find_add_env; auto.
        ChorEnv.simplify.
      }
      
      assert (Hnin : ~ Actor.FSet.In A (Label.actors l)).
      { simpl in H12. specialize (H12 A). Actor.simplify. }

      pose proof (step_inversion
                    C T cfg1 l C' T2 cfg2 H5 Hscoped
                    (ChorEnv.add B y tau G)
                    (Actor.Map.add A DeltaA2 D)
                    (Actor.Map.add A ThetaA2 T)
                    A ThetaA1 Hnin HWT Hsipart Hsieq) as Hsi.
      
      destruct Hsi as [Theta0 Hsi].
      destruct Hsi as [HsiA [HsiB HsiC]].
      
      specialize (IHHWT cfg1 l C' Theta0 cfg2 HsiA).
      
      pose proof (ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H2)) as Hwspe.
      
      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (elt:=Expr.typ) (ChorEnv.find A0 (ChorEnv.add B y tau G)) /\
                   Var.Map.Empty (elt:=Expr.typ) (ChorEnv.find A0 (Actor.Map.add A DeltaA2 D))) as Hih.
      {
        intros A0 HA0inl.

        assert (Actor.FSet.In A (Insn.actors (Insn.Send A e B y))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        assert (Actor.FSet.In B (Insn.actors (Insn.Send A e B y))) as HBinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.Send A e B y))
                      H12 HA0inl HAinI).
        
        pose proof (members_dj A0 B
                      (Label.actors l)
                      (Insn.actors (Insn.Send A e B y))
                      H12 HA0inl HBinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        { rewrite find_ab_neq1; auto. }
        { rewrite find_ab_neq2; auto. }
      }

      specialize (IHHWT Hwspe Hih).

      eapply Send.
      { auto. }
      { eauto. }
      {
        assert
          (WellTyped
             (ChorEnv.add B y tau G)
             (Actor.Map.add A DeltaA2 D)
             (Actor.Map.add A (ChorEnv.find A Theta0) T2) C') as HwtC.
        { rewrite HsiC; auto. }
        eauto.
      }
      { auto. }
      { apply (@Var.Map.Properties.Partition_sym _
                 (ChorEnv.find A T2) (ChorEnv.find A Theta0) ThetaA1 HsiB). }

  (* Case LetBang *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case LetBangC *)
    + unfold  WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
      
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in *.    
      
      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H12 
                    ThetaA1 ThetaA2 (Expr.BANG tau) Hscoped H H1) as Hsi.
      
      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].
      
      eapply LetBang; auto.
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
        eapply Expr.preservation.
        { eauto. }
        { apply (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1). }
        { eauto. }
      }
      {
        rewrite H13.
        rewrite addadd2.
        eauto.
      }
      { auto. }
      { 
        rewrite H13.
        rewrite find_add; auto.
      }
      
    (* Case LetBangB *)
    + assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
      
      rewrite H13 in *.
      
      destruct (bangty_inversion (Var.Map.empty Expr.typ) DeltaA1 ThetaA1 e0 tau H)
        as [HbangA [HbangB HbangC]].
      rewrite HbangB in *.
      rewrite HbangC in *.
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in H0.
      pose proof (@Var.Map.Properties.Partition_sym _
                    (Var.Map.empty Expr.typ) (Var.Map.empty Expr.typ) DeltaA2 H0) as Hpart.
      pose proof (empty_partition
                    (Var.Map.empty Expr.typ) DeltaA2 (Var.Map.empty Expr.typ)
                    empty_map_empty Hpart) as Hep.
      
      rewrite empty_to_empty in HWT; auto.
      rewrite <- (lopsided_partition (ChorEnv.find A T) ThetaA2 H1) in HWT.
      rewrite find_add_env in HWT; auto.
      
      eapply wt_subst_bang; eauto.
      
    (* Case Delay/LetBang *)
    + assert (Var.Map.Partition (ChorEnv.find A T)
                (ChorEnv.find A (Actor.Map.add A ThetaA2 T)) ThetaA1) as Hsipart.
      {
        rewrite find_add; auto.
        apply @Var.Map.Properties.Partition_sym; auto.
      }
                        
      assert (ChorEnv.Equal
                (Actor.Map.add A (ChorEnv.find A T) (Actor.Map.add A ThetaA2 T)) T) as Hsieq.
      {
        rewrite addadd2; auto.
        rewrite find_add_env; auto.
        ChorEnv.simplify.
      }
      

      assert (Hnin : ~ Actor.FSet.In A (Label.actors l)).
      { simpl in H11. specialize (H11 A). Actor.simplify. }
      pose proof (step_inversion
                    C T cfg1 l C' T2 cfg2 H4 Hscoped
                    (ChorEnv.add A x tau G)
                    (Actor.Map.add A DeltaA2 D)
                    (Actor.Map.add A ThetaA2 T)
                    A ThetaA1 Hnin HWT Hsipart Hsieq) as Hsi.
      
      destruct Hsi as [T0 Hsi].
      destruct Hsi as [HsiA [HsiB HsiC]].

      specialize (IHHWT cfg1 l C' T0 cfg2 HsiA).

      pose proof (ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H1)) as Hwspe.
      
      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (elt:=Expr.typ) (ChorEnv.find A0 (ChorEnv.add A x tau G)) /\
                   Var.Map.Empty (elt:=Expr.typ) (ChorEnv.find A0 (Actor.Map.add A DeltaA2 D))) as Hih.
      {
        intros A0 HA0inl.

        assert (Actor.FSet.In A (Insn.actors (Insn.LetBang A x e))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.LetBang A x e))
                      H11 HA0inl HAinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        { rewrite find_ab_neq1; auto. }
        { rewrite find_ab_neq2; auto. }
      }

      specialize (IHHWT Hwspe Hih).

      eapply LetBang.
      { eauto. }
      {
        assert
          (WellTyped
             (ChorEnv.add A x tau G)
             (Actor.Map.add A DeltaA2 D)
             (Actor.Map.add A (ChorEnv.find A T0) T2) C') as HwtC.
        { rewrite HsiC; auto. }
        eauto.
      }
      { auto. }
      {
        apply (@Var.Map.Properties.Partition_sym _
                 (ChorEnv.find A T2) (ChorEnv.find A T0) ThetaA1 HsiB).
      }
      
  (* Case LetIn *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case LetC *)
    + unfold  WellScoped in Hscoped.
      specialize (Hscoped A).

      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].

      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
    
      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H13 
                    ThetaA1 ThetaA2 tau Hscoped H H1) as Hsi.

      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].

      eapply LetIn; eauto.
      { 
        eapply Expr.WellTyped_preservation.
        {
          rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp).
          rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
          eauto.
        }
        { auto. }
        { auto. }
        { apply (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1). }
        { eauto. }
      }
      {
        instantiate (1 := ThetaA2).
        rewrite H14.
        rewrite addadd2.
        auto.
      }
      {
        rewrite H14.
        rewrite find_add; auto.
      }

    (* Case LetC *) 
    + assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      
      eapply wt_subst_lin with (ThetaA2 := ThetaA2).
      {
        rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H.
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
        eauto.
      }
      {
        rewrite <- H15.
        rewrite rem_empty2 in HWT; auto.
        unfold ChorEnv.add.
        Var.simplify.
      }
      {
        rewrite <- H15; auto.
      }
      { 
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
        Var.simplify.
      }
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty).
        Var.simplify.
      }

    (* Case Delay/Let *)
    + 
    
    assert (Hnin : ~ Actor.FSet.In A (Label.actors l)).
    { simpl in H12. specialize (H12 A). Actor.simplify. }
    pose proof (step_inversion
                    C T cfg1 l C' T2 cfg2 H5 Hscoped
                    (ChorEnv.remove A x G)
                    (Actor.Map.add A (Var.Map.add x tau DeltaA2) D) 
                    (Actor.Map.add A ThetaA2 T) A ThetaA1 Hnin
                    HWT) as Hsi.

      rewrite find_add in Hsi; auto.
      rewrite addadd2 in Hsi; auto.
      rewrite find_add_env in Hsi; auto.

      assert (Var.Map.Partition (ChorEnv.find A T) ThetaA2 ThetaA1).
      { apply (@Var.Map.Properties.Partition_sym _
                 (ChorEnv.find A T) ThetaA1 ThetaA2 H1). }
      assert (ChorEnv.Equal T T).
      { ChorEnv.simplify. }

      destruct (Hsi H3 H4) as [T0 HsiT0].
      destruct HsiT0 as [HsiT0A [HsiT0B HsiT0C]].

      pose proof (ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H1)) as Hwspe.
                    
      specialize (IHHWT cfg1 l C' T0 cfg2 HsiT0A Hwspe).

      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (ChorEnv.find A0 (ChorEnv.remove A x G)) /\
                   Var.Map.Empty (ChorEnv.find A0
                                    (Actor.Map.add A (Var.Map.add x tau DeltaA2) D))) as Hih.
      {
        intros A0 HA0inl.
        assert (Actor.FSet.In A (Insn.actors (Insn.Let A x e))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.Let A x e))
                      H12 HA0inl HAinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        { rewrite find_ab_neq3; auto. }
        { rewrite find_ab_neq2; auto. }
      }

      specialize (IHHWT Hih).
      
      eapply LetIn.
      { eauto. }
      {
        assert (WellTyped
                  (ChorEnv.remove A x G)
                  (Actor.Map.add A (Var.Map.add x tau DeltaA2) D)
                  (Actor.Map.add A (ChorEnv.find A T0) T2) C').
        rewrite HsiT0C.
        auto.
        eauto.
      }
      { eauto. }
      { eapply (@Var.Map.Properties.Partition_sym _ (
                    ChorEnv.find A T2) (ChorEnv.find A T0) ThetaA1 HsiT0B). }
      { auto. }

  (* Case LetPair *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case LetPairC *)
    + unfold  WellScoped in Hscoped.
      specialize (Hscoped A).
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
      
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in *.    
      
      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H16 
                    ThetaA1 ThetaA2 (Expr.Tensor tau1 tau2) Hscoped H H1) as Hsi.
      
      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].
      
      eapply LetPair; auto.
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty); auto.
        eapply Expr.preservation.
        { eauto. }
        { apply (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1). }
        { eauto. }
      }
      {
        rewrite H17.
        rewrite addadd2.
        eauto.
      }
      { auto. }
      { 
        rewrite H17.
        rewrite find_add; auto.
      }
      { auto. }
      { auto. }

    (* Case LetPairB *)
    + assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      rewrite H19 in *.
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp1.
      pose proof (empty_partition (ChorEnv.find A D) DeltaA2 DeltaA1 HADempty
                    (@Var.Map.Properties.Partition_sym _  (ChorEnv.find A D) DeltaA1 DeltaA2 H0)) as Hdp2.
      
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA2 Hdp2) in H0.  
       
      inversion H; subst.
      pose proof (empty_partition DeltaA1 Δ1 Δ2 Hdp1 H14) as Hdpd1.
      pose proof (empty_partition DeltaA1 Δ2 Δ1 Hdp1
                    (@Var.Map.Properties.Partition_sym _ DeltaA1 Δ1 Δ2 H14)) as Hdpd2.
      
      rewrite (Var.Map.Proofs.empty_map_equal Δ1 Hdpd1) in H12.    
      rewrite (Var.Map.Proofs.empty_map_equal Δ2 Hdpd2) in H13.
      
      rewrite rem_empty2 in HWT; auto.
      rewrite rem_empty2 in HWT; auto.
      rewrite addadd8 in HWT.
      rewrite addadd8 in HWT.
      rewrite empty_to_empty in HWT.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H12.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H13.
      
      pose proof wt_subst_lin as Hwtslinx2.
      
      specialize (Hwtslinx2 C Θ2 ThetaA2 tau2
                    G
                    (ChorEnv.add A x1 tau1 D)
                    (Actor.Map.add A (Var.Map.concat ThetaA2 Θ2) T)
                    A x2 v2 H13).
      
      rewrite addadd2 in Hwtslinx2; auto.
      rewrite find_add in Hwtslinx2; auto.
      
      destruct (partitioning
                  (ChorEnv.find A T) Θ1 ThetaA2 ThetaA1 Θ2
                  (@Var.Map.Properties.Partition_sym _ (ChorEnv.find A T)
                     ThetaA1 ThetaA2 H1) H15)
        as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
      
      assert (~ Var.Map.In x1 (ChorEnv.find A G)) as Hx1ninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      assert (~ Var.Map.In x2 (ChorEnv.find A G)) as Hx2ninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      
      rewrite addadd9 in HWT; auto.
      
      specialize (Hwtslinx2 HWT
                    (@Var.Map.Properties.Partition_sym _ (Var.Map.concat ThetaA2 Θ2)
                       ThetaA2 Θ2 HPartitionB)
                    Hx2ninG).
      
      rewrite find_add_map in Hwtslinx2; auto.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in Hwtslinx2; auto.
      
      assert (x2 <> x1) as Hx2nex1; auto.
      assert (~ Var.Map.In x1 (Var.Map.empty Expr.typ)) as Hx1niemp.
      Var.simplify.
      assert (~ Var.Map.In x2 (Var.Map.empty Expr.typ)) as Hx2niemp.
      Var.simplify.
      
      pose proof (nin_mapl (Var.Map.empty _) x2 x1 tau1 Hx2nex1 Hx2niemp).
      specialize (Hwtslinx2 (nin_mapl (Var.Map.empty _) x2 x1 tau1 Hx2nex1 Hx2niemp)).
      
      pose proof wt_subst_lin as Hwtslinx1.
      
      specialize (Hwtslinx1
                    (Choreography.subst A x2 v2 C)
                    Θ1
                    (Var.Map.concat ThetaA2 Θ2)
                    tau1
                    G
                    D
                    T
                    A x1 v1 H12 Hwtslinx2
                    HPartitionD Hx1ninG).
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in Hwtslinx1; auto.
      { Var.simplify. }
      { auto. }
      { rewrite rem_empty2; auto. }

    (* Case Delay/LetPair *)
    + 

      assert (Hnin : ~ Actor.FSet.In A (Label.actors l)).
      { simpl in H14. specialize (H14 A). Actor.simplify. }
      pose proof (step_inversion
                    C T cfg1 l C' T2 cfg2 H7 Hscoped
                    (ChorEnv.remove A x1 (ChorEnv.remove A x2 G))
                    (Actor.Map.add A (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D)
                    (Actor.Map.add A ThetaA2 T) A ThetaA1
                    Hnin HWT) as Hsi.

      rewrite find_add in Hsi; auto.
      rewrite addadd2 in Hsi; auto.
      rewrite find_add_env in Hsi; auto.

      assert (Var.Map.Partition (ChorEnv.find A T) ThetaA2 ThetaA1).
      { apply (@Var.Map.Properties.Partition_sym _
                 (ChorEnv.find A T) ThetaA1 ThetaA2 H1). }
      assert (ChorEnv.Equal T T).
      { ChorEnv.simplify. }

      destruct (Hsi H5 H6) as [T0 HsiT0].
      destruct HsiT0 as [HsiT0A [HsiT0B HsiT0C]].

      pose proof (ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H1)) as Hwspe.
                    
      specialize (IHHWT cfg1 l C' T0 cfg2 HsiT0A Hwspe).

      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (ChorEnv.find A0
                                  (ChorEnv.remove A x1 (ChorEnv.remove A x2 G))) /\
                   Var.Map.Empty (ChorEnv.find A0
                                    (Actor.Map.add A
                                       (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D))) as Hih.
      {
        intros A0 HA0inl.
        assert (Actor.FSet.In A (Insn.actors (Insn.LetPair A x1 x2 e ))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.LetPair A x1 x2 e))
                      H14 HA0inl HAinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        {
          rewrite find_ab_neq3; auto.
          rewrite find_ab_neq3; auto.
        }
        { rewrite find_ab_neq2; auto. }
      }

      specialize (IHHWT Hih).
      
      eapply LetPair.
      { eauto. }
      {
        assert (WellTyped
                  (ChorEnv.remove A x1 (ChorEnv.remove A x2 G))
                  (Actor.Map.add A (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D)
                  (Actor.Map.add A (ChorEnv.find A T0) T2) C').
        rewrite HsiT0C.
        auto.
        eauto.
      }
      { eauto. }
      { eapply (@Var.Map.Properties.Partition_sym _
                  (ChorEnv.find A T2) (ChorEnv.find A T0) ThetaA1 HsiT0B). }
      { auto. }
      { auto. }
      { auto. }
Qed.

Lemma bangval_inversion : forall Gamma Delta Theta e tau,
    Expr.WellTyped Gamma Delta Theta e (Expr.BANG tau) ->
    Expr.Val e ->
    exists e0, e = Expr.Bang e0.
Proof.
  intros.
  Expr.simplify_val.
  exists e0.
  auto.
Qed.

Lemma tensorval_inversion : forall Gamma Delta Theta e tau1 tau2,
    Expr.WellTyped Gamma Delta Theta e (Expr.Tensor tau1 tau2) ->
    Expr.Val e ->
    exists v1 v2, e = Expr.Pair v1 v2 /\ Expr.Val v1 /\ Expr.Val v2 .
Proof.
  intros.
  Expr.simplify_val.
  exists e1.
  exists e2.
  auto.
Qed.

Lemma step_scope : forall Theta Theta2 e Theta1 cfg1 e' Theta1' cfg2,
    Config.WellScoped Theta cfg1 ->
    Var.Map.Partition Theta Theta1 Theta2 ->
    Expr.step e Theta1 cfg1 e' Theta1' cfg2 ->
    Var.Map.Properties.Disjoint Theta1' Theta2.
Proof.
  intros ? ? ? ? ? ? ? ? HWS Hpart Hstep.
  dependent induction Hstep;
    Var.Map.Tactics.reflect_partition; auto;
    try (apply IHHstep; auto;
      Var.Map.Tactics.reflect_partition; auto;
      try reflexivity).

  * inversion H; subst; clear H.
    Var.simplify.
    split; auto.
    intros Hin; eapply Config.wf_qrefs in Hin; eauto.
    lia.
  * inversion H0; subst; clear H0.
    apply Var.Map.Proofs.disjoint_remove_1; auto.
Qed.

Lemma epr_exists : forall A B T cfg,
  exists q1 q2 T0 cfg',  ChorEnv.epr A B T cfg = (q1, q2, T0, cfg').
Proof.
  intros.
  eexists. eexists. eexists. eexists.
  Var.simplify.
Qed.
       
Theorem progress : forall G D T1 C1,
    WellTyped G D T1 C1 ->
    forall cfg1,
      WellScoped T1 cfg1 ->
      Actor.Map.Empty G ->
      Actor.Map.Empty D ->
      C1 = [] \/ exists l C2 T2 cfg2, step C1 T1 cfg1 l C2 T2 cfg2.
Proof.
  intros G D T1 C1 HWT.
  induction HWT; intros cfg1 Hscoped HGempty HDempty.

  (* Case Nil *)
  - auto.

  (* Case EPR *)
  - right.

    destruct (epr_exists A B T cfg1) as [q1 [q2 [T0 [cfg2 Hepr]]]].

    exists (Label.EPR A B).
    exists (Choreography.subst A x (Expr.QRef q1)
              (Choreography.subst B y (Expr.QRef q2) C)).
    eexists T0. 
    exists cfg2.

    eapply EPRB.
    eauto.
    Var.simplify.
    eauto.

  (* Case Send *)
  - right.

    (* This disjunction allows destruction into context and beta subcases *)
    assert (Expr.Val e \/ ~ Expr.Val e) as Hvale.
    tauto.
    destruct Hvale as [HvaleL | HvaleR].
    {
      pose proof (bangval_inversion (ChorEnv.find A G) DeltaA1 ThetaA1 e tau H0 HvaleL) as Hbang.
      destruct Hbang as [e0 Hbang].
      rewrite Hbang in H0.
      rewrite Hbang.

      exists (Label.Send A e0 B).
      exists (Choreography.subst B y e0 C).
      exists T.
      exists cfg1.

      apply SendB.
      auto.
      Var.simplify.
    }
    { 
      unfold WellScoped in Hscoped.
      specialize (Hscoped A).
      pose proof (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H2) as Hpart.
      
      pose proof
        (Expr.progress e (Expr.BANG tau) (ChorEnv.find A G) DeltaA1 ThetaA1 H0 cfg1 Hpart) as Heprog.

      rewrite (empty_eq_env G HGempty) in Heprog.

      assert (Var.Map.Empty (ChorEnv.find A D)) as HADempty.
      {
        rewrite (empty_eq_env D HDempty).
        apply (empty_is_empty A).
      }
     
      specialize (Heprog (empty_is_empty A)
                    (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H1)).

      destruct Heprog as [Habsurd | HeprogR].
      { contradiction. }
      {
        destruct HeprogR as [e' [ThetaA1' [cfg2 HeprogR]]].

        exists (Label.Loc A).
        exists (Insn.Send A e' B y :: C).
        exists (Actor.Map.add A (Var.Map.concat ThetaA1' ThetaA2) T).
        exists cfg2.

        eapply SendC.
        auto.
        Var.simplify.

        pose proof (concat_partition ThetaA1' ThetaA2
                      (step_scope (ChorEnv.find A T)
                         ThetaA2 e ThetaA1 cfg1 e' ThetaA1' cfg2
                         Hscoped H2 HeprogR)) as Hstepscope.

        pose proof (Expr.step_weakening_1
                      ThetaA1 ThetaA1' ThetaA2 e
                      (ChorEnv.find A T) cfg1 e'
                      (Var.Map.concat ThetaA1' ThetaA2)
                      cfg2
                      HeprogR H2 Hstepscope).
        eauto.
        Var.simplify.
      }
    }

  (* Case LetBang *)
  - right.

    (* This disjunction allows destruction into context and beta subcases *)
    assert (Expr.Val e \/ ~ Expr.Val e) as Hvale.
    tauto.
    destruct Hvale as [HvaleL | HvaleR].
    {
      pose proof (bangval_inversion (ChorEnv.find A G) DeltaA1 ThetaA1 e tau H HvaleL) as Hbang.
      destruct Hbang as [e0 Hbang].
      rewrite Hbang in H.
      rewrite Hbang.

      exists (Label.Loc A).
      exists (Choreography.subst A x e0 C).
      exists T.
      exists cfg1.

      apply LetBangB.
      auto.
      Var.simplify.
    }
    { 
      unfold WellScoped in Hscoped.
      specialize (Hscoped A).
      pose proof (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1) as Hpart.
      
      pose proof
        (Expr.progress e (Expr.BANG tau) (ChorEnv.find A G) DeltaA1 ThetaA1 H cfg1 Hpart) as Heprog.

      rewrite (empty_eq_env G HGempty) in Heprog.

      assert (Var.Map.Empty (ChorEnv.find A D)) as HADempty.
      {
        rewrite (empty_eq_env D HDempty).
        apply (empty_is_empty A).
      }
     
      specialize (Heprog (empty_is_empty A)
                    (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0)).

      destruct Heprog as [Habsurd | HeprogR].
      { contradiction. }
      {
        destruct HeprogR as [e' [ThetaA1' [cfg2 HeprogR]]].

        exists (Label.Loc A).
        exists (Insn.LetBang A x e' :: C).
        exists (Actor.Map.add A (Var.Map.concat ThetaA1' ThetaA2) T).
        exists cfg2.

        eapply LetBangC.
 
        pose proof (concat_partition ThetaA1' ThetaA2
                      (step_scope (ChorEnv.find A T)
                         ThetaA2 e ThetaA1 cfg1 e' ThetaA1' cfg2
                         Hscoped H1 HeprogR)) as Hstepscope.

        pose proof (Expr.step_weakening_1
                      ThetaA1 ThetaA1' ThetaA2 e
                      (ChorEnv.find A T) cfg1 e'
                      (Var.Map.concat ThetaA1' ThetaA2)
                      cfg2
                      HeprogR H1 Hstepscope).
        eauto.
        Var.simplify.
      }
    }

  (* Case LetIn *)
  - right.

    (* This disjunction allows destruction into context and beta subcases *)
    assert (Expr.Val e \/ ~ Expr.Val e) as Hvale.
    tauto.
    destruct Hvale as [HvaleL | HvaleR].
    {
      exists (Label.Loc A).
      exists (Choreography.subst A x e C).
      exists T.
      exists cfg1.

      apply LetB.
      auto.
      Var.simplify.
      Var.simplify.
    }
    { 
      unfold WellScoped in Hscoped.
      specialize (Hscoped A).
      pose proof (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1) as Hpart.
      
      pose proof
        (Expr.progress e tau (ChorEnv.find A G) DeltaA1 ThetaA1 H cfg1 Hpart) as Heprog.

      rewrite (empty_eq_env G HGempty) in Heprog.

      assert (Var.Map.Empty (ChorEnv.find A D)) as HADempty.
      {
        rewrite (empty_eq_env D HDempty).
        apply (empty_is_empty A).
      }
     
      specialize (Heprog (empty_is_empty A)
                    (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0)).

      destruct Heprog as [Habsurd | HeprogR].
      { contradiction. }
      {
        destruct HeprogR as [e' [ThetaA1' [cfg2 HeprogR]]].

        exists (Label.Loc A).
        exists (Insn.Let A x e' :: C).
        exists (Actor.Map.add A (Var.Map.concat ThetaA1' ThetaA2) T).
        exists cfg2.

        eapply LetC.
 
        pose proof (concat_partition ThetaA1' ThetaA2
                      (step_scope (ChorEnv.find A T)
                         ThetaA2 e ThetaA1 cfg1 e' ThetaA1' cfg2
                         Hscoped H1 HeprogR)) as Hstepscope.

        pose proof (Expr.step_weakening_1
                      ThetaA1 ThetaA1' ThetaA2 e
                      (ChorEnv.find A T) cfg1 e'
                      (Var.Map.concat ThetaA1' ThetaA2)
                      cfg2
                      HeprogR H1 Hstepscope).
        eauto.
        Var.simplify.
      }
    }

  (* Case LetPair *)
  - right.

    (* This disjunction allows destruction into context and beta subcases *)
    assert (Expr.Val e \/ ~ Expr.Val e) as Hvale.
    tauto.
    destruct Hvale as [HvaleL | HvaleR].
    {
      pose proof (tensorval_inversion
                    (ChorEnv.find A G) DeltaA1 ThetaA1 e tau1 tau2 H HvaleL) as Htensor.
      destruct Htensor as [v1 [v2 [HtensorA [HtensorB HtensorC]]]].
      rewrite HtensorA in H.
      rewrite HtensorA.
      
      exists (Label.Loc A).
      exists (Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C)).
      exists T.
      exists cfg1.

      apply LetPairB; auto.
      Var.simplify.
    }
    { 
      unfold WellScoped in Hscoped.
      specialize (Hscoped A).
      pose proof (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1) as Hpart.
      
      pose proof
        (Expr.progress
           e (Expr.Tensor tau1 tau2) (ChorEnv.find A G) DeltaA1 ThetaA1 H cfg1 Hpart) as Heprog.

      rewrite (empty_eq_env G HGempty) in Heprog.

      assert (Var.Map.Empty (ChorEnv.find A D)) as HADempty.
      {
        rewrite (empty_eq_env D HDempty).
        apply (empty_is_empty A).
      }
     
      specialize (Heprog (empty_is_empty A)
                    (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0)).

      destruct Heprog as [Habsurd | HeprogR].
      { contradiction. }
      {
        destruct HeprogR as [e' [ThetaA1' [cfg2 HeprogR]]].

        exists (Label.Loc A).
        exists (Insn.LetPair A x1 x2 e' :: C).
        exists (Actor.Map.add A (Var.Map.concat ThetaA1' ThetaA2) T).
        exists cfg2.

        eapply LetPairC.
 
        pose proof (concat_partition ThetaA1' ThetaA2
                      (step_scope (ChorEnv.find A T)
                         ThetaA2 e ThetaA1 cfg1 e' ThetaA1' cfg2
                         Hscoped H1 HeprogR)) as Hstepscope.

        pose proof (Expr.step_weakening_1
                      ThetaA1 ThetaA1' ThetaA2 e
                      (ChorEnv.find A T) cfg1 e'
                      (Var.Map.concat ThetaA1' ThetaA2)
                      cfg2
                      HeprogR H1 Hstepscope).
        eauto.
        Var.simplify.
      }
    }

Qed.

Theorem preservation_v2 : forall G D T1 C1,
    WellTyped G D T1 C1 ->
    forall cfg1 l C2 T2 cfg2, 
      step C1 T1 cfg1 l C2 T2 cfg2 ->
      WellScoped T1 cfg1 ->
        (forall A, Actor.FSet.In A (Label.actors l) ->
                   Var.Map.Empty (ChorEnv.find A G) /\  Var.Map.Empty (ChorEnv.find A D)) ->   
        WellTyped G D T2 C2.
Proof.
  intros G D T1 C1 HWT.
  induction HWT.

  (* Case Nil *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.
    apply nilnostep in HStep.
    contradiction.

  (* Case EPR *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case EPRB *) 
    + assert (Actor.FSet.In A (Label.actors (Label.EPR A B))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      assert (Actor.FSet.In B (Label.actors (Label.EPR A B))) as HBinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      destruct (Hemptiness B HBinl) as [HBGempty HBDempty].
      
      destruct (epr_inversion A B T cfg1 q1 q2 T0 cfg2 H H13 Hscoped) as [HeprA HeprB].
      destruct HeprA as [idx1 [idx2]].
      destruct H2 as [HeprAA HeprAB].
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q1 idx1 (Var.Map.empty _))
                    q1 idx1 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q1 idx1)) as Hq1ty.
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q2 idx2 (Var.Map.empty _))
                    q2 idx2 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q2 idx2)) as Hq2ty.
      
      rewrite rem_empty2 in HWT; auto.
      rewrite rem_empty2 in HWT; auto.
      rewrite HeprB in HWT.
      
      pose proof (wt_subst_lin
                    C
                    (Var.Map.add q2 idx2 (Var.Map.empty nat))
                    (ChorEnv.find B T)
                    Expr.QUBIT
                    G
                    (ChorEnv.add A x Expr.QUBIT D)
                    (Actor.Map.add A (ChorEnv.find A T) T0)
                    B y
                    (Expr.QRef q2)
                    Hq2ty HWT) as HwtCAx.
      
      rewrite find_ab_neq1 in HwtCAx; auto.
      rewrite find_ab_neq2 in HwtCAx; auto.
      
      assert (~ Var.Map.In x (ChorEnv.find A G)) as HxninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      assert (~ Var.Map.In y (ChorEnv.find B G)) as HyninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find B G) HBGempty).
      Var.simplify.
      
      specialize (HwtCAx
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find B T0)
                       (ChorEnv.find B T)
                       (Var.Map.add q2 idx2 (Var.Map.empty nat))
                       HeprAB)
                    HyninG H1).
      
      pose proof (wt_subst_lin
                    (Choreography.subst B y (Expr.QRef q2) C)
                    (Var.Map.add q1 idx1 (Var.Map.empty nat))
                    (ChorEnv.find A T)
                    Expr.QUBIT
                    G
                    D
                    T0
                    A x
                    (Expr.QRef q1)
                    Hq1ty HwtCAx) as HwtCBy.
      
      rewrite H14.
      apply (HwtCBy
               (@Var.Map.Properties.Partition_sym _
                  (ChorEnv.find A T0)
                  (ChorEnv.find A T)
                  (Var.Map.add q1 idx1 (Var.Map.empty nat))
                  HeprAA)
               HxninG H0).
      
      rewrite find_ab_neq3; auto.

    (* Case EPRB' *) 
    + assert (Actor.FSet.In A (Label.actors (Label.EPR B A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      assert (Actor.FSet.In B (Label.actors (Label.EPR B A))) as HBinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      destruct (Hemptiness B HBinl) as [HBGempty HBDempty].

      assert (B <> A) as HBneA; auto.
      destruct (epr_inversion B A T cfg1 q2 q1 T0 cfg2 HBneA H13 Hscoped) as [HeprA HeprB].
      destruct HeprA as [idx1 [idx2]].
      destruct H2 as [HeprAA HeprAB].
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q1 idx2 (Var.Map.empty _))
                    q1 idx2 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q1 idx2)) as Hq1ty.
      
      pose proof (qref_ty
                    (Var.Map.empty _)
                    (Var.Map.empty _)
                    (Var.Map.add q2 idx1 (Var.Map.empty _))
                    q2 idx1 empty_map_empty
                    (Var.Map.Proofs.singleton_singleton nat q2 idx1)) as Hq2ty.
      
      rewrite rem_empty2 in HWT; auto.
      rewrite rem_empty2 in HWT; auto.
      rewrite HeprB in HWT.
      rewrite addadd4 in HWT; auto.
      
      pose proof (wt_subst_lin
                    C
                    (Var.Map.add q2 idx1 (Var.Map.empty nat))
                    (ChorEnv.find B T)
                    Expr.QUBIT
                    G
                    (ChorEnv.add A x Expr.QUBIT D)
                    (Actor.Map.add A (ChorEnv.find A T) T0)
                    B y
                    (Expr.QRef q2)
                    Hq2ty HWT) as HwtCBy.
      
      rewrite find_ab_neq1 in HwtCBy; auto.
      rewrite find_ab_neq2 in HwtCBy; auto.
      
      assert (~ Var.Map.In x (ChorEnv.find A G)) as HxninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
      Var.simplify.
      assert (~ Var.Map.In y (ChorEnv.find B G)) as HyninG.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find B G) HBGempty).
      Var.simplify.
      
      specialize (HwtCBy
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find B T0)
                       (ChorEnv.find B T)
                       (Var.Map.add q2 idx1 (Var.Map.empty nat))
                       HeprAA)
                    HyninG H1).
      
      pose proof (wt_subst_lin
                    (Choreography.subst B y (Expr.QRef q2) C)
                    (Var.Map.add q1 idx2 (Var.Map.empty nat))
                    (ChorEnv.find A T)
                    Expr.QUBIT
                    G
                    D
                    T0
                    A x
                    (Expr.QRef q1)
                    Hq1ty HwtCBy) as HwtCAx.
      
      rewrite H14.
      apply (HwtCAx
               (@Var.Map.Properties.Partition_sym _
                  (ChorEnv.find A T0)
                  (ChorEnv.find A T)
                  (Var.Map.add q1 idx2 (Var.Map.empty nat))
                  HeprAB)
               HxninG H0).
      
      rewrite find_ab_neq3; auto.

    (* Case Delay/EPR *) 
    + assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (ChorEnv.find A0 (ChorEnv.remove B y (ChorEnv.remove A x G))) /\
                   Var.Map.Empty (ChorEnv.find A0
                                    (ChorEnv.add B y Expr.QUBIT (ChorEnv.add A x Expr.QUBIT D)))) as Hih.
      {
        intros A0 HA0inl.
        
        assert (Actor.FSet.In A (Insn.actors (Insn.EPR A x B y))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        assert (Actor.FSet.In B (Insn.actors (Insn.EPR A x B y))) as HBinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.EPR A x B y))
                      H11 HA0inl HAinI).
        
        pose proof (members_dj A0 B
                      (Label.actors l)
                      (Insn.actors (Insn.EPR A x B y))
                      H11 HA0inl HBinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        {
          rewrite find_ab_neq3; auto.
          rewrite find_ab_neq3; auto.
        }
        {
          rewrite find_ab_neq1; auto.
          rewrite find_ab_neq1; auto.                    
        }
      }

      specialize (IHHWT cfg1 l C' T2 cfg2 H4 Hscoped Hih).

      apply EPR.
      { auto. }
      { auto. }
      { auto. }
      { auto. }

  (* Case Send *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.
   
    (* Case SendC *)
    + unfold  WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in H1.
      
      assert (Var.Map.Empty (Var.Map.M.empty Expr.typ)) as Hee.
      Var.simplify.
      
      pose proof (empty_partition (Var.Map.M.empty Expr.typ) DeltaA1 DeltaA2 Hee H1) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H0.
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H0.
      

      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H14
                    ThetaA1 ThetaA2 (Expr.BANG tau) Hscoped H0 H2) as Hsi.
      
      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].
      
      eapply Send.
      { auto. }
      { 
        eapply Expr.WellTyped_preservation.
        { rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty); eauto. }
        { rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty); Var.simplify. }
        { Var.simplify. }
        { apply (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H2). }
        { eauto. }
      }
      {
        rewrite H15.
        rewrite addadd2.
        eauto.
      }
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty).
        rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H1.
        auto.
      }
      {
        rewrite H15.
        rewrite find_add; auto.
      }
   
    (* Case SendB *)
    + rewrite <- H15 in *.

      assert (Actor.FSet.In A (Label.actors (Label.Send A v B))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      assert (Actor.FSet.In B (Label.actors (Label.Send A v B))) as HBinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      destruct (Hemptiness B HBinl) as [HBGempty HBDempty].
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H0.
      destruct (bangty_inversion (Var.Map.empty Expr.typ) DeltaA1 ThetaA1 v tau H0)
        as [HbangA [HbangB HbangC]].
      rewrite HbangB in *.
      rewrite HbangC in *.

      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in H1.
      pose proof (@Var.Map.Properties.Partition_sym _
                    (Var.Map.empty Expr.typ) (Var.Map.empty Expr.typ) DeltaA2 H1) as Hpart.
      pose proof (empty_partition
                    (Var.Map.empty Expr.typ) DeltaA2 (Var.Map.empty Expr.typ)
                    empty_map_empty Hpart) as Hep.
      eapply wt_subst_bang; eauto.
      
      rewrite <- (lopsided_partition (ChorEnv.find A T) ThetaA2 H2) in HWT.
      rewrite find_add_env in HWT; auto.
      rewrite empty_to_empty in HWT; auto.
   
    (* Case Delay/Send *)
    + assert (Partition_except l T (Actor.Map.add A ThetaA2 T)) as Hpart.
      {
        unfold Partition_except.
        split.
        {
          intros.
          assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
          tauto.
          {
            rewrite <- HAeqA0 in *.
            exists ThetaA1.
            rewrite find_add.
            pose proof (@Var.Map.Properties.Partition_sym _
                          (ChorEnv.find A T) ThetaA1 ThetaA2 H2); auto.
          }
          {
            exists (Var.Map.empty _).
            rewrite find_ab_neq2; auto.
            apply Var.Map.Proofs.partition_empty_r.
          }
        }
        {
          intros.

          assert (Actor.FSet.In A (Insn.actors (Insn.Send A e B y))) as HAinI.
          unfold Insn.actors.
          Actor.simplify.
          
          pose proof (members_dj A0 A
                        (Label.actors l)
                        (Insn.actors (Insn.Send A e B y)) H12 H3 HAinI).
          
          rewrite find_ab_neq2; auto.
          Var.simplify.
        }
      }
      
      pose proof (delay_inversion
                    C T cfg1 l C' T2 cfg2 H5 Hscoped
                    (ChorEnv.add B y tau G)
                    (Actor.Map.add A DeltaA2 D)
                    (Actor.Map.add A ThetaA2 T)
                    Hpart HWT) as Hsi.
      
      destruct Hsi as [T2' [HsiA HsiB]].
      
      specialize (IHHWT cfg1 l C' T2' cfg2 HsiA).
      
      pose proof (ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H2)) as Hwspe.
      
      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (elt:=Expr.typ) (ChorEnv.find A0 (ChorEnv.add B y tau G)) /\
                   Var.Map.Empty (elt:=Expr.typ) (ChorEnv.find A0 (Actor.Map.add A DeltaA2 D))) as Hih.
      {
        intros A0 HA0inl.

        assert (Actor.FSet.In A (Insn.actors (Insn.Send A e B y))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        assert (Actor.FSet.In B (Insn.actors (Insn.Send A e B y))) as HBinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.Send A e B y))
                      H12 HA0inl HAinI).
        
        pose proof (members_dj A0 B
                      (Label.actors l)
                      (Insn.actors (Insn.Send A e B y))
                      H12 HA0inl HBinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        { rewrite find_ab_neq1; auto. }
        { rewrite find_ab_neq2; auto. }
      }

      specialize (IHHWT Hwspe Hih).
      destruct (spps_on A ThetaA1 ThetaA2 T T2 T2' HsiB H2) as [HsppsonA HsppsonB].

      eapply Send.
      { auto. }
      { eauto. }
      {
        assert (WellTyped
                  (ChorEnv.add B y tau G)
                  (Actor.Map.add A DeltaA2 D)
                  (Actor.Map.add A (ChorEnv.find A T2') T2) C').
        {
          rewrite HsppsonA in IHHWT; auto.
        }
        eauto.
      }
      { auto. }
      { auto. }
      
  (* Case LetBang *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case LetBangC *)
    + unfold  WellScoped in Hscoped.
      specialize (Hscoped A).
      
      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
      
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in *.    
      
      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H12 
                    ThetaA1 ThetaA2 (Expr.BANG tau) Hscoped H H1) as Hsi.
      
      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].
      
      eapply LetBang; auto.
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
        eapply Expr.preservation.
        { eauto. }
        { apply (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1). }
        { eauto. }
      }
      {
        rewrite H13.
        rewrite addadd2.
        eauto.
      }
      { auto. }
      { 
        rewrite H13.
        rewrite find_add; auto.
      }
      
    (* Case LetBangB *)
    + assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
      
      rewrite H13 in *.
      
      destruct (bangty_inversion (Var.Map.empty Expr.typ) DeltaA1 ThetaA1 e0 tau H)
        as [HbangA [HbangB HbangC]].
      rewrite HbangB in *.
      rewrite HbangC in *.
      
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty) in H0.
      pose proof (@Var.Map.Properties.Partition_sym _
                    (Var.Map.empty Expr.typ) (Var.Map.empty Expr.typ) DeltaA2 H0) as Hpart.
      pose proof (empty_partition
                    (Var.Map.empty Expr.typ) DeltaA2 (Var.Map.empty Expr.typ)
                    empty_map_empty Hpart) as Hep.
      
      rewrite empty_to_empty in HWT; auto.
      rewrite <- (lopsided_partition (ChorEnv.find A T) ThetaA2 H1) in HWT.
      rewrite find_add_env in HWT; auto.
      
      eapply wt_subst_bang; eauto.

    (* Case Delay/LetBang *)
    + assert (Partition_except l T (Actor.Map.add A ThetaA2 T)) as Hpart.
      {
        unfold Partition_except.
        split.
        {
          intros.
          assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
          tauto.
          {
            rewrite <- HAeqA0 in *.
            exists ThetaA1.
            rewrite find_add.
            pose proof (@Var.Map.Properties.Partition_sym _
                          (ChorEnv.find A T) ThetaA1 ThetaA2 H1); auto.
          }
          {
            exists (Var.Map.empty _).
            rewrite find_ab_neq2; auto.
            apply Var.Map.Proofs.partition_empty_r.
          }
        }
        {
          intros.

          assert (Actor.FSet.In A (Insn.actors (Insn.LetBang A x e))) as HAinI.
          unfold Insn.actors.
          Actor.simplify.
          
          pose proof (members_dj A0 A
                        (Label.actors l)
                        (Insn.actors (Insn.LetBang A x e)) H11 H2 HAinI).
          
          rewrite find_ab_neq2; auto.
          Var.simplify.
        }
      }
      
      pose proof (delay_inversion
                    C T cfg1 l C' T2 cfg2 H4 Hscoped
                    (ChorEnv.add A x tau G)
                    (Actor.Map.add A DeltaA2 D)
                    (Actor.Map.add A ThetaA2 T)
                    Hpart HWT) as Hsi.
      
      destruct Hsi as [T2' [HsiA HsiB]].
      
      specialize (IHHWT cfg1 l C' T2' cfg2 HsiA).
      
      pose proof (ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H1)) as Hwspe.
      
      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (elt:=Expr.typ) (ChorEnv.find A0 (ChorEnv.add A x tau G)) /\
                   Var.Map.Empty (elt:=Expr.typ) (ChorEnv.find A0 (Actor.Map.add A DeltaA2 D))) as Hih.
      {
        intros A0 HA0inl.

        assert (Actor.FSet.In A (Insn.actors (Insn.LetBang A x e))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.LetBang A x e))
                      H11 HA0inl HAinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        { rewrite find_ab_neq1; auto. }
        { rewrite find_ab_neq2; auto. }
      }

      specialize (IHHWT Hwspe Hih).
      destruct (spps_on A ThetaA1 ThetaA2 T T2 T2' HsiB H1) as [HsppsonA HsppsonB].

      eapply LetBang.
      { eauto. }
      {
        assert (WellTyped
                  (ChorEnv.add A x tau G)
                  (Actor.Map.add A DeltaA2 D)
                  (Actor.Map.add A (ChorEnv.find A T2') T2) C').
        {
          rewrite HsppsonA in IHHWT; auto.
        }
        eauto.
      }
      { auto. }
      { auto. }
      
  (* Case LetIn *)
  - intros cfg1 l C2 T2 cfg2 HStep Hscoped Hemptiness.

    inversion HStep; subst.

    (* Case LetC *)
    + unfold  WellScoped in Hscoped.
      specialize (Hscoped A).

      assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].

      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H.
      rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
    
      pose proof (Expr.step_inversion e (ChorEnv.find A T) cfg1 e' TA' cfg2 H13 
                    ThetaA1 ThetaA2 tau Hscoped H H1) as Hsi.

      destruct Hsi as [ThetaA1' Hsi].
      destruct Hsi as [HsiA HsiB].

      eapply LetIn; eauto.
      { 
        eapply Expr.WellTyped_preservation.
        {
          rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp).
          rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
          eauto.
        }
        { auto. }
        { auto. }
        { apply (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg1 Hscoped H1). }
        { eauto. }
      }
      {
        instantiate (1 := ThetaA2).
        rewrite H14.
        rewrite addadd2.
        auto.
      }
      {
        rewrite H14.
        rewrite find_add; auto.
      }

    (* Case LetC *) 
    + assert (Actor.FSet.In A (Label.actors (Label.Loc A))) as HAinl.
      unfold Label.actors.
      Actor.simplify.
      destruct (Hemptiness A HAinl) as [HAGempty HADempty].
      
      pose proof (empty_partition (ChorEnv.find A D) DeltaA1 DeltaA2 HADempty H0) as Hdp.
      
      eapply wt_subst_lin with (ThetaA2 := ThetaA2).
      {
        rewrite (Var.Map.Proofs.empty_map_equal DeltaA1 Hdp) in H.
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty) in H.
        eauto.
      }
      {
        rewrite <- H15.
        rewrite rem_empty2 in HWT; auto.
        unfold ChorEnv.add.
        Var.simplify.
      }
      {
        rewrite <- H15; auto.
      }
      { 
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A G) HAGempty).
        Var.simplify.
      }
      {
        rewrite (Var.Map.Proofs.empty_map_equal (ChorEnv.find A D) HADempty).
        Var.simplify.
      }

    (* Case Delay/Let *)
    + assert (Partition_except l T (Actor.Map.add A ThetaA2 T)) as Hpart.
      {
        unfold Partition_except.
        split.
        {
          intros.
          assert (A = A0 \/ A <> A0) as [HAeqA0 | HneqA0].
          tauto.
          {
            rewrite <- HAeqA0 in *.
            exists ThetaA1.
            rewrite find_add.
            pose proof (@Var.Map.Properties.Partition_sym _
                          (ChorEnv.find A T) ThetaA1 ThetaA2 H1); auto.
          }
          {
            exists (Var.Map.empty _).
            rewrite find_ab_neq2; auto.
            apply Var.Map.Proofs.partition_empty_r.
          }
        }
        {
          intros.

          assert (Actor.FSet.In A (Insn.actors (Insn.Let A x e))) as HAinI.
          unfold Insn.actors.
          Actor.simplify.
          
          pose proof (members_dj A0 A
                        (Label.actors l)
                        (Insn.actors (Insn.LetBang A x e)) H12 H3 HAinI).
          
          rewrite find_ab_neq2; auto.
          Var.simplify.
        }
      }
      
      pose proof (delay_inversion
                    C T cfg1 l C' T2 cfg2 H5 Hscoped
                    (ChorEnv.remove A x G)
                    (Actor.Map.add A (Var.Map.add x tau DeltaA2) D)
                    (Actor.Map.add A ThetaA2 T)
                    Hpart HWT) as Hsi.
      
      destruct Hsi as [T2' [HsiA HsiB]].
      
      specialize (IHHWT cfg1 l C' T2' cfg2 HsiA).
      
      pose proof (ws_partition_env
                    A T ThetaA2 ThetaA1 cfg1 Hscoped
                    (@Var.Map.Properties.Partition_sym _
                       (ChorEnv.find A T) ThetaA1 ThetaA2 H1)) as Hwspe.
      
      assert (forall A0 : Actor.FSet.elt,
                 Actor.FSet.In A0 (Label.actors l) ->
                 Var.Map.Empty (ChorEnv.find A0 (ChorEnv.remove A x G)) /\
                   Var.Map.Empty (ChorEnv.find A0
                                    (Actor.Map.add A (Var.Map.add x tau DeltaA2) D))) as Hih.
      {
        intros A0 HA0inl.
        assert (Actor.FSet.In A (Insn.actors (Insn.Let A x e))) as HAinI.
        unfold Insn.actors.
        Actor.simplify.
        
        pose proof (members_dj A0 A
                      (Label.actors l)
                      (Insn.actors (Insn.Let A x e))
                      H12 HA0inl HAinI).
        
        destruct (Hemptiness A0 HA0inl) as [HempA0G HempA0D].
        split.
        { rewrite find_ab_neq3; auto. }
        { rewrite find_ab_neq2; auto. }
      }
      
      specialize (IHHWT Hwspe Hih).
      destruct (spps_on A ThetaA1 ThetaA2 T T2 T2' HsiB H1) as [HsppsonA HsppsonB].

      eapply LetIn.
      { eauto. }
      {
        assert (WellTyped
                  (ChorEnv.remove A x G)
                  (Actor.Map.add A (Var.Map.add x tau DeltaA2) D)
                  (Actor.Map.add A (ChorEnv.find A T2') T2) C').
        {
          rewrite HsppsonA in IHHWT; auto.
        }
        eauto.
      }
      { auto. }
      { auto. }
      { auto. }
        

Admitted.
 
