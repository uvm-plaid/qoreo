From Qoreo Require Import Base.
From Qoreo Require Expr.

From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Setoid.


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
        Check bind_eq_dec.
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
    Expr.Val v ->
    C' = Choreography.subst B x v C ->
    ChorEnv.Equal refs refs' ->
    step  (Insn.Send A v B x :: C) refs cfg
          (Label.Send A v B)
          C' refs' cfg

| EPRB : forall q1 q2 T0 A x B y C T cfg C' T' cfg',
    ChorEnv.epr A B T cfg = (q1, q2, T0, cfg') ->
    ChorEnv.Equal T' T0 ->

    C' = Choreography.subst A x (Expr.Var q1) (Choreography.subst B y (Expr.Var q2) C) ->

    step  (Insn.EPR A x B y :: C) T cfg
          (Label.EPR A B) 
          C' T' cfg'

| EPRB' : forall q1 q2 T0 A x B y C T cfg C' T' cfg',
    ChorEnv.epr B A T cfg = (q2, q1, T0, cfg') ->
    ChorEnv.Equal T' T0 ->

    C' = Choreography.subst A x (Expr.Var q1) (Choreography.subst B y (Expr.Var q2) C) ->

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

Inductive WellTyped :
  ChorEnv.t Expr.typ -> ChorEnv.t Expr.typ -> ChorEnv.t nat -> Choreography.t -> Prop :=
  
| Nil : forall G D T, 
    Actor.Map.Empty D ->
    Actor.Map.Empty T ->
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

    WellTyped G D T ((Insn.LetPair A x1 x2 e)::C)
.

From Stdlib Require Import Morphisms. (* for Proper *)

Lemma empty_Equal : forall T (M1 M2 : ChorEnv.t T),
  ChorEnv.Equal M1 M2 ->
  Actor.Map.Empty M1 ->
  Actor.Map.Empty M2.
Proof.
  intros T M1 M2 [Heq Heq'] Hempty.
  Actor.reflect_find.
  apply Actor.Map.Properties.F.not_find_in_iff.
  rewrite <- Heq.
  Actor.simplify. rewrite Hempty.
  Actor.solve.
Qed.
  

Global Instance empty_Proper' : forall T,
  Proper (ChorEnv.Equal ==> iff) (@Actor.Map.Empty (Var.Map.t T)).
Proof.
  intros T M1 M2 Heq.
  split; apply empty_Equal; auto.
  symmetry; auto.
Qed.

Lemma WellTyped_proper : forall G D T C,
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
  split; intros; eapply WellTyped_proper; eauto;
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

(* START Jennifer to address with map tactics. *)

Lemma extension : forall A G x (tau : Expr.typ),
    ChorEnv.MapsTo A x tau G <-> Var.Map.MapsTo x tau (ChorEnv.find A G).
Proof.
  intros A G x tau.
  split.
  auto.
  auto.
Qed.

Lemma empty_dj : forall {X : Type} (CE1 : ChorEnv.t X) CE2 A,
    Actor.Map.Empty CE2 ->
    Var.Map.Properties.Disjoint (ChorEnv.find A CE1) (ChorEnv.find A CE2).
Proof.
  intros X CE1 CE2 A Hempty.
  intros z [Hin1 Hin2].
  unfold ChorEnv.find in Hin2.
  rewrite Actor.Map.Proofs.Empty_find in Hempty.
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
Admitted.

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
    ~ Actor.Map.Empty (ChorEnv.add A x tau D).
Proof.
  intros. intros Hempty.
  unfold ChorEnv.add in Hempty.
  Actor.simplify.
Qed.

Lemma empty_is_empty : forall {X : Type} A,
    Var.Map.Empty (ChorEnv.find A (Actor.Map.empty (Var.Map.t X))).
Proof.
Admitted.

Lemma empty_partition : forall (M M1 M2 : Var.Map.t Expr.typ),
    Var.Map.Empty M ->
    Var.Map.Partition M M1 M2 ->
    Var.Map.Empty M1.
Proof.
Admitted.

Lemma find_add : forall {X : Type} A M (CE : ChorEnv.t X),
    ChorEnv.find A (Actor.Map.add A M CE) = M.
Proof.
  intros.
  unfold ChorEnv.find.
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
Admitted.

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
Admitted.

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
Admitted.

Lemma readd_eq: forall A x tau (CE : ChorEnv.t Expr.typ),
    Var.Map.MapsTo x tau (ChorEnv.find A CE) ->
    ChorEnv.Equal (ChorEnv.add A x tau CE) CE.
Proof.
Admitted.

Lemma remove_add_partition : forall (CE1 CE2 CE3: ChorEnv.t Expr.typ) A B x tau,
    Var.Map.Partition (ChorEnv.find A CE1)
      (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
    Var.Map.MapsTo x tau (ChorEnv.find B CE1) ->
    Var.Map.Partition (ChorEnv.find A CE1)
      (ChorEnv.find A (ChorEnv.add B x tau CE2))
      (ChorEnv.find A (ChorEnv.remove B x CE3)).
Proof.
Admitted.
  
Lemma map_subset_add : forall A B y tau (CE1 : ChorEnv.t Expr.typ) CE2 CE3,
    ~ Var.Map.MapsTo y tau (ChorEnv.find B CE3) ->
    Var.Map.Partition (ChorEnv.find A CE1) (ChorEnv.find A CE2) (ChorEnv.find A CE3) ->
    Var.Map.Partition
      (ChorEnv.find A (ChorEnv.add B y tau CE1))
      (ChorEnv.find A (ChorEnv.add B y tau CE2)) (ChorEnv.find A CE3).
Proof.
  intros.
  Var.simplify.
  Actor.Map.Tactics.compare A B; subst; auto.
  apply Var.Map.Proofs.partition_add_l; auto.
    admit (*??*).
Admitted.

Lemma add_mapsto : forall x (tau : Expr.typ) m,
    Var.Map.MapsTo x tau m ->
    Var.Map.Equal (Var.Map.add x tau m) m.
Proof.
  intros. Var.solve.
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
                      H8).
        
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
        assert (Var.Map.MapsTo y tau (ChorEnv.find B G0) \/
                  ~ Var.Map.MapsTo y tau (ChorEnv.find B G0)) as HCasesByinG0.
        tauto.
        
        destruct HCasesByinG0 as [HCasesByinG0L | HCasesByinG0R].
        {
          specialize (HE B) as HEBinG0.
          destruct HEBinG0 as [HEBinG0A HEBinG0B].
          pose proof (map_partition_map y tau
                        (ChorEnv.find B G') (ChorEnv.find B G) (ChorEnv.find B G0)
                        HCasesByinG0L
                        HEBinG0A) as Hmpm.
          rewrite (readd_eq B y tau G' Hmpm).
          
          apply (IHC
                   (ChorEnv.add B y tau G) (Actor.Map.add A DeltaA2 D)
                   (Actor.Map.add A ThetaA2 T) (ChorEnv.remove B y G0) H9 G').

          intros A0.
          destruct (HE A0) as [HEA0A HA0EB].

          split.
          {
            apply (remove_add_partition G' G G0 A0 B y tau HEA0A Hmpm).
          }
          {
            pose proof (remove_dj_env G0 D A0 B y HA0EB) as HG0Ddj.

            assert (A0 = A \/ A0 <> A) as HeqA0A.
            tauto.
            destruct HeqA0A as [HeqA0AL | HeqA0AR].
            {
              rewrite HeqA0AL in *.
              rewrite find_add.
              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A D) DeltaA1 DeltaA2 H10) as Hpart.
              apply (partition_dj
                       (ChorEnv.find A (ChorEnv.remove B y G0))
                       (ChorEnv.find A D)
                       DeltaA2 DeltaA1
                       HG0Ddj Hpart).
            }
            { rewrite find_ab_neq2; auto. }

          }
        }
        {
          apply (IHC
                   (ChorEnv.add B y tau G) (Actor.Map.add A DeltaA2 D)
                   (Actor.Map.add A ThetaA2 T) G0 H9 (ChorEnv.add B y tau G')).       
          intros A0.
          destruct (HE A0) as [HEA0A HEA0B].
          split.
          { apply (map_subset_add A0 B y tau G' G G0 HCasesByinG0R HEA0A). }
          { apply (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEA0B H10). }
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
        assert (Var.Map.MapsTo y tau (ChorEnv.find A G0) \/
                  ~ Var.Map.MapsTo y tau (ChorEnv.find A G0)) as HCasesAyinG0.
        tauto.
        
        destruct HCasesAyinG0 as [HCasesAyinG0L | HCasesAyinG0R].
        {
          specialize (HE A) as HEAinG0.
          destruct HEAinG0 as [HEAinG0A HEAinG0B].
          pose proof (map_partition_map y tau
                        (ChorEnv.find A G') (ChorEnv.find A G) (ChorEnv.find A G0)
                        HCasesAyinG0L
                        HEAinG0A) as Hmpm.
          rewrite (readd_eq A y tau G' Hmpm).
          
          apply (IHC
                   (ChorEnv.add A y tau G) (Actor.Map.add A DeltaA2 D)
                   (Actor.Map.add A ThetaA2 T) (ChorEnv.remove A y G0) H7 G').

          intros A0.
          destruct (HE A0) as [HEA0A HA0EB].
          split.
          {
            apply (remove_add_partition G' G G0 A0 A y tau HEA0A Hmpm).
          }
          {
            pose proof (remove_dj_env G0 D A0 A y HA0EB) as HG0Ddj.

            assert (A0 = A \/ A0 <> A) as HeqA0A.
            tauto.
            destruct HeqA0A as [HeqA0AL | HeqA0AR].
            {
              rewrite HeqA0AL in *.
              rewrite find_add.
              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A D) DeltaA1 DeltaA2 H8) as Hpart.
              apply (partition_dj
                       (ChorEnv.find A (ChorEnv.remove A y G0))
                       (ChorEnv.find A D)
                       DeltaA2 DeltaA1
                       HG0Ddj Hpart).
            }
            { rewrite find_ab_neq2; auto. }
          }
        }
        {
          apply (IHC
                   (ChorEnv.add A y tau G) (Actor.Map.add A DeltaA2 D)
                   (Actor.Map.add A ThetaA2 T) G0 H7 (ChorEnv.add A y tau G')).       
          intros A0.
          destruct (HE A0) as [HEA0A HEA0B].
          split.
          { apply (map_subset_add A0 A y tau G' G G0 HCasesAyinG0R HEA0A). }
          { apply (partition_dj_env A0 A G0 D DeltaA1 DeltaA2 HEA0B H8). }
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
                      (ChorEnv.remove A y (ChorEnv.remove A z G0)) H8
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
                rewrite remrem in H8.
                destruct (beq A A x y) as [HbeqL _].
                destruct (HbeqL HrbiA) as [_ Heqxy].
                rewrite <- Heqxy in *.
                rewrite rmadd1 in H8.
                eauto.
              }
              {
                destruct (beq A A x z) as [HbeqL _].
                destruct (HbeqL HrbiB) as [_ Heqxz].
                rewrite <- Heqxz in *.
                rewrite rmadd1 in H8.
                eauto.
              }                
            }
            {
              unfold Insn.rebound_in in Hrbi.
              rewrite orb_false_iff in Hrbi.
              destruct Hrbi as [HrbiA HrbiB].

              rewrite rmadd2 in H8; auto.
              rewrite rmadd2 in H8; auto.
               apply (IHC tau
                        (ChorEnv.remove A y (ChorEnv.remove A z G))
                        (Actor.Map.add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                        (Actor.Map.add A ThetaA2 T) 
                        A x v H8 HWTV).
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
                 rewrite rmadd2 in H8; auto.
                 rewrite rmadd2 in H8; auto.
                 apply (IHC tau
                          (ChorEnv.remove A' y (ChorEnv.remove A' z G))
                          (Actor.Map.add A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                          (Actor.Map.add A' ThetaA2 T)
                          A x v H8 HWTV).
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
                          H8).

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
                                         (Actor.Map.add A ThetaA3 (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T))
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

        rewrite -> (addadd1 A D (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) x tau) in H8.
        rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H8.
        
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
                        H8) as HCSL.
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
                rewrite -> HDA2A in H8.                
                rewrite -> (addadd6 x tau z tau2 DeltaA2' H0) in H8.
                rewrite -> (addadd6 x tau y tau1 (Var.Map.add z tau2 DeltaA2') H) in H8.
                rewrite -> (addadd8 D A x tau (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2'))) in H8.

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
                
                specialize (IHC H8 HPartitionB HninGzy Hniny).
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
                            (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) HCasesAeqA'R) in H8.
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H8.
              
              (* specialize and apply IH *)
              specialize (IHC ThetaA1 ThetaA2 tau (ChorEnv.remove A' y (ChorEnv.remove A' z G))
                            (Actor.Map.add A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hv H8).
 
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
      }
Qed.

Definition WellScoped (T : ChorEnv.t nat) (cfg : Config.t) : Prop :=
  forall A, Config.WellScoped (ChorEnv.find A T) cfg.

Lemma ws_partition : forall M M1 M2 cfg,
    Config.WellScoped M cfg ->
    Var.Map.Partition M M1 M2 ->
    Config.WellScoped M1 cfg.
Proof.
Admitted.

Lemma nilnostep : forall T1 cfg1 l C2 T2 cfg2,
    ~ step [] T1 cfg1 l C2 T2 cfg2.
Proof.
Admitted.

Theorem preservation : forall C1 T1 cfg1 l C2 T2 cfg2,
    step C1 T1 cfg1 l C2 T2 cfg2 ->
    WellTyped (Actor.Map.empty _) (Actor.Map.empty _) T1 C1 ->
    WellScoped T1 cfg1 ->
    WellTyped (Actor.Map.empty _) (Actor.Map.empty _) T2 C2.
Proof.
  intros C1 T1 cfg1 l C2 T2 cfg2 Hstep.

  induction Hstep.

   - intros HWT Hscoped.

    inversion HWT; subst.

    eapply Send.
    { auto. }
    { 
      eapply Expr.preservation.
      { eauto. }
      { apply empty_is_empty. }
      {
        apply (empty_partition (ChorEnv.find A (Actor.Map.empty (Var.Map.t Expr.typ)))
                 DeltaA1 DeltaA2).
        apply empty_is_empty.
        auto.
      }
      {
        unfold WellScoped in Hscoped.
        specialize (Hscoped A).
        apply (ws_partition (ChorEnv.find A T) ThetaA1 ThetaA2 cfg Hscoped H13).
      }
      { 

Admitted.
