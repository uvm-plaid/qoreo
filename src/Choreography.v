From Qoreo Require Import Base.
From Qoreo Require Expr.

From Stdlib Require Import Structures.Equalities.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Bool.Bool.

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

    Definition bindings (I : t) : list bindt :=
      match I with
      | Send B1 e B2 y => [(B2,y)]    
      | EPR B1 y1 B2 y2 => [(B1,y1);(B2,y2)]
      | Let B y e => [(B,y)]
      | LetBang B y e => [(B,y)]
      | LetPair B y1 y2 e => [(B,y1);(B,y2)]
    end.

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
      (* pose proof (bind_eqb_true Ax By) as Hbeqt.
      destruct Hbeqt as [HbeqtA HbeqtB].
      pose proof (bind_eqb_false Ax By) as Hbeqf.
      destruct Hbeqf as [HbeqfA HbeqfB]. *)

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

Inductive step : Choreography.t -> ChorEnv.t nat -> Config.t ->
                 Label.t ->
                 Choreography.t -> ChorEnv.t nat -> Config.t -> Prop :=

| SendC : forall refsA' A e B x C refs cfg e' refs' cfg',
    Expr.step e (ChorEnv.find A refs) cfg e' refsA' cfg' ->
    ChorEnv.Equal refs' (Actor.Map.add A refsA' refs) ->
    step  (Insn.Send A e B x :: C) refs cfg
          (Label.Loc A)
          (Insn.Send A e' B x :: C) refs' cfg'

| SendB : forall A v B x C refs cfg C',
    Expr.Val v ->
    C' = Choreography.subst B x v C ->
    step  (Insn.Send A v B x :: C) refs cfg
          (Label.Send A v B)
          C' refs cfg

| EPRB : forall q1 q2 A x B y C refs cfg C' refs' cfg',
    ChorEnv.epr A B refs cfg = (q1, q2, refs', cfg') ->

    C' = Choreography.subst A x (Expr.Var q1) (Choreography.subst B y (Expr.Var q2) C) ->

    step  (Insn.EPR A x B y :: C) refs cfg
          (Label.EPR A B) 
          C' refs' cfg'

| LetC : forall refsA' A x e C refs cfg e' refs' cfg',
    Expr.step e (ChorEnv.find A refs) cfg e' refsA' cfg' ->
    
    ChorEnv.Equal refs' (Actor.Map.add A refsA' refs) ->

    step  (Insn.Let A x e :: C) refs cfg
          (Label.Loc A)
          (Insn.Let A x e' :: C) refs' cfg'

| LetB : forall A x v C refs cfg C',
    Expr.Val v ->
    C' = Choreography.subst A x v C ->
    step  (Insn.Let A x v :: C) refs cfg
          (Label.Loc A)
          C' refs cfg

| LetBangC : forall refsA' A x e C refs cfg e' refs' cfg',
    Expr.step e (ChorEnv.find A refs) cfg e' refsA' cfg' ->
    ChorEnv.Equal refs' (Actor.Map.add A refsA' refs) ->
    step  (Insn.LetBang A x e :: C) refs cfg
          (Label.Loc A)
          (Insn.LetBang A x e' :: C) refs' cfg'

| LetBangB : forall A x e0 C refs cfg C',
    C' = Choreography.subst A x e0 C ->
    step  (Insn.LetBang A x (Expr.Bang e0) :: C) refs cfg
          (Label.Loc A)
          C' refs cfg

| LetPairC : forall refsA' A x1 x2 e C refs cfg e' refs' cfg',
    Expr.step e (ChorEnv.find A refs) cfg e' refsA' cfg' ->
    ChorEnv.Equal refs' (Actor.Map.add A refsA' refs) ->

    step  (Insn.LetPair A x1 x2 e :: C) refs cfg
          (Label.Loc A)
          (Insn.LetPair A x1 x2 e' :: C) refs' cfg'

| LetPairB : forall A x1 x2 v1 v2 C refs cfg C',
    Expr.Val v1 -> Expr.Val v2 ->
    C' = Choreography.subst A x1 v1 (Choreography.subst A x2 v2 C) ->
    step  (Insn.LetPair A x1 x2 (Expr.Pair v1 v2) :: C) refs cfg
          (Label.Loc A) 
          C' refs cfg

(* delay *)
| Delay : forall I C refs cfg C' refs' cfg' l,
    step C refs cfg l C' refs' cfg' ->
    Actor.FSet.Empty (Actor.FSet.inter (Label.actors l) (Insn.actors I)) ->
    step (I::C) refs cfg l (I::C') refs' cfg'
.


Inductive WellTyped : ChorEnv.t Expr.typ -> ChorEnv.t Expr.typ -> ChorEnv.t nat -> Choreography.t -> Prop :=
  
| Nil : forall G D T, 
    Actor.Map.Empty D ->
    Actor.Map.Empty T ->
    WellTyped G D T nil
                                
| EPR : forall G D T A x B y C,
    A <> B ->
    WellTyped G (ChorEnv.add B y Expr.QUBIT (ChorEnv.add A x Expr.QUBIT D)) T C ->

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
    WellTyped G (Actor.Map.add A (Var.Map.add x tau DeltaA2) D) (Actor.Map.add A ThetaA2 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x DeltaA2 ->

    (* Leaving this here as the analogue of shadowing requirement in Expr.WellTyped, that
       I argue is not necessary. *)
    (* WellTyped (Actor.Map.add A (Var.Map.remove x (ChorEnv.find A G)) G) D T ((Insn.Let A x e)::C) *)
    WellTyped G D T ((Insn.Let A x e)::C)

| LetPair: forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A x1 x2 tau1 tau2 e C,

    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.Tensor tau1 tau2) ->
    WellTyped G (Actor.Map.add A (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D) (Actor.Map.add A ThetaA2 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x1 DeltaA2 -> 
    ~ Var.Map.In x2 DeltaA2 ->

    WellTyped G D T ((Insn.LetPair A x1 x2 e)::C)
.

From Stdlib Require Import Morphisms. (* for Proper *)

Global Instance WellTypedProper : Proper (ChorEnv.Equal ==> ChorEnv.Equal ==> ChorEnv.Equal ==> eq ==> iff) WellTyped.
Admitted.

Lemma wt_disjoint : forall A G D T C,
    WellTyped G D T C ->
    Var.Map.Properties.Disjoint (ChorEnv.find A G) (ChorEnv.find A D).
Proof.
Admitted.
    
Lemma extension : forall A G x (tau : Expr.typ),
    ChorEnv.MapsTo A x tau G <-> Var.Map.MapsTo x tau (ChorEnv.find A G).
Proof.
  intros A G x tau.
  split.
  auto.
  auto.
Qed.

Lemma map_subset_add : forall G1 G2,
    (forall A x (tau : Expr.typ), (ChorEnv.MapsTo A x tau G1 -> ChorEnv.MapsTo A x tau G2)) ->
    (forall A x tau1 B y tau2,
        (ChorEnv.MapsTo A x tau1 (ChorEnv.add B y tau2 G1) ->
         ChorEnv.MapsTo A x tau1 (ChorEnv.add B y tau2 G2))).
Proof.
  intros G1 G2 HMA1 A x tau1 B y tau2 HMA2. 
Admitted.

Lemma weakening_gen : forall G D T C,
    WellTyped G D T C -> forall G',
      (forall A x tau, ChorEnv.MapsTo A x tau G -> ChorEnv.MapsTo A x tau G') ->
      WellTyped G' D T C.
Proof. 
  intros G D T C HWT.
  induction HWT.
  
  - intros G' HW. apply Nil; auto. 

  - intros G' HW. apply EPR; auto.

  - intros G' HW. eapply Send; auto.
    eapply Expr.weakening_gen. eauto.

    intros x tau' HEW.
    rewrite <- extension.
    apply extension in HEW.
    apply (HW A x tau') in HEW.
    auto.

    specialize (IHHWT (ChorEnv.add B y tau G')).
    apply IHHWT.
    intros A0 x tau' HWB.
    pose proof (map_subset_add G G' HW A0 x tau' B y tau) as HMA.
    auto.

    auto.
    eauto.

  - intros G' HW. eapply LetBang; eauto.

    pose proof (Expr.weakening_gen
                  (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.BANG tau) H (ChorEnv.find A G'))
      as HEW.
    apply HEW.
    intros x' tau' HVM.
    specialize (HW A x' tau').
    rewrite -> extension in HW.
    rewrite -> extension in HW.
    auto.

    specialize (IHHWT (ChorEnv.add A x tau G')).
    apply IHHWT.
    intros A0 x0 tau0 HE.
    pose proof (map_subset_add G G' HW A0 x0 tau0 A x tau) as HMA.
    auto.

  - intros G' HW. eapply LetIn; eauto.
    pose proof (Expr.weakening_gen (ChorEnv.find A G) DeltaA1 ThetaA1 e tau H (ChorEnv.find A G'))
      as HEW.
    setoid_rewrite -> extension in HW.
    auto.

  - intros G' HW. eapply LetPair; eauto.
    pose proof (Expr.weakening_gen (ChorEnv.find A G) DeltaA1 ThetaA1 e
                  (Expr.Tensor tau1 tau2) H (ChorEnv.find A G'))
      as HEW.
    setoid_rewrite -> extension in HW.
    auto.
Qed.

Lemma no_capture_add : forall A x (tau1 : Expr.typ) I G, 
    (Insn.rebound_in A x I) = false ->
    (forall B y tau2, (List.In (B,y) (Insn.bindings I)) ->
                      ChorEnv.MapsTo A x tau1 G -> ChorEnv.MapsTo A x tau1 (ChorEnv.add B y tau2 G))
.
Proof.
Admitted.

 
Lemma add_MapsTo : forall A x (tau : A) m,
  Var.Map.MapsTo x tau m ->
  Var.Map.Equal (Var.Map.add x tau m) m.
Admitted.
Require Import Setoid.

Lemma wt_subst_bang : forall tau G D T A x v C,
    WellTyped G D T C ->
    Expr.Val v ->
    Expr.WellTyped (Var.Map.empty _) (Var.Map.empty _) (Var.Map.empty _) v (Expr.BANG tau) ->
    ChorEnv.MapsTo A x tau G ->
               WellTyped G D T (Choreography.subst A x v C).
Proof.
  intros tau G D T A x v C HWT HV HWTV HA.
  induction HWT.

  - apply Nil; auto.

  - apply EPR; auto.

    fold Choreography.subst.
    destruct (Insn.rebound_in A x (Insn.EPR A0 x0 B y)).
    { auto. }
    { apply IHHWT. auto. }
  
  - eapply Send; eauto.

    + (* v must be of the form !e *)
      inversion HWTV; subst; inversion HV; subst.
      Var.Map.Tactics.vsimpl.
      destruct (Actor.FSet.MF.eq_dec A A0) eqn:Heq; subst; eauto.
      { (* A = A0 *)
        eapply Expr.wt_subst_bang; eauto.
        setoid_replace (Var.Map.add x tau (ChorEnv.find A0 G))
                with   (ChorEnv.find A0 G);
                auto.
        {
          intros z. autorewrite with var_db.
          Var.Map.Tactics.reduce_eq_dec; auto.
          symmetry; apply Var.Map.find_1; auto.
        }
      }
    
    + fold Choreography.subst.
      destruct (Insn.rebound_in A x (Insn.Send A0 e B y)) eqn:Heq.
      { eapply HWT. }
      {
        apply IHHWT.
        pose proof (no_capture_add A x tau (Insn.Send A0 e B y) G) as HNCA.
        specialize (HNCA Heq B y tau0).
        apply HNCA.
        unfold Insn.bindings.
        simpl.
        auto.
        auto.
      }

  - eapply LetBang; eauto.

    + Actor.Map.Tactics.compare A A0; eauto.
      {
        eapply Expr.wt_subst_bang; eauto.
        setoid_replace (Var.Map.add x tau (ChorEnv.find A G))
                with   (ChorEnv.find A G);
                auto.
        {
          intros z. autorewrite with var_db.
          Var.Map.Tactics.reduce_eq_dec; auto.
          symmetry; apply Var.Map.find_1; auto.
        }
      }

    + fold Choreography.subst.
      destruct (Insn.rebound_in A x (Insn.LetBang A0 x0 e)) eqn:Heq.
      { eapply HWT. }
      {
        apply IHHWT.
        pose proof (no_capture_add A x tau (Insn.LetBang A0 x0 e) G) as HNCA.
        specialize (HNCA Heq A0 x0 tau0).
        apply HNCA.
        unfold Insn.bindings.
        simpl.
        auto.
        auto.
      }

  - eapply LetIn; eauto.

    + Actor.Map.Tactics.compare A A0; eauto.
      eapply Expr.wt_subst_bang; eauto.
       setoid_replace (Var.Map.add x tau (ChorEnv.find A G))
                with   (ChorEnv.find A G);
                auto.
        {
          intros z. autorewrite with var_db.
          Var.Map.Tactics.reduce_eq_dec; auto.
          symmetry; apply Var.Map.find_1; auto.
        }

    + 
      fold Choreography.subst.
      destruct (Insn.rebound_in A x (Insn.Let A0 x0 e)) eqn:Heq.
      { eapply HWT. }
      {
        apply IHHWT.
        auto.
      }
      

  - eapply LetPair; eauto.
    
    + Actor.Map.Tactics.compare A A0; eauto.
    
      {
        pose proof (Expr.wt_subst_bang tau (ChorEnv.find A G) DeltaA1 ThetaA1 x v e (Expr.Tensor tau1 tau2)) as HEWTS.
          eapply HEWTS.
        { auto. }
        { apply Expr.weakening; auto. }
        { rewrite add_MapsTo; eauto. }
      }
    + fold Choreography.subst.
      destruct (Insn.rebound_in A x (Insn.LetPair A0 x1 x2 e)) eqn:Heq;
        eauto.

Qed.

(* Helpful Lemmas about binding equality based on Insn.beq *)
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

Lemma beq : forall A B x y,
    Insn.bind_eqb (A, x) (B, y) = true <-> (A = B /\ x = y).
Proof.
  intros.
  pose proof (Insn.bind_eqb_true (A, x) (B, y)).
  rewrite -> (Insn.beq (A, x) (B, y)) in H.
  simpl in H.
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

(* START Easily(?) proven facts *)

Lemma nin_dj : forall  {X : Type} x (M1 : Var.Map.t X) M2,
    Var.Map.Properties.Disjoint M1 M2 ->
    Var.Map.In x M2 ->
    ~ Var.Map.In x M1.
Proof.
Admitted.

Lemma partitionm_refl : forall {X : Type} (M : Var.Map.t X) M1 M2,
    Var.Map.Partition M M1 M2 -> Var.Map.Partition M M2 M1.
Proof.
Admitted.
    
Lemma add_empty_delta : forall A x tau (D : ChorEnv.t Expr.typ),
    ~ Actor.Map.Empty (ChorEnv.add A x tau D).
Proof.
Admitted.

Lemma find_add : forall {X : Type} A M (CE : ChorEnv.t X),
    (ChorEnv.find A (Actor.Map.add A M CE)) = M.
Proof.
Admitted.

Lemma find_ab_neq1 : forall {X : Type} A B x tau (CE : ChorEnv.t X),
    A <> B ->
    (ChorEnv.find A (ChorEnv.add B x tau CE)) = (ChorEnv.find A CE).
Proof.
Admitted.

Lemma find_ab_neq2 : forall {X : Type} A B M (CE : ChorEnv.t X),
    A <> B ->
    (ChorEnv.find A (Actor.Map.add B M CE)) = (ChorEnv.find A CE).
Proof.
Admitted.

Lemma find_nbeq : forall (CE : ChorEnv.t Expr.typ) A x B y tau,
    Insn.bind_eqb (A, x) (B, y) = false -> 
    ~ Var.Map.In x (ChorEnv.find A CE) ->
    ~ Var.Map.In x (ChorEnv.find A (ChorEnv.add B y tau CE)).
Proof.
Admitted.

Lemma add_find : forall (CE : ChorEnv.t Expr.typ) A x tau,
    (ChorEnv.find A (ChorEnv.add A x tau CE)) = (Var.Map.add x tau (ChorEnv.find A CE)).
Proof.
Admitted.

Lemma add_remove : forall (CE : ChorEnv.t Expr.typ) M A x tau,
    Var.Map.MapsTo x tau M ->
    (ChorEnv.add A x tau (Actor.Map.add A (Var.Map.remove x M) CE)) =
      (Actor.Map.add A M CE).
Proof.
Admitted.

Lemma nin_remove : forall (M : Var.Map.t Expr.typ) x,
    ~ (Var.Map.In x (Var.Map.remove x M)).
Proof.
Admitted.

Lemma partition_remove : forall (Delta : Var.Map.t Expr.typ) Delta1 Delta2 x tau,
    Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
    ~ Var.Map.In x Delta ->
    ~ Var.Map.In x Delta1 ->
    Var.Map.Partition Delta Delta1 (Var.Map.remove x Delta2).
Proof.
Admitted.

Lemma remove_add : forall x tau (Delta1 : Var.Map.t Expr.typ) Delta2,
    ~ Var.Map.In x Delta1 ->
    Delta2 = Var.Map.add x tau Delta1 ->
    (Var.Map.remove x Delta2) = Delta1.
Proof.
Admitted.

Lemma addadd1 : forall A (D : ChorEnv.t Expr.typ) Delta x tau,
    (Actor.Map.add A Delta (ChorEnv.add A x tau D)) = (Actor.Map.add A Delta D).
Proof.
Admitted.

Lemma addadd2 : forall {X : Type} A (T : ChorEnv.t X) Theta1 Theta2,
    (Actor.Map.add A Theta1 (Actor.Map.add A Theta2 T)) = (Actor.Map.add A Theta1 T).
Proof.
Admitted.

Lemma addadd3 :  forall (CE : ChorEnv.t Expr.typ) A x tau B M,
  A <> B -> 
  Actor.Map.add B M (ChorEnv.add A x tau CE) = ChorEnv.add A x tau (Actor.Map.add B M CE).
Proof.
Admitted.

Lemma addadd4 :  forall {X : Type} (CE : ChorEnv.t X) A MA B MB,
  A <> B -> 
  Actor.Map.add B MB (Actor.Map.add A MA CE) = Actor.Map.add A MA (Actor.Map.add B MB CE).
Proof.
Admitted.

Lemma addadd5 : forall (CE : ChorEnv.t Expr.typ) A x taux B y tauy,
    Insn.bind_eqb (B, y) (A, x) = false ->
    (ChorEnv.add A x taux (ChorEnv.add B y tauy CE)) = 
      (ChorEnv.add B y tauy (ChorEnv.add A x taux CE)).
Proof.
Admitted.

(* this lemma may help prove the preceding lemma. *)
Lemma addadd6 :  forall {X : Type} x taux y tauy (M : Var.Map.t X),
    x <> y -> 
    (Var.Map.add y tauy (Var.Map.add x taux M)) =
      (Var.Map.add x taux (Var.Map.add y tauy M)).
Proof.
Admitted.

Lemma addadd7 :  forall (CE : ChorEnv.t Expr.typ) A x tau1 y tau2 M,
    x <> y -> 
    Actor.Map.add A (Var.Map.add y tau2 M) (ChorEnv.add A x tau1 CE) =
      ChorEnv.add A x tau1 (Actor.Map.add A (Var.Map.add y tau2 M) CE).
Proof.
Admitted.

Lemma addadd8 :  forall (CE : ChorEnv.t Expr.typ) A x tau M, 
    Actor.Map.add A (Var.Map.add x tau M) CE =
      ChorEnv.add A x tau (Actor.Map.add A M CE).
Proof.
Admitted.

Lemma nin_mapl : forall (M : Var.Map.t Expr.typ)  x y tau,
    x <> y ->
    ~ Var.Map.In x M ->
    ~ Var.Map.In x (Var.Map.add y tau M).
Proof.
Admitted.

Lemma nin_mapr : forall (M : Var.Map.t Expr.typ)  x y tau,
    x <> y ->
    ~ Var.Map.In x (Var.Map.add y tau M) ->
    ~ Var.Map.In x M.
Proof.
Admitted.

Lemma nin_nxeq : forall (M : Var.Map.t Expr.typ)  x y tau,
    ~ Var.Map.In x (Var.Map.add y tau M) -> x <> y.
Proof.
Admitted.

(* contrapositive of nin_mapl with mapsto rewrite *)
Lemma map_in : forall (M : Var.Map.t Expr.typ)  x tau,
    Var.Map.MapsTo x tau M ->
    Var.Map.In x M.
Proof.
Admitted.
      

Lemma nin_nbeq : forall (CE : ChorEnv.t Expr.typ) A x tau B y,
    ~ Var.Map.In y (ChorEnv.find B (ChorEnv.add A x tau CE)) ->
    Insn.bind_eqb (A, x) (B, y) = false.
Proof.
Admitted.
      

Lemma  contra_nin_nbeq : forall (CE : ChorEnv.t Expr.typ) A x tau B y,
    Insn.bind_eqb (A, x) (B, y) = true ->
    Var.Map.In y (ChorEnv.find B (ChorEnv.add A x tau CE)).
Proof.
  intros.  
Admitted.

(* this follows by contraposition of nin_nbeq, atm I am not sure how to
   prove contrapositive. *)          
Lemma in_beq : forall (CE : ChorEnv.t Expr.typ) A x tau,
    Var.Map.In x (ChorEnv.find A (ChorEnv.add A x tau CE)).
Proof.
Admitted.

Lemma nin_nbeq_add1 : forall (CE : ChorEnv.t Expr.typ) A x B y tau,
    Insn.bind_eqb (A, x) (B, y) = false ->
    ~ Var.Map.In x (ChorEnv.find A CE) ->
      ~ Var.Map.In x (ChorEnv.find A (ChorEnv.add B y tau CE)).
Proof.
Admitted.

Lemma nin_nbeq_add2 : forall (CE : ChorEnv.t Expr.typ) A x B y tau,
    Insn.bind_eqb (A, x) (B, y) = false ->
    ~ Var.Map.In x (ChorEnv.find A (ChorEnv.add B y tau CE))->
    ~ Var.Map.In x (ChorEnv.find A CE).
Proof.
Admitted.


Lemma ini : forall (Delta : Var.Map.t Expr.typ) Delta1 Delta2 x tau,
    Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
    ~ (Var.Map.In x Delta1) ->
    (Var.Map.MapsTo x tau Delta2).
Proof.
Admitted.

Lemma nin : forall (Delta : Var.Map.t Expr.typ) Delta1' Delta1 Delta2 x tau,
    Var.Map.add x tau Delta1' = Delta1 ->
    Var.Map.Partition (Var.Map.add x tau Delta) Delta1 Delta2 ->
    ~ (Var.Map.In x Delta2) /\ Var.Map.Partition Delta Delta1' Delta2.
Proof.
Admitted.

Lemma mapsto_destruct : forall {X : Type} x tau (M : Var.Map.t X) ,
    Var.Map.MapsTo x tau M ->
    (exists M', M = Var.Map.add x tau M' /\ ~ Var.Map.In x M').
Proof.
Admitted.

(* STOP Easily(?) proven facts *) 

Lemma partitioning : forall  {X : Type} (M : Var.Map.t X) M0 M1 M2 M3,
    Var.Map.Partition M M1 M2 ->
    Var.Map.Partition M2 M0 M3 ->
    Var.Map.Partition (Var.Map.concat M1 M0) M1 M0 /\
      Var.Map.Partition (Var.Map.concat M1 M3) M1 M3 /\      
      Var.Map.Partition M (Var.Map.concat M1 M0) M3 /\
      Var.Map.Partition M M0 (Var.Map.concat M1 M3).
Proof.
Admitted.

Lemma nri_lin : forall G A x tau D T I C G' D' T',
    WellTyped G (ChorEnv.add A x tau D) T (I::C) ->
    WellTyped G' (ChorEnv.add A x tau D') T' C ->
    ~(Insn.rebound_in A x I = true).
Proof.
Admitted.

Lemma esubst_lin : forall Gamma Delta e x v tau,
    (exists Theta tau', Expr.WellTyped Gamma Delta Theta e tau') -> 
    ~ Var.Map.In x Gamma -> 
    (exists Delta', ((Var.Map.add x tau Delta') = Delta) /\
                      ~(Var.Map.In x Delta'))
    \/ (~(Var.Map.In x Delta) /\ (Expr.subst x v e) = e).
Proof.
Admitted.

Lemma csubst_lin : forall G D T C A x v,
    WellTyped G D T C ->
    ~ (Var.Map.In x (ChorEnv.find A D)) ->
    (Choreography.subst A x v C) = C.
Proof.
Admitted.

Lemma wt_subst_lin : forall C ThetaA1 ThetaA2 tau G D T A x v,
    Expr.Val v ->
    Expr.WellTyped (Var.Map.empty _) (Var.Map.empty _) ThetaA1 v tau ->
    WellTyped G (ChorEnv.add A x tau D) (Actor.Map.add A ThetaA2 T) C ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x (ChorEnv.find A G) ->
    ~ Var.Map.In x (ChorEnv.find A D) ->
    WellTyped G D T (Choreography.subst A x v C).
Proof.
  intros C. induction C as [| I C IHC ].

  (* Case C = Nil is not possible. *)
  - intros ThetaA1 ThetaA2 tau G D T A x v Hval Hv HC HinG HinD HninD.
    inversion HC; subst.
    pose proof (add_empty_delta A x tau D).
    contradiction.
    
  (* Case C = I::C' *) 
  - intros ThetaA1 ThetaA2 tau G D T A x v Hval Hv HC HinT HninG HninD.
    destruct I as [ A' e B y | A' y B z | A' y e | A' y e | A' y z e ].

    (* Case Send *)
    + inversion HC. subst.

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.
        
        assert (HSendety : (exists Theta tau', Expr.WellTyped (ChorEnv.find A G)
                                                 DeltaA1 Theta e tau')).
        exists ThetaA0.
        exists (Expr.BANG tau0).
        auto.
        
        pose proof
          (esubst_lin (ChorEnv.find A G) DeltaA1 e x v tau HSendety HninG) as HESL.
        
        (* Case x in e *) 
        destruct HESL as [HxinDA | HxninDA].          
        {
          (* prepare witness for expression e typing and partioning facts. *)
          destruct HxinDA as [DeltaA1'].
          destruct H as [HinDA HninDA'].
          rewrite <- HinDA in H8.
          pose proof
            (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
               (Var.Map.concat ThetaA1 ThetaA0) x v (Expr.BANG tau0)
               Hval Hv H8) as HWTS.
          pose proof (find_add A ThetaA2 T) as HFA.
          rewrite -> HFA in H11.
          (* partioning facts. *)
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H11)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          (* e typing witness. *)
          specialize (HWTS HPartitionA HninG HninDA').
          
          (* prepare witness for choreography C typing *)
          rewrite -> (addadd1 A D DeltaA2 x tau) in H9.
          rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H9.
          
          (* prepare hypotheses for partitioning requirements *)
          rewrite -> (add_find D A x tau) in H10.
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau HinDA H10) as Hnin.
          pose proof (csubst_lin
                        (ChorEnv.add B y tau0 G)
                        (Actor.Map.add A DeltaA2 D)
                        (Actor.Map.add A ThetaA3 T)
                        C
                        A x v H9) as HCSL.
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
                specialize (HCSL HninA).
                rewrite -> HCSL.
                eauto.
              }
              
            + auto.
              
            + auto.
        }
        (* case x not in e *)
        {
          destruct HxninDA as [HxninDAA HxninDAB].
          rewrite -> (add_find D A x tau) in H10.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H10 HxninDAA) as Hini.

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
                rewrite -> HxninDAB.
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
                              Hval Hv).
                rewrite -> (add_remove D DeltaA2 A x tau) in IHC.
                rewrite -> (addadd2 A T ThetaA3 (Var.Map.concat ThetaA1 ThetaA3)) in IHC.
                rewrite -> (addadd1 A D DeltaA2 x tau) in H9.
                rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H9.
                specialize (IHC H9).
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                specialize (IHC HPartitionB).
                rewrite -> (find_ab_neq1 A B y tau0 G H7) in IHC.
                specialize (IHC HninG).
                rewrite -> (find_add A (Var.Map.remove (elt:=Expr.typ) x DeltaA2) D) in IHC.
                specialize (IHC (nin_remove DeltaA2 x)).
                eauto.
                auto.
              }
              
            + apply (partition_remove (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H10 HninD HxninDAA).
              
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
              pose proof (nri_lin G A x tau D (Actor.Map.add A ThetaA2 T) (Insn.Send A' e B y) C
                            (ChorEnv.add B y tau0 G)
                            (Actor.Map.add A' DeltaA2 D)
                            (Actor.Map.add A' ThetaA3 (Actor.Map.add A ThetaA2 T))
                            HC H9) as Hnri.
              contradiction.
            }
            {
              (* specialize and apply IH *)
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H9.
              specialize (IHC ThetaA1 ThetaA2 tau
                            (ChorEnv.add B y tau0 G)
                            (Actor.Map.add A' DeltaA2 D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hval Hv H9).
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

      (* specialize and apply IH *)
      specialize (IHC ThetaA1 ThetaA2 tau G
                    (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A' y Expr.QUBIT D))
                    T A x v Hval Hv H8 HinT HninG HaddAB).

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

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.
        
        assert (HSendety : (exists Theta tau', Expr.WellTyped (ChorEnv.find A G) DeltaA1 Theta e tau')).
        exists ThetaA0.
        exists tau0.
        auto.
        
        pose proof
          (esubst_lin (ChorEnv.find A G) DeltaA1 e x v tau HSendety HninG) as HESL.
      
        (* Case x in e *) 
        destruct HESL as [HxinDA | HxninDA].          
        {
          (* prepare witness for expression e typing and partioning facts. *)
          destruct HxinDA as [DeltaA1'].
          destruct H as [HinDA HninDA'].
          rewrite <- HinDA in H3.
          pose proof
            (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
               (Var.Map.concat ThetaA1 ThetaA0) x v tau0
               Hval Hv H3) as HWTS.
          pose proof (find_add A ThetaA2 T) as HFA.
          rewrite -> HFA in H9.
          (* partioning facts. *)
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          (* e typing witness. *)
          specialize (HWTS HPartitionA HninG HninDA').

          (* prepare witness for choreography C typing *)
          rewrite -> (addadd1 A D (Var.Map.add y tau0 DeltaA2) x tau) in H7. 
          rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H7.

          (* prepare hypotheses for partitioning requirements *)
          rewrite -> (add_find D A x tau) in H8.
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau HinDA H8) as Hnin.
          pose proof (csubst_lin
                        G
                        (Actor.Map.add A  (Var.Map.add y tau0 DeltaA2) D)
                        (Actor.Map.add A ThetaA3 T)
                        C
                        A x v H7) as HCSL.
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
                specialize (HCSL (nin_mapl DeltaA2 x y tau0 (nbeqeq A x y Heq) HninA)).
                rewrite -> HCSL.
                eauto.
              }
              
            + auto.
              
            + auto.

            + auto.
        }
        (* case x not in e *)
        {
          destruct HxninDA as [HxninDAA HxninDAB].
          rewrite -> (add_find D A x tau) in H8.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H8 HxninDAA) as Hini.

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
                rewrite -> HxninDAB.
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
                              G
                              (Actor.Map.add A (Var.Map.add y tau0 DeltaA2') D)
                              (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T)
                              A x v Hval Hv).
                
                unfold ChorEnv.add in IHC.
                rewrite -> (find_add A (Var.Map.add y tau0 DeltaA2') D) in IHC.
                rewrite -> (addadd2 A D (Var.Map.add x tau (Var.Map.add y tau0 DeltaA2'))) in IHC.
                rewrite -> (addadd2 A T ThetaA3 (Var.Map.concat ThetaA1 ThetaA3)) in IHC.
                specialize (IHC H7).

                unfold Insn.rebound_in in Heq.
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                specialize (IHC HPartitionB HninG
                              (nin_mapl DeltaA2' x y tau0 (nbeqeq A x y Heq) HDA2B)).                

                eauto.

                apply (nbeqeq A x y Heq).
              }
              
            + pose proof (partition_remove (ChorEnv.find A D) DeltaA1 DeltaA2 x tau
                            H8 HninD HxninDAA).
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
              specialize (IHC ThetaA1 ThetaA2 tau G
                            (Actor.Map.add A' (Var.Map.add y tau0 DeltaA2) D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hval Hv H7).
 
              rewrite -> (find_ab_neq2 A A' ThetaA3 T HCasesAeqA'R) in IHC.
              rewrite -> (find_ab_neq2 A A' (Var.Map.add y tau0 DeltaA2) D HCasesAeqA'R) in IHC.

              specialize (IHC HinT HninG HninD).
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
        
        assert (HSendety : (exists Theta tau', Expr.WellTyped (ChorEnv.find A G)
                                                 DeltaA1 Theta e tau')).
        exists ThetaA0.
        exists (Expr.BANG tau0).
        auto.
        
        pose proof
          (esubst_lin (ChorEnv.find A G) DeltaA1 e x v tau HSendety HninG) as HESL.
        
        (* Case x in e *) 
        destruct HESL as [HxinDA | HxninDA].          
        {
          (* prepare witness for expression e typing and partioning facts. *)
          destruct HxinDA as [DeltaA1'].
          destruct H as [HinDA HninDA'].

          (* expression typing *)
          rewrite <- HinDA in H6.
          
          (* partioning facts. *)
          rewrite -> (find_add A ThetaA2 T) in H9.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          rewrite -> (add_find D A x tau) in H8.
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau HinDA H8) as Hnin.
          destruct Hnin as [HninA HninB].
               
          eapply LetBang.
          
          + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
            {
            
              pose proof
                (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
                   (Var.Map.concat ThetaA1 ThetaA0) x v (Expr.BANG tau0)
                   Hval Hv H6 HPartitionA HninG HninDA') as HWTS.
              eauto.
            }
            {
              contradiction.
            }

          +  fold Choreography.subst.
             destruct (Insn.rebound_in A x) eqn:Heq.
             { eauto.}
             {
               pose proof (csubst_lin
                             (ChorEnv.add A y tau0 G)
                             (Actor.Map.add A DeltaA2 D)
                             (Actor.Map.add A ThetaA3 T)
                             C
                             A x v H7) as HCSL.
               rewrite -> (find_add A DeltaA2 D) in HCSL.
                       
               specialize (HCSL HninA).
               rewrite -> HCSL.
               eauto.
             }
             
          + auto.

          + auto.
        }
        (* case x not in e *)
        {
          destruct HxninDA as [HxninDAA HxninDAB].
          rewrite -> (add_find D A x tau) in H8.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H8 HxninDAA) as Hini.

          
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
                rewrite -> HxninDAB.
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

                pose proof (wt_disjoint A (ChorEnv.add A x tau0 G) (Actor.Map.add A DeltaA2 D)
                              (Actor.Map.add A ThetaA3 T) C H7) as Hwtdj.
                rewrite (find_add A DeltaA2 D) in Hwtdj.

                (* This does not go through with tauto. 
                   pose proof (nin_nbeq G A x tau0 A x).
                   assert (Insn.bind_eqb (A, x) (A, x) = true ->
                       Var.Map.In (elt:=Expr.typ) x (ChorEnv.find A (ChorEnv.add A x tau0 G))).
                   tauto. *)

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
                              Hval Hv).

                rewrite <- HCasesAeqA'L in IHC.
                rewrite -> (addadd2 A T ThetaA3 (Var.Map.concat ThetaA1 ThetaA3)) in IHC.
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                rewrite -> (find_add A DeltaA2' D) in IHC.
                pose proof (nin_nbeq_add1 G A x A y tau0 Heq HninG) as HninGy.
                
                specialize (IHC H7 HPartitionB HninGy HDA2B).

                eauto.
              }

            +  assert (Var.Map.add x tau DeltaA2' = DeltaA2) as Hdel; auto.
               pose proof (partitionm_refl (Var.Map.add x tau (ChorEnv.find A D)) DeltaA1 DeltaA2 H8) as Hpart.
               pose proof (nin (ChorEnv.find A D) DeltaA2' DeltaA2 DeltaA1 x tau Hdel Hpart) as Hnin.
               destruct Hnin as [HninA HninB].
               pose proof (partitionm_refl (ChorEnv.find A D) DeltaA2' DeltaA1 HninB).
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
                            A x v Hval Hv H7).
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

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.

        rewrite -> (addadd1 A D (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) x tau) in H8.
        rewrite -> (addadd2 A T ThetaA3 ThetaA2) in H8.
        
        assert (HSendety : (exists Theta tau', Expr.WellTyped (ChorEnv.find A G)
                                                 DeltaA1 Theta e tau')).
        exists ThetaA0.
        exists (Expr.Tensor tau1 tau2).
        auto. 
        
        pose proof
          (esubst_lin (ChorEnv.find A G) DeltaA1 e x v tau HSendety HninG) as HESL.

        (* Case x in e *) 
        destruct HESL as [HxinDA | HxninDA].          
        {
          (* prepare witness for expression e typing and partioning facts. *)
          destruct HxinDA as [DeltaA1'].
          destruct H as [HinDA HninDA'].
          rewrite <- HinDA in H4.
          pose proof
            (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
               (Var.Map.concat ThetaA1 ThetaA0) x v (Expr.Tensor tau1 tau2)
               Hval Hv H4) as HWTS.
          pose proof (find_add A ThetaA2 T) as HFA.
          rewrite -> HFA in H10.
          (* partioning facts. *)
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H10)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          (* e typing witness. *)
          specialize (HWTS HPartitionA HninG HninDA').

          (* prepare hypotheses for partitioning requirements *)
          rewrite -> (add_find D A x tau) in H9.
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau HinDA H9) as Hnin.
          pose proof (csubst_lin
                        G
                        (Actor.Map.add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                        (Actor.Map.add A ThetaA3 T)
                        C
                        A x v H8) as HCSL.
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
                                    x y tau1 (nbeqeq A x y HeqA) Hninz)).
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
          destruct HxninDA as [HxninDAA HxninDAB].
          rewrite -> (add_find D A x tau) in H9.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H9 HxninDAA) as Hini.

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
                rewrite -> HxninDAB.
                eauto.
              }
              { auto. }

            + fold Choreography.subst.
              destruct (Insn.rebound_in A x (Insn.LetPair A y z e)) eqn:Heq.
              (* impossible case x = y *)
              {
                Check beqeq.
                Check map_in.
                unfold Insn.rebound_in in Heq.

                (* NOTE: nice boolean eq rewrite Lemma from Bool.Bool *)
                rewrite orb_true_iff in Heq.
                destruct Heq as [HeqA HeqB].
                
                pose proof (beqeq A x y Heq).
                pose proof (map_in DeltaA2 x tau Hini).
                rewrite <- H in H11.
                contradiction.
               
Admitted.

    
(* placeholder for well-formedness definition *)
Definition  WellFormed (cfg : Config.t) (C : ChorEnv.t nat) : Prop := True.

Theorem preservation : forall C1 T1 cfg1 l C2 T2 cfg2,
  step C1 T1 cfg1 l C2 T2 cfg2 ->
  WellFormed cfg1 T1 ->
  WellTyped (Actor.Map.empty _) (Actor.Map.empty _) T1 C1 ->
  WellFormed cfg2 T2 /\ WellTyped (Actor.Map.empty _) (Actor.Map.empty _) T2 C2.
Proof.
Admitted.
