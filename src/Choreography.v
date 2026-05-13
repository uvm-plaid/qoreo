From Qoreo Require Import Base.
From Qoreo Require Expr.

From Stdlib Require Import Structures.Equalities.

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
           
    Definition bind_eqb  (Ax : bindt) (By: bindt) : bool :=
      if Actor.eq_dec (fst Ax) (fst By) then if Var.eq_dec (snd Ax) (snd By) then true else false else false.

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

    (* Fixpoint subst (A : Actor.t) (x : Var.t) (v : Expr.t) (C : t) : t :=
      match C with
      | [] => []
      | (Ins :: C') =>
          if (List.existsb (Insn.bind_eqb (A,x)) (Insn.bindings (Ins))) then
            (Insn.subst A x v Ins)::C'
          else
            (Insn.subst A x v Ins)::(subst A x v C') 
      end.*)
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
    ~ Var.Map.In y (ChorEnv.find A D) ->

    WellTyped G D T ((Insn.EPR A x B y)::C)

| Send : forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A e tau B y C,
    A <> B ->
    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.BANG tau) ->
    WellTyped (ChorEnv.add B y tau G) (Actor.Map.add A DeltaA2 D) (Actor.Map.add A ThetaA1 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->

    WellTyped G D T ((Insn.Send A e B y)::C)

| LetBang : forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A x e tau C,

    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.BANG tau) ->
    WellTyped (ChorEnv.add A x tau G) (Actor.Map.add A DeltaA2 D) (Actor.Map.add A ThetaA1 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->

    WellTyped G D T ((Insn.LetBang A x e)::C)

| LetIn : forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A x e tau C,

    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e tau ->
    WellTyped G (Actor.Map.add A (Var.Map.add x tau DeltaA2) D) (Actor.Map.add A ThetaA1 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x DeltaA2 ->

    WellTyped G D T ((Insn.Let A x e)::C)

| LetPair: forall DeltaA1 DeltaA2 ThetaA1 ThetaA2 G D T A x1 x2 tau1 tau2 e C,

    Expr.WellTyped (ChorEnv.find A G) DeltaA1 ThetaA1 e (Expr.Tensor tau1 tau2) ->
    WellTyped G (Actor.Map.add A (Var.Map.add x1 tau1 (Var.Map.add x2 tau2 DeltaA2)) D) (Actor.Map.add A ThetaA1 T) C ->

    Var.Map.Partition (ChorEnv.find A D) DeltaA1 DeltaA2 ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x1 DeltaA2 -> 
    ~ Var.Map.In x2 DeltaA2 ->

    WellTyped G D T ((Insn.LetPair A x1 x2 e)::C)
.

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

    (* I think we need a nonlinear Expr.wt_subst to proceed with this case? *)
    admit.

    fold Choreography.subst.
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
    
    admit.

    fold Choreography.subst.
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

    destruct (Actor.eq_dec A A0) eqn:Heq.

    {
      pose proof (Expr.wt_subst_bang tau (ChorEnv.find A0 G) DeltaA1 ThetaA1 x v e tau0) as HEWTS.
      eapply HEWTS.
      (*
      auto.
      auto.
      auto.
      auto.
      rewrite <- e0.
      rewrite <- extension.
      auto.
      *)
      admit.
      admit.
      admit.
    }
    { auto. }

    fold Choreography.subst.
    destruct (Insn.rebound_in A x (Insn.Let A0 x0 e)) eqn:Heq.
    { eapply HWT. }
    {
      apply IHHWT.
      auto.
    }
    
    - eapply LetPair.
    
Admitted.
    
    
Lemma wt_subst_lin : forall ThetaA1 ThetaA2 tau G D T A x v C,
    WellTyped G D (Actor.Map.add A ThetaA2 T) C ->
    Expr.Val v ->
    Expr.WellTyped (Var.Map.empty _) (Var.Map.empty _) ThetaA1 v tau ->

    ChorEnv.MapsTo A x tau D ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->

    WellTyped G D T (Choreography.subst A x v C).
Proof.
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
