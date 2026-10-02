
From QuantumLib Require Import Matrix Pad Quantum.
From Stdlib Require Import String Morphisms (* for Proper *).
Require Import Setoid. (* for setoid_replace with *)
From Qoreo.Base Require Var Actor Config.

Module ChorEnv.
    Definition t T := Actor.Map.t (Var.Map.t T).
    
    Definition find {T} (A : Actor.t) (G : t T) : Var.Map.t T :=
        match Actor.Map.find A G with
        | Some D => D
        | None => Var.Map.empty _
        end.

    Definition empty {T} : ChorEnv.t T := Actor.Map.empty _.

    (* equivalence of ChorEnv.t *)
    Definition Equal {T} (G1 G2 : t T) : Prop := 
    (*Actor.Map.Equiv (Var.Map.Equal) G1 G2.*)
      forall A, Var.Map.Equal (find A G1) (find A G2).

    Definition Empty {T} (G : t T) : Prop :=
      forall A, Var.Map.Equal (find A G) (Var.Map.empty _).

    Definition add {T} (A : Actor.t) (x : Var.t) (tau : T) (G : t T) : t T :=
        let D := find A G in
        Actor.Map.add A (Var.Map.add x tau D) G.


    Definition remove {T} (A : Actor.t) (x : Var.t) (CE : t T) :  t T :=
        (Actor.Map.add A (Var.Map.remove x (find A CE)) CE).

    Definition MapsTo {T} (A : Actor.t) (x : Var.t) (tau : T) (G : t T) : Prop :=
      Var.Map.MapsTo x tau (find A G).


    Definition WellScoped (T : ChorEnv.t nat) (cfg : Config.t) : Prop :=
      forall A, Config.WellScoped (ChorEnv.find A T) cfg.

    
    Definition epr (A B : Actor.t) (refs : t nat) (cfg : Config.t)
                  : Var.t * Var.t * t nat * Config.t :=
      match Config.epr_cfg cfg with
      | (idx1, idx2, cfg') =>
        let x1 := (* Var.fresh (find A refs) in*) idx1 in
        let refs' := add A x1 idx1 refs in
        let x2 := (*Var.fresh (find B refs') in*) idx2 in
        let refs'' := add B x2 idx2 refs' in

        (x1, x2, refs'', cfg')
      end.

    Ltac simplify := repeat (Actor.simplify; Var.simplify).


    (** properties of find *)

    Lemma find_add : forall T A B x (a : T) G,
      (ChorEnv.find A (ChorEnv.add B x a G))
      = (if Actor.eq_dec A B then Var.Map.add x a (ChorEnv.find A G) else ChorEnv.find A G).
    Proof.
      intros.
      unfold ChorEnv.add, ChorEnv.find.
      autorewrite with actor_db.
      repeat Actor.Map.Tactics.reduce_eq_dec.
      + destruct (Actor.Map.find B G); try reflexivity.
      + destruct (Actor.Map.find B G); try reflexivity.
    Qed.
    #[global] Hint Rewrite find_add : var_db.


    Lemma find_add' : forall {T} A B M (M' : t T),
      (find A (Actor.Map.add B M M'))
      = (if Actor.eq_dec A B then M else find A M').
    Proof.
      intros.
      unfold find.
      Actor.simplify.
    Qed.
    #[global] Hint Rewrite @find_add' : var_db.

    Lemma find_remove : forall {T} A B x (G : t T),
      (find A (ChorEnv.remove B x G))
      = (if Actor.eq_dec A B then Var.Map.remove x (find B G) else find A G).
    Proof.
      intros.
      unfold find. unfold remove.
      autorewrite with actor_db.
      repeat Actor.Map.Tactics.reduce_eq_dec; try reflexivity.
    Qed.
    #[global] Hint Rewrite @find_remove : var_db.

    Lemma find_remove' : forall T A B (G : t T),
      (find A (Actor.Map.remove B G))
      = if Actor.eq_dec A B then Var.Map.empty _ else find A G.
    Proof.
      intros T A B G.
      unfold find. Actor.simplify.
    Qed.
    #[global] Hint Rewrite find_remove' : var_db.

    Global Instance findProper : forall T, Proper (eq ==> Equal ==> Var.Map.Equal) (@find T).
    Proof.
      intros T ? A ? env1 env2 Henv; subst.
      unfold Equal in Henv.
      apply Henv.
    Qed.

    Lemma find_concat : forall A T (M1 M2 : t T),
      find A (Actor.Map.concat M1 M2) =
        match Actor.Map.find A M1 with
        | Some D1 => D1
        | None => find A M2
        end.
    Proof.
      intros. unfold find.
      Actor.simplify.
      destruct (Actor.Map.find A M1); auto.
    Qed.
    #[global] Hint Rewrite find_concat : var_db.

    Lemma find_setminus : forall A X T (M : t T),
      find A (Actor.Map.setminus X M)
      = if Actor.Map.FSetProofs.in_dec A X
        then Var.Map.empty _
        else find A M.
  Proof.
    intros.
    unfold find.
    Actor.simplify.
    destruct (Actor.Map.FSetProofs.in_dec A X); auto.
  Qed.
  #[global] Hint Rewrite find_setminus : var_db.

  Lemma mapsto_find : forall T A D (M : t T),
    Actor.Map.MapsTo A D M ->
    find A M = D.
  Proof.
    intros T A D M H.
    Actor.reflect_find.
    unfold find.
    rewrite H. auto.
  Qed.

  Lemma find_empty : forall T A,
    find A (Actor.Map.empty (Var.Map.t T)) = Var.Map.empty _.
  Proof.
    intros.
    unfold find. Actor.simplify.
  Qed.
  #[global] Hint Rewrite find_empty : var_db.


    (** Properties of ChorEnv.add *)
      
    Global Instance add_Proper : forall T, Proper (eq ==> eq ==> eq ==> Equal ==> Equal) (@add T).
    Proof.
      intros T ? A ? ? x ? ? tau ? G1 G2 HG; subst.
      unfold add.
      unfold Equal in *. intros B.
      simplify.
      rewrite HG.
      reflexivity.
    Qed.

    Global Instance actor_add_Proper : forall T, 
      Proper  (eq ==> @Var.Map.Equal T ==> Equal ==> @Equal T)
              (@Actor.Map.add (Var.Map.t T)).
    Proof.
      intros T ? A ? D1 D2 HD T1 T2 HT; subst.
      intros B.
      Var.simplify.
      Actor.Map.Tactics.compare B A; auto.
    Qed.

  (* singleton, concat, domain, setminus, remove, add, In, MapsTo, empty, Empty, disjoint, partition *)

    (* Properties of Equal *)

    Global Instance Equal_refl : forall T, Reflexive (@Equal T).
    Proof.
      intros T x.
      intros B. reflexivity.
    Qed.

    Global Instance Equal_symm : forall T, Symmetric (@Equal T).
    Proof.
      intros T env1 env2 Heq.
      intros B. symmetry. apply Heq.
    Qed.

    Global Instance Equal_trans : forall T, Transitive (@Equal T).
    Proof.
      intros T env1 env2 env3 H1 H2.
      intros B.
      rewrite H1. apply H2.
    Qed.

    Lemma actor_map_Equal : forall T (M1 M2 : t T),
      Actor.Map.Equal M1 M2 -> Equal M1 M2.
    Proof.
      intros T M1 M2 Heq.
      intros B. unfold find.
      rewrite Heq. reflexivity.
    Qed.

    Lemma actor_map_Equal' : forall T (M1 M2 N1 N2 : t T),
      Actor.Map.Equal M1 M2 ->
      Actor.Map.Equal N1 N2 ->
      Equal M1 N1 ->
      Equal M2 N2.
    Proof.
      intros T M1 M2 N1 N2 HeqM HeqN Heq.
      apply actor_map_Equal in HeqM.
      apply actor_map_Equal in HeqN.
      rewrite <- HeqM.
      rewrite <- HeqN.
      auto.
    Qed.

    Global Instance Equal_Proper : forall T, Proper (Actor.Map.Equal ==> Actor.Map.Equal ==> iff) (@Equal T).
    Proof.
      intros T M1 M2 HM N1 N2 HN.
      split; intros.
      eapply actor_map_Equal'; eauto.
      eapply actor_map_Equal'; eauto; symmetry; auto.
    Qed.

    (** Properties of remove *)

    Global Instance remove_Proper : forall T, Proper (eq ==> eq ==> Equal ==> Equal) (@remove T).
    Proof.
      intros T ? A ? ? x ? G1 G2 HG; subst.
      unfold remove.
      unfold Equal in *. intros B.
      simplify.
      rewrite HG.
      reflexivity.
    Qed.


    Global Instance actor_remove_Proper : forall T, 
      Proper  (eq ==> Equal ==> @Equal T)
              (@Actor.Map.remove (Var.Map.t T)).
    Proof.
      intros T ? A ? T1 T2 HT; subst.
      intros B.
      Var.simplify.
      Actor.Map.Tactics.compare B A; auto.
      reflexivity.
    Qed.

    (** Properties of MapsTo *)

    Global Instance MapsTo_Proper : forall T,
        Proper (eq ==> eq ==> eq ==> Equal ==> iff) (@MapsTo T).
    Proof.
      intros T ? A ? ? x ? ? tau ? G1 G2 HG; subst.
      unfold MapsTo.
      rewrite HG.
      reflexivity.
    Qed.

    Lemma MapsTo_add : forall T A x (tau : T) G,
      ChorEnv.MapsTo A x tau G ->
      ChorEnv.Equal (ChorEnv.add A x tau G)
                    G.
    Proof.
      intros T A x tau G H.
      unfold ChorEnv.Equal.
      unfold Actor.Map.Equiv, ChorEnv.add, ChorEnv.MapsTo, ChorEnv.find in *.
      intros B.
      Actor.simplify.
      destruct (Actor.Map.find A G) as [D | ] eqn:Hfind;
        Var.simplify.
      Var.solve.
    Qed.


    (* singleton, concat, domain, setminus, remove, add, In, MapsTo, empty, Empty, disjoint, partition *)



    (* ChorEnv + singleton *)


  (** Facts about Empty *)

    Lemma Empty_empty : forall T (G : t T),
      Empty G ->
      Equal G (Actor.Map.empty _).
    Proof.
      intros T G H. unfold Empty in H. unfold Equal.
      intros A. rewrite H.
      rewrite find_empty.
      reflexivity.
    Qed.

    Lemma Empty_find : forall T (G : t T) A,
      Empty G ->
      Var.Map.Equal (find A G) (Var.Map.empty _).
    Proof.
      intros T G A H. apply H.
    Qed.

  Global Instance EmptyProper : forall T,
    Proper (ChorEnv.Equal ==> iff) (@ChorEnv.Empty T).
  Proof.
    intros T G1 G2 HG.
    split; intros Hempty.
    * intros A. rewrite <- HG. auto.
    * intros A. rewrite HG. auto.
  Qed.

  (* Interaction between add/remove/empty*)

    Lemma ce_add_empty : forall T (m : ChorEnv.t T) A,
      ChorEnv.Equal
        (Actor.Map.add A (Var.Map.empty _) m)
        (Actor.Map.remove A m).
    Proof.
      intros T m A.
      intros B. ChorEnv.simplify.
    Qed.
    #[global] Hint Rewrite ce_add_empty : var_db.

    Lemma addadd1 : forall {T} A (D : ChorEnv.t T) Delta x tau,
        ChorEnv.Equal (Actor.Map.add A Delta (ChorEnv.add A x tau D)) (Actor.Map.add A Delta D).
    Proof.
      intros.
      unfold ChorEnv.add.
      Actor.simplify. 
    Qed.
    #[global] Hint Rewrite @addadd1 : var_db.

    Lemma addadd2 : forall {X : Type} A (T : ChorEnv.t X) Theta1 Theta2,
        ChorEnv.Equal (Actor.Map.add A Theta1 (Actor.Map.add A Theta2 T)) 
                      (Actor.Map.add A Theta1 T).
    Proof.
      intros.
      Actor.simplify.
    Qed.
    #[global] Hint Rewrite @addadd2 : var_db.


    Lemma find_add_env : forall {X : Type} A (CE : ChorEnv.t X),
        ChorEnv.Equal (Actor.Map.add A (ChorEnv.find A CE) CE) CE.
    Proof.
      intros X A CE B.
      ChorEnv.simplify.
    Qed.
    #[global] Hint Rewrite @find_add_env : var_db.


    Lemma remove_empty : forall A x T,
      ChorEnv.Equal (ChorEnv.remove A x (Actor.Map.empty (Var.Map.t T))) (Actor.Map.empty _).
    Proof.
      intros. intros B. ChorEnv.simplify.
    Qed.
    #[global] Hint Rewrite remove_empty : var_db.


    Lemma actor_remove_empty : forall A,
        ChorEnv.Equal (Actor.Map.remove A (Actor.Map.empty (Var.Map.t nat))) (Actor.Map.empty _).
    Proof. intros. ChorEnv.simplify. Qed.
    #[global] Hint Rewrite actor_remove_empty : var_db.


    Lemma ce_actor_add_neq_sym : forall A B X DA DB (T : ChorEnv.t X),
      A <> B ->
      ChorEnv.Equal (Actor.Map.add A DA (Actor.Map.add B DB T))
                    (Actor.Map.add B DB (Actor.Map.add A DA T)).
    Proof.
      intros.
      intros D.
      ChorEnv.simplify.
    Qed.


    Lemma ce_actor_remove_add : forall {X} A D (m : ChorEnv.t X),
      ChorEnv.Equal (Actor.Map.remove A (Actor.Map.add A D m))
                    (Actor.Map.remove A m).
    Proof.
      intros. intros B. ChorEnv.simplify.
    Qed.
    #[global] Hint Rewrite @ce_actor_remove_add : var_db.


  (* find, add, remove, mapsto, epr*)


  Ltac reflect_find :=
    repeat match goal with
    | [ H : Actor.Map.MapsTo ?A ?D ?M |- _ ] =>
      apply mapsto_find in H;
      rewrite H in *
    | [ H : Empty _ |- _ ] =>
      apply Empty_empty in H;
      rewrite H in *
    | [ |- Empty _ ] =>
      let A := fresh "A" in
      intros A
    | [ |- Equal _ _ ] =>
      let A := fresh "A" in
      intros A
    end.
  Ltac solve := reflect_find; simplify.

  (** Properties of epr *)

  
  Lemma chor_epr_eq : forall T2 T1 T1' A B cfg cfg' q1 q2,
    ChorEnv.epr A B T1 cfg = (q1, q2, T1', cfg') ->
    ChorEnv.Equal T1 T2 ->
    exists T2', ChorEnv.Equal T2' T1' /\ ChorEnv.epr A B T2 cfg = (q1, q2, T2', cfg').
  Proof.
    intros ? ? ? ? ? ? ? ? ? Hepr HT.
    unfold epr in *.
    destruct (Config.epr_cfg cfg) as [[q1' q2'] cfg0] eqn:Hcfg.
    remember (Var.fresh (find A T2)) as x eqn:Hx.
    replace (Var.fresh (find A T1)) with x in *.
    2:{ subst. rewrite HT. auto. }
    remember (Var.fresh (find B (add A x q1' T1))) as y eqn:Hy.
    replace ((Var.fresh (find B (add A x q1' T2)))) with y in *.
    2:{ subst. rewrite HT. auto. }

    inversion Hepr; subst; clear Hepr.
    eexists. split.
    2:{ reflexivity. }
    rewrite HT. reflexivity.
  Qed.

  Lemma epr_Proper : Proper (eq ==> eq ==> ChorEnv.Equal ==> eq ==> RelationPairs.RelProd (RelationPairs.RelProd eq ChorEnv.Equal) eq) ChorEnv.epr.
  Proof.
    intros ? A ? ? B ? T1 T2 HT ? cfg ?; subst.
    unfold ChorEnv.epr.
    split; split; simpl; unfold RelationPairs.RelCompFun; simpl; auto.
    * rewrite HT. reflexivity.
  Qed.


    (** Properties of WellScoped *)


    Global Instance WellScopedProper : Proper (ChorEnv.Equal ==> eq ==> iff) WellScoped.
    Proof.
      intros T1 T2 HT ? cfg ?; subst.
      split; intros HWS;
        intros A; specialize (HWS A);
        specialize (HT A);
        rewrite HT in *; auto.
    Qed.


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


    (*From QuantumLib Require Import Matrix Pad Quantum.*)
    Lemma WF_Matrix_epr : forall A B T cfg q1 q2 T0 cfg',
      ChorEnv.epr A B T cfg = (q1, q2, T0, cfg') ->
      WF_Matrix (Config.qstate cfg) ->
      WF_Matrix (Config.qstate cfg').
    Proof.
      intros A B T cfg q1 q2 T0 cfg' H HWF.
      inversion H; subst; clear H. simpl.
      assert (WF_Matrix EPRpair).
      { apply WF_EPRpair. }
      remember (EPRpair × (EPRpair †)) as rho eqn:Hrho.
      assert (WF_Matrix rho).
      { subst. auto with wf_db. }
      apply WF_kron; auto.
      {
        repeat rewrite Nat.add_0_r.
        repeat rewrite double_pow.
        replace 4%nat with (2^2)%nat by auto.
        rewrite <- Nat.pow_add_r.
        f_equal.
        lia.
      }
      {
        repeat rewrite Nat.add_0_r.
        repeat rewrite double_pow.
        replace 4%nat with (2^2)%nat by auto.
        rewrite <- Nat.pow_add_r.
        f_equal.
        lia.
      }
    Qed.
  Close Scope R_scope.


  Lemma WellScoped_epr : forall A B T cfg q1 q2 T0 cfg',
    ChorEnv.epr A B T cfg = (q1, q2, T0, cfg') ->
    A <> B ->
    WellScoped T cfg ->
    WellScoped T0 cfg'.
  Proof.
    intros A B T cfg q1 q2 T0 cfg' H Hneq HWS.
    intros D.
    specialize (HWS D).
    destruct HWS as [HWF HWS].
    split.
    * eapply WF_Matrix_epr; eauto.
    * intros y Hy.
      inversion H; subst; clear H.
      autorewrite with var_db in Hy.
      Actor.Map.Tactics.compare D B; subst; simpl.
      { (* D = B *)
        ChorEnv.simplify.
        destruct Hy as [Hy | Hy]; subst.
        { (* y = S (dim cfg) *)
          lia.
        }
        {
          (* y ∈ find D T *)
          apply HWS in Hy.
          lia.
        }
      }
      Actor.Map.Tactics.compare D A; subst; simpl.
      { (* D = A *)
        ChorEnv.simplify.
        destruct Hy as [Hy | Hy]; subst.
        { (* y = dim cfg *)
          lia.
        }
        {
          (* y ∈ find D T *)
          apply HWS in Hy.
          lia.
        }
      }
      { (* D <> A, D <> B *)
        apply HWS in Hy; auto.
      }
  Qed.


End ChorEnv.