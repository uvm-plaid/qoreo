From Qoreo.Base Require Import Map.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia. (* lia *)


Create HintDb var_db.

  Module V := OrderedTypeEx.UOT_to_OT (OrderedTypeEx.Nat_as_OT).
  Include V.
  Module Map := FMap V.
  Module FSet := Map.S.

  Definition fresh {A} (m : Map.t A) :=
    let f := fun x _ z_fresh => if Nat.leb z_fresh x then (x+1)%nat else z_fresh in
    Map.fold f m 0%nat.

  
  Ltac simplify :=
    repeat
    (autorewrite with var_db in *;
      Map.Tactics.vsimpl;
      repeat Map.Tactics.reduce_eq_dec;
      try (first [tauto | reflexivity | discriminate | auto | intuition]; fail)).

  (* instantiate this for each relevant hint database *)
  Ltac reflect_find :=
    repeat (
      Map.Proofs.reflect_find_body;
      autorewrite with var_db in *;
      repeat Map.Tactics.reduce_eq_dec
    ).
  Ltac solve := 
    repeat (reflect_find; first [tauto | discriminate | auto; fail | intuition]).

  (* Global var_db hints: instantiations of FMap_fun's local qoreo_db hints for Var.Map *)
  #[global] Hint Rewrite Map.Properties.F.add_mapsto_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.empty_mapsto_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.add_in_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.map_o : var_db.
  #[global] Hint Rewrite Map.Properties.F.remove_o : var_db.
  #[global] Hint Rewrite Map.Properties.F.add_o : var_db.
  #[global] Hint Rewrite Map.Properties.F.empty_o : var_db.
  #[global] Hint Rewrite Map.Properties.F.map_in_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.remove_mapsto_iff : var_db.
  #[global] Hint Rewrite Map.Properties.F.empty_in_iff : var_db.

  #[global] Hint Rewrite Map.Properties.F.remove_in_iff : var_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_1 : var_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_2 : var_db.

  #[global] Existing Instance Map.Proofs.singletonProper.
  #[global] Existing Instance Map.Proofs.concatProper.
  #[global] Existing Instance Map.Proofs.domainProper.
  #[global] Existing Instance Map.FSetProofs.setminusProper.

  #[global] Hint Rewrite Map.Proofs.concat_find : var_db.
  #[global] Hint Rewrite Map.Proofs.concat_in : var_db.
  #[global] Hint Rewrite @Map.Proofs.concat_add_l : var_db.
  #[global] Hint Rewrite @Map.Proofs.map_concat : var_db.
  #[global] Hint Rewrite Map.Proofs.fset_in_union : var_db.
  #[global] Hint Rewrite Map.Proofs.remove_map : var_db.
  #[global] Hint Rewrite Map.Proofs.remove_add : var_db.
  #[global] Hint Rewrite Map.Proofs.remove_empty : var_db.
  #[global] Hint Rewrite @Map.Proofs.map_add : var_db.
  #[global] Hint Resolve @Map.Proofs.empty_map_equal : var_db.
  #[global] Hint Rewrite @Map.Proofs.empty_map_empty : var_db.
  #[global] Hint Rewrite @Map.Proofs.concat_disjoint : var_db.
  #[global] Hint Rewrite Map.Proofs.add_remove_eq : var_db.
  #[global] Hint Rewrite Map.Proofs.add_add_eq : var_db.
  #[global] Hint Rewrite Map.Proofs.singleton_empty : var_db.
  #[global] Hint Rewrite Map.Proofs.remove_remove : var_db.

  #[global] Hint Rewrite @Map.FSetProofs.setminus_mapsto_iff : var_db.
  #[global] Hint Rewrite Map.FSetProofs.setminus_add : var_db.
  #[global] Hint Rewrite Map.FSetProofs.setminus_singleton : var_db.
  #[global] Hint Rewrite Map.FSetProofs.find_setminus : var_db.
  #[global] Hint Rewrite Map.FSetProofs.add_mem_iff : var_db.
  #[global] Hint Rewrite Map.FSetProofs.singleton_mem_iff : var_db.

  (* separate out more expensive resolves into extra_var_db *)
  #[global] Hint Resolve Map.empty_1 : var_db.  
  #[global] Hint Resolve Map.Properties.Partition_sym : extra_var_db.
  #[global] Hint Resolve @Map.Proofs.singleton_remove : var_db.
  #[global] Hint Resolve Map.Proofs.add_mapsto : extra_var_db.
  #[global] Hint Resolve Map.Proofs.disjoint_empty_1 Map.Proofs.disjoint_empty_2 : var_db.
  #[global] Hint Resolve Map.Proofs.disjoint_in_l Map.Proofs.disjoint_in_r : var_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_l : var_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_r : var_db.
  #[global] Hint Resolve Map.M.remove_1 : var_db.
  #[global] Hint Resolve Map.Proofs.disjoint_sym : extra_var_db.
  #[global] Hint Resolve Map.Proofs.concat_assoc : extra_var_db.

  (*
  #[global] Hint Extern 4 (Map.Partition (Map.concat _ _) _ _) => Map.Proofs.partition_concat : extra_var_db.
  #[global] Hint Extern 4 (Map.Partition _ (Map.concat _ _) _) => Map.Tactics.partition_concat : extra_var_db.
  #[global] Hint Extern 4 (Map.Partition _ _ (Map.concat _ _)) => Map.Tactics.partition_concat : extra_var_db.
  *)

  #[global] Hint Rewrite Map.FSetProperties.inter_iff : var_db.
  #[global] Hint Rewrite Map.MProofs.FSetProperties.add_iff: var_db.
  #[global] Hint Rewrite Map.FSetProperties.singleton_iff : var_db.
  #[global] Hint Rewrite Map.FSetProperties.add_iff : var_db.
  #[global] Hint Rewrite Map.FSetProperties.remove_iff : var_db.

  (** Proofs about fresh variables *)

  (* The operations on configurations form Proper relations *)
  Global Instance freshProper : forall A, 
      Proper (@Var.Map.Equal A ==> eq) Var.fresh.
  Proof.

    intros A refs1 refs2 Hrefs.
    unfold Var.fresh.
    apply Var.Map.Properties.fold_Equal; auto.
    + intros ? ? ? ? ? ? ? ? ?; subst; auto.
      repeat rewrite H1. reflexivity.
    + intros ? ? ? ? ? ?.
    
      destruct (Nat.leb (k' + 1) k) eqn:H_k'_k;
      destruct (Nat.leb a k') eqn:Hk';
      destruct (Nat.leb a k) eqn:Hk;
      destruct (Nat.leb (k+1) k') eqn:H_k_k';
      auto;
        try 
        (try rewrite Nat.leb_le in *;
        try rewrite Nat.leb_nle in *;
        lia).
      * rewrite H_k'_k; auto. reflexivity.
      * reflexivity.
      * rewrite Hk'; reflexivity.
      * rewrite H_k'_k; reflexivity.
      * rewrite H_k'_k; auto. rewrite Hk'; auto. reflexivity.
      * rewrite Hk'; auto. reflexivity.
  Qed.   

  Lemma fresh_empty : forall T,
    Var.fresh (Var.Map.empty T) = 0%nat.
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
      (Var.fresh m > x)%nat.
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

