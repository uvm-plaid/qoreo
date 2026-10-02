From Qoreo.Base Require Import Map.
From Stdlib Require Import Bool.

Create HintDb actor_db.

  Lemma bool_dec_refl : forall (b : bool), bool_dec b b = left (eq_refl b).
  Proof. destruct b; auto. Qed.
  Lemma ascii_dec_refl : forall (a : Ascii.ascii), Ascii.ascii_dec a a = left (eq_refl a).
  Proof.
    destruct a. simpl.
    repeat rewrite bool_dec_refl.
    simpl.
    reflexivity.
  Qed.


  Module V := OrderedTypeEx.UOT_to_OT (OrderedTypeEx.String_as_OT).
  Include V.
  
  Module Map := FMap(V).
  Module FSet := Map.S.

  Ltac simplify :=
    repeat
    (autorewrite with actor_db in *;
      Map.Tactics.vsimpl;
      repeat Map.Tactics.reduce_eq_dec;
      try (first [tauto | reflexivity | discriminate | auto | intuition]; fail)).

  (* instantiate this for each relevant hint database *)
  Ltac reflect_find :=
    repeat (
      Map.Proofs.reflect_find_body;
      autorewrite with actor_db in *;
      repeat Map.Tactics.reduce_eq_dec
    ).
  Ltac solve := 
    repeat (reflect_find; first [tauto | discriminate | auto; fail | intuition]).

  (*  #[global] Existing Instance MapProofs.F.EqualSetoid.*)
  
  (* Global actor_db hints: instantiations of FMap_fun's local qoreo_db hints for Actor.Map *)
  #[global] Hint Rewrite Map.Properties.F.add_mapsto_iff : actor_db.
  #[global] Hint Rewrite Map.Properties.F.empty_mapsto_iff : actor_db.
  #[global] Hint Rewrite Map.Properties.F.add_in_iff : actor_db.
  #[global] Hint Rewrite Map.Properties.F.map_o : actor_db.
  #[global] Hint Rewrite Map.Properties.F.remove_o : actor_db.
  #[global] Hint Rewrite Map.Properties.F.add_o : actor_db.
  #[global] Hint Rewrite Map.Properties.F.empty_o : actor_db.
  #[global] Hint Rewrite Map.Properties.F.map_in_iff : actor_db.
  #[global] Hint Rewrite Map.Properties.F.remove_mapsto_iff : actor_db.
  #[global] Hint Rewrite Map.Properties.F.empty_in_iff : actor_db.

  #[global] Hint Resolve Map.empty_1 : actor_db.
  #[global] Hint Resolve Map.Properties.Partition_sym : actor_db.
  #[global] Hint Rewrite Map.Properties.F.remove_in_iff : actor_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_1 : actor_db.
  #[global] Hint Rewrite Map.Proofs.disjoint_add_2 : actor_db.

  #[global] Existing Instance Map.Proofs.singletonProper.
  #[global] Existing Instance Map.Proofs.concatProper.
  #[global] Existing Instance Map.Proofs.domainProper.
  #[global] Existing Instance Map.FSetProofs.setminusProper.

  #[global] Hint Rewrite Map.Proofs.concat_find : actor_db.
  #[global] Hint Rewrite Map.Proofs.concat_in : actor_db.
  #[global] Hint Rewrite @Map.Proofs.concat_add_l : actor_db.
  #[global] Hint Rewrite @Map.Proofs.map_concat : actor_db.
  #[global] Hint Rewrite Map.Proofs.fset_in_union : actor_db.
  #[global] Hint Rewrite Map.Proofs.remove_map : actor_db.
  #[global] Hint Rewrite Map.Proofs.remove_add : actor_db.
  #[global] Hint Rewrite Map.Proofs.remove_empty : actor_db.
  #[global] Hint Rewrite @Map.Proofs.map_add : actor_db.
  #[global] Hint Resolve @Map.Proofs.empty_map_equal : actor_db.
  #[global] Hint Rewrite @Map.Proofs.empty_map_empty : actor_db.
  #[global] Hint Resolve @Map.Proofs.singleton_remove : actor_db.
  #[global] Hint Rewrite @Map.Proofs.concat_disjoint : actor_db.
  #[global] Hint Rewrite Map.Proofs.add_remove_eq : actor_db.
  #[global] Hint Rewrite Map.Proofs.add_add_eq : actor_db.
  #[global] Hint Rewrite Map.Proofs.singleton_empty : actor_db.
  #[global] Hint Rewrite Map.Proofs.remove_remove : actor_db.

  #[global] Hint Rewrite @Map.FSetProofs.setminus_mapsto_iff : actor_db.
  #[global] Hint Rewrite Map.FSetProofs.setminus_add : actor_db.
  #[global] Hint Rewrite Map.FSetProofs.setminus_singleton : actor_db.
  #[global] Hint Rewrite Map.FSetProofs.find_setminus : actor_db.
  #[global] Hint Rewrite Map.FSetProofs.add_mem_iff : actor_db.
  #[global] Hint Rewrite Map.FSetProofs.singleton_mem_iff : actor_db.

  #[global] Hint Resolve Map.Proofs.add_mapsto : actor_db.
  #[global] Hint Resolve Map.Proofs.disjoint_empty_1 Map.Proofs.disjoint_empty_2 : actor_db.
  #[global] Hint Resolve Map.Proofs.disjoint_in_l Map.Proofs.disjoint_in_r : actor_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_l : actor_db.
  #[global] Hint Resolve Map.Proofs.partition_empty_r : actor_db.
  #[global] Hint Resolve Map.M.remove_1 : actor_db.
  #[global] Hint Resolve Map.Proofs.disjoint_sym : actor_db.
  #[global] Hint Resolve Map.Proofs.concat_assoc : actor_db.

  (*
  #[global] Hint Extern 4 (Map.Partition (Map.concat _ _) _ _) => Map.Proofs.partition_concat : actor_db.
  #[global] Hint Extern 4 (Map.Partition _ (Map.concat _ _) _) => Map.Tactics.partition_concat : actor_db.
  #[global] Hint Extern 4 (Map.Partition _ _ (Map.concat _ _)) => Map.Tactics.partition_concat : actor_db.
  *)

  #[global] Hint Rewrite Map.FSetProperties.inter_iff : actor_db.
  #[global] Hint Rewrite Map.MProofs.FSetProperties.add_iff: actor_db.
  #[global] Hint Rewrite Map.FSetProperties.singleton_iff : actor_db.
  #[global] Hint Rewrite Map.FSetProperties.add_iff : actor_db.
  #[global] Hint Rewrite Map.FSetProperties.remove_iff : actor_db.

