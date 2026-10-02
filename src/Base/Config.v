From QuantumLib Require Import Matrix Pad Quantum.
From Stdlib Require Import String Morphisms (* for Proper *).
Require Import Setoid. (* for setoid_replace with *)
From Qoreo.Base Require Var.

Module Unitary.
Inductive unitary :=
| H | X | Y | Z | CNOT | SGATE | Sdag | TGATE | Tdag.
End Unitary.
Import Unitary.
  
  Record t := {
    dim : nat;
    (*qrefs : Var.Map.t nat;*)
    qstate : Matrix (Nat.pow 2 dim) (Nat.pow 2 dim)
  }.


  Record WellScoped (refs : Var.Map.t nat) (cfg : t) := {
    wf_qstate : Matrix.WF_Matrix (qstate cfg);
    (*wf_qrefs : List.Forall
              (fun x => snd x < dim cfg)%nat
              (Var.Map.elements refs)
              *)
    wf_qrefs : forall x, Var.Map.In x refs -> (x < dim cfg)%nat
  }.

  
    Definition find (x : Var.t) refs : nat :=
      match Var.Map.find x refs with
      | Some q => q
      | None   => 0%nat
      end.
      


  (* Project onto the state where qubit q is in the classical state |b> *)
  (*Definition proj q dim (b : bool) := pad_u dim q (bool_to_matrix b).*)
  Definition measure (b : bool) (x : Var.t) refs (cfg : t)
    : Var.Map.t nat * t :=
    let q := find x refs in
    let rho' := super (pad_u (dim cfg) q (bool_to_matrix b)) (qstate cfg) in
    (Var.Map.remove x refs, {|
      dim := dim cfg;
      qstate := rho'
    |}).

  Definition new (b : bool) refs (cfg : t) : Var.t * Var.Map.t nat * t :=
    (*let x := Var.fresh refs in*)
    let x := dim cfg in (* don't want x to depend on refs *)
    let q := dim cfg in
    let rho' := kron (qstate cfg) (bool_to_ket b × (bool_to_ket b)†) in
    (x, Var.Map.add x q refs, {|
      dim := 1 + dim cfg;
      qstate := rho'
    |}).

  Definition apply_matrix (cfg : t) (U : Matrix (2 ^ dim cfg) (2 ^ dim cfg)) : t :=
  {|
    dim := dim cfg;
    qstate := super U (qstate cfg)
  |}.
  
  (**
    Inputs:
      - refs : an assignment of variables in indices in cfg
      - cfg : a configuration of dimension d
    Returns:
      - a fresh variable x
      - an updated map that includes refs along with x |-> d
      - an updated configuration where the dimension has been incremented to d+1
    Note that the quantum state inside the resulting configuration still has dimension d, and will need to be incremented.
  *)
  Definition fresh_var (refs : Var.Map.t nat) (cfg : t) : Var.t * Var.Map.t nat * t :=
    let d := dim cfg in
    let x := Var.fresh refs in
    let refs' := Var.Map.add x d refs in
    let cfg' := {| dim := 1 + dim cfg; qstate := qstate cfg |} in
    (x, refs', cfg').

  Definition epr_cfg cfg : nat * nat * t :=
    let d := dim cfg in
    let bell00 := Quantum.EPRpair × (Quantum.EPRpair †) in
    let rho' := kron (qstate cfg) bell00 in
    (d, 1+d, {|
      dim := 2 + dim cfg;
      qstate := rho'
    |})%nat.

  Definition epr refs (cfg : t) : Var.t * Var.t * Var.Map.t nat * t :=
    match epr_cfg cfg with
    | (idx1, idx2, cfg') =>
      let x1 := (*Var.fresh refs*) idx1 in (* don't want x1 to depend on refs *)
      let refs' := Var.Map.add x1 idx1 refs in
      let x2 := (*Var.fresh refs'*) idx2 in (* don't want x2 to depend on refs*)
      let refs'' := Var.Map.add x2 idx2 refs' in
      (x1, x2, refs'', cfg')
    end.


  Definition gate_to_matrix (n : nat) (U : unitary) (qs : list nat) : Matrix (2^n) (2^n) :=
  match U, qs with
  | H, [q] => @pad 1 q n Quantum.hadamard
  | X, [q] => @pad 1 q n Quantum.σx
  | Y, [q] => @pad 1 q n Quantum.σy
  | Z, [q] => @pad 1 q n Quantum.σz
  | CNOT, [q1; q2] => pad_ctrl n q1 q2 Quantum.σx
  | SGATE, [q] => @pad 1 q n Quantum.Sgate
  | Sdag, [q]  => @pad 1 q n Quantum.Sgate†
  | TGATE, [q] => @pad 1 q n Quantum.Tgate
  | Tdag, [q]  => @pad 1 q n Quantum.Tgate†
  | _, _ => Zero
  end.

  Definition apply_gate (U : unitary) (xs : list Var.t) refs (cfg : t) : t :=
    let qs := List.map (fun x => find x refs) xs in
    apply_matrix cfg (gate_to_matrix _ U qs).

  (*
  Lemma test1 : gate_to_matrix 2 CNOT [0;1]%nat = cnot.
  Proof.
    assert (H : WF_Matrix (gate_to_matrix 2 CNOT [0%nat; 1%nat])).
    { simpl.
      set (H0 := QuantumLib.Pad.WF_pad_ctrl 2 0 1 σx).
      apply H0.
      auto with wf_db.
    }
    prep_matrix_equality.
    destruct x as [ | [ | [ | [ | x ]]]];
    destruct y as [ | [ | [ | [ | y ]]]];
      try (rewrite H; [ auto | right; simpl; lia]; fail);
      try (rewrite H; [ auto | left; simpl; lia]; fail);
      try lca.
  Qed.

  Lemma test2 :gate_to_matrix 1 H [0]%nat = hadamard.
  Proof.
    simpl. unfold pad. simpl. Msimpl; auto.
  Qed.
  *)

  (* Properties of well-scopedness*)

  Global Instance WellScopedProper : Proper (Var.Map.Equal ==> eq ==> iff) Config.WellScoped.
  Proof.
    intros refs1 refs2 Hrefs cfg1 cfg2 Hcfg; subst.
    split; intros [wf_qstate wf_qrefs].
    + split; auto;
      intros x; setoid_rewrite <- Hrefs; auto.
    + split; auto;
      intros x; setoid_rewrite Hrefs; auto.
  Qed.

  Lemma WellScoped_concat : forall Θ1 Θ2 cfg,
    WellScoped (Var.Map.concat Θ1 Θ2) cfg 
    <->
    WellScoped Θ1 cfg /\ Config.WellScoped Θ2 cfg.
  Proof.
    intros ? ? ?.
    split.
    + intros [wf ws].
      split; split; auto;
      intros x Hin; apply ws;
      autorewrite with var_db; auto.
    + intros [[wf ws1] [_ ws2]].
      split; auto.
      intros x Hin. autorewrite with var_db in Hin.
      destruct Hin as [Hin | Hin];
        [apply ws1 | apply ws2]; auto.
  Qed.
  #[global] Hint Rewrite WellScoped_concat : var_db.

  Lemma WellScoped_empty : forall cfg,
    WF_Matrix (qstate cfg) ->
    WellScoped (Var.Map.empty nat) cfg.
  Proof.
    intros cfg HWF.
    split; auto.
    intros z Hin.
    autorewrite with var_db in *.
    contradiction.
  Qed.

  Global Instance findProper : Proper (eq ==> Var.Map.Equal ==> eq) find.
  Proof.
    intros x' x Hx refs1 refs2 Hrefs; subst.
    unfold Config.find. rewrite Hrefs; auto.
  Qed.

  Lemma measure_Proper : forall b x cfg refs1 refs2 refs1' refs2' cfg1' cfg2',
    Var.Map.Equal refs1 refs2 ->
    measure b x refs1 cfg = (refs1', cfg1') ->
    measure b x refs2 cfg = (refs2', cfg2') ->
    Var.Map.Equal refs1' refs2' /\ cfg1' = cfg2'.
  Proof.
    intros ? ? ? ? ? ? ? ? ?.
    intros Heq Hmeas1 Hmeas2.
    inversion Hmeas1; inversion Hmeas2; subst; clear Hmeas1 Hmeas2.
    split.
    + rewrite Heq. reflexivity.
    + unfold find. rewrite Heq. reflexivity.
  Qed.

  Global Instance measureProper :
    Proper (eq ==> eq ==> Var.Map.Equal ==> eq ==>
      RelationPairs.RelProd Var.Map.Equal eq)
      measure.
  Proof.
    intros ? b ? ? x ? refs1 refs2 Hrefs ? cfg ?;
      subst.
    
    eapply (measure_Proper b x cfg) in Hrefs;
      try reflexivity.
    destruct Hrefs as [Heq Heq'].
    split; unfold RelationPairs.RelCompFun;
      simpl; auto.
  Qed.

  Global Instance newProper :
    Proper (eq ==> Var.Map.Equal ==> eq ==>
      RelationPairs.RelProd (RelationPairs.RelProd eq Var.Map.Equal) eq)
      new.
  Proof.
    intros ? b ? refs1 refs2 Hrefs ? cfg ?; subst.
    repeat split; unfold RelationPairs.RelCompFun;
      simpl; auto.
    rewrite Hrefs; reflexivity.
  Qed.

  Global Instance eprProper :
    Proper (Var.Map.Equal ==> eq ==>
      RelationPairs.RelProd
      (RelationPairs.RelProd eq Var.Map.Equal)
      eq)
      epr.
  Proof.
    intros refs1 refs2 Hrefs ? cfg ?; subst;
    repeat split; unfold RelationPairs.RelCompFun;
      simpl; auto.
    * rewrite Hrefs; auto. reflexivity.
  Qed. 

  Global Instance apply_gate_Proper :
    Proper (eq ==> eq ==> Var.Map.Equal ==> eq ==> eq) apply_gate.
  Proof.
    intros g' g Hg ls' ls Hls refs1 refs2 Hrefs cfg1 cfg2 Hcfg;
      subst.
    unfold Config.apply_gate.
    f_equal. f_equal.
    apply Proper_map; auto.
    intros x. rewrite Hrefs; auto.
  Qed.

  Lemma WellScoped_monotonic : forall cfg cfg' Theta Theta',
    WellScoped Theta cfg ->
    WellScoped Theta' cfg' ->
    (dim cfg <= dim cfg')%nat ->
    WellScoped Theta cfg'.
  Proof.
    intros ? ? ? ? HWS HWS' Hdim.
    destruct HWS; destruct HWS'.
    split; auto.
    intros x Hin.
    specialize (wf_qrefs0 x Hin). lia.
  Qed.

