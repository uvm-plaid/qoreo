From Stdlib Require Import String.
From Stdlib Require Lists.List.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
Export List.ListNotations.
From Stdlib Require Import Setoid.


From Qoreo.Base Require Config.
Export Config.Unitary.
From Qoreo Require Import Expr.Expr Choreography.Choreography.
From Qoreo Require Import Network.Network NetQasm.
Require Extraction.

(** 
    This module provides a convenient syntax for writing quantum choreographies in Qoreo. It uses a state monad
    to build up the choreography while using higher-order abstract syntax (HOAS) to generate fresh variable names.

    See Teleport.v for example usage.
*)

(*Open Scope string_scope.*)
Declare Scope example_scope.
Delimit Scope example_scope with QOREO.


(** [state] tracks variable ownership and the choreography being constructed.
    - [vars]: Maps variables to their owning actors
    - [chor]: List of choreography instructions *)
  Record state :=
  {
    vars : Var.Map.t Actor.t
  }.

  (** Expressions of type Qoreo A construct a choreography under the hood *)
  (*
  Definition Qoreo A := state -> state * A.

  Definition ret {A} (a : A) : Qoreo A := fun m => (m, a).
  Definition bind {A B} (m : Qoreo A) (f : A -> Qoreo B) : Qoreo B :=
    fun s =>
      let (s', a) := m s in
      f a s'.

  Definition addVar A x :=
    fun s => 
  
  (** Allocate a fresh variable and map it to the actor [A] in the underlying state. *)
  Definition fresh A : Qoreo Var.t :=
    fun s =>
      let x := Var.fresh (vars s) in
      let s' := {|
        vars := Var.Map.add x A (vars s);
        chor := chor s
      |} in
      (s', x).
*)


  Definition let_var A x C1 C2 :=
    let x' := NetQasm.Var.encode x in
    Choreography.LetIn (Choreography.Pattern.Var A x') C1 C2.
  
  Definition let_bang A x C1 C2 :=
    let x' := NetQasm.Var.encode x in
    Choreography.LetIn (Choreography.Pattern.Bang A x') C1 C2.

  Definition let_pair A1 A2 x1 x2 C1 C2 :=
    let x1' := NetQasm.Var.encode x1 in
    let x2' := NetQasm.Var.encode x2 in
    Choreography.LetIn
      (Choreography.Pattern.Pair 
          (Choreography.Pattern.Var A1 x1')
          (Choreography.Pattern.Var A2 x2'))
      C1 C2.

  (** Convenient notations for local quantum operations. *)
  Notation "A '[-' e '-]'" := (Choreography.Loc A e)
    (no associativity, at level 70).

  Notation "x '@' A" :=
    (Choreography.Pattern.Var A (NetQasm.Var.encode x))
    (no associativity, at level 10) : example_scope.
  Notation "x '@@' A" :=
    (Choreography.Pattern.Bang A (NetQasm.Var.encode x))
    (no associativity, at level 10) : example_scope.
  Notation "'(' p1 ',' p2 ')'" := (Choreography.Pattern.Pair p1 p2) : example_scope.

  Notation "'do' p '←' C1 ;; C2" :=
    (Choreography.LetIn p C1 C2)
    (no associativity, at level 90) : example_scope.


  Open Scope example_scope.

  (** ** Quantum Operations: constructs common quantum protocol operations. *)

  (** Create an entangled pair (EPR pair) between actors [A] and [B]. *)
  Definition get_entangled_pair (A B : Actor.t) :=
    Choreography.EPR A B.


  (** Create a new qubit initialized to |0⟩ owned by [A]. *)
  Definition new (A : Actor.t) : Choreography.t :=
    Choreography.Loc A (New (Bit false)).
  
  Coercion NetQasm.Var.encode : string >-> nat.
  Coercion Var : Var.t >-> Expr.t.
  Definition to_expr (x : string) : Expr.t :=
    Var (NetQasm.Var.encode x).
  Coercion to_expr : string >-> Expr.t.

  (*
  (** Bind the expression [e] to a fresh variable [x] at [A], and return [x]. *)
  Definition local A e : Qoreo Var.t :=
    do q ← fresh A ;;
    do _ ← add_insn (Choreography.Insn.Let A q e);;
    ret q.

   (** Bind the expression [e] to the tuple [(x1,x2)] of fresh variables at [A], and return [(x1,x2)]. *)
  Definition localPair A e : Qoreo (Var.t * Var.t) :=
    do x1 ← fresh A ;;
    do x2 ← fresh A ;;
    do _ ← add_insn (Choreography.Insn.LetPair A x1 x2 e);;
    ret (x1, x2).


  (** Bind the expression [e] to !x , and return x *)
  Definition localBang A e : Qoreo Var.t :=
    do x ← fresh A ;;
    do _ ← add_insn (Choreography.Insn.LetBang A x e);;
    ret x.
  *)

  (** Measure qubit [q] owned by [A] in the computational basis. *)
  Definition meas (A : Actor.t) (q : Var.t) : Choreography.t :=
    Choreography.Loc A (Meas (Var q)).

  (** Send quantum data from actor [A] to actor [B]. *)
  Definition send A (e : Expr.t) B : Choreography.t :=
    Choreography.Send A e B.

  Fixpoint expr_of_pat (p : Choreography.Pattern.t) : Expr.t :=
    match p with
    | Choreography.Pattern.Var _ x => Expr.Var x
    | Choreography.Pattern.Bang _ x => Expr.Bang (Expr.Var x)
    | Choreography.Pattern.Unit => Expr.Unit
    | Choreography.Pattern.Pair p1 p2 => Expr.Pair (expr_of_pat p1) (expr_of_pat p2)
    end.
  Coercion expr_of_pat : Choreography.Pattern.t >-> Expr.t.


  (** Send a qubit from Alice to Bob via teleportation. *)
  Definition teleport (A B : Actor.t) (q : Var.t) : Choreography.t :=
    let a := "a" @ A in
    let b := "b" @ B in
    let q := "q" @ A in
    let x := "x" in
    let z := "z" in
    do ("a"@A,b)  ← get_entangled_pair A B ;;
    do (q,a)  ← A [- Unitary CNOT (Pair q a) -] ;;
    do q      ← A [- Unitary H q -] ;;
    do z@@A   ← A [- Meas q -] ;;
    do x@@A   ← A [- Meas a -] ;;
    do z@@B   ← send A z B ;;
    do x@@B   ← send A x B ;;
    do b      ← B [- Expr.If z (Unitary Z b) b -] ;;
    do b      ← B [- Expr.If x (Unitary X b) b -] ;;
    Choreography.Loc B b.



(* Tactics for typechecking examples *)


Import Actor.Map.
Require Import Lia.


Definition singleton {T} x (tau : T) := Var.Map.add x tau (Var.Map.empty T).
Lemma wtqvar : forall x (τ : typ),
  Expr.WellTyped (Var.Map.empty _) (Var.Map.add x τ (Var.Map.empty _)) (Var.Map.empty _) (Expr.Var x) τ.
Proof.
  intros. econstructor; eauto; Var.simplify.
Qed.
Lemma wtbit : forall Γ b,
  Expr.WellTyped Γ (Var.Map.empty _) (Var.Map.empty _) (Bit b) BIT.
Proof. intros. econstructor; eauto; Var.simplify. Qed.

Lemma wtqref : forall Γ q (idx : nat),
  Expr.WellTyped Γ (Var.Map.empty _) (Var.Map.add q idx (Var.Map.empty _)) (QRef q) QUBIT.
Proof. intros. econstructor; eauto; Var.simplify. Qed.


Ltac solve_wt :=
  match goal with
  | [ |- Expr.WellTyped _ _ _ (Expr.Var ?q) _ ] => apply wtqvar
  | [ |- Expr.WellTyped _ _ _ (Bit _) _] => apply wtbit
  | [ |- Expr.WellTyped _ _ _ (QRef _) _] => apply wtqref
  | [ |- Expr.WellTyped _ _ _ _ _] => econstructor; auto; try reflexivity
  | [ |- Choreography.WellTyped _ _ _ _] => econstructor; auto; try reflexivity

  | [ |- Var.Map.Partition _ _ _ ] => Var.Map.Tactics.reflect_partition
  | [ |- _ /\ _ ] => split; auto
  | [ |- ~ (_ \/ _)] => intros [? | ?]; subst; try contradiction
  end.


Ltac fold_ChorEnv :=
  match goal with
  | [ |- context[Actor.Map.add ?A (Var.Map.add ?x ?tau ?D) ?T ]] =>
    let Heq := fresh "Heq" in
    assert (Heq : ChorEnv.Equal (Actor.Map.add A (Var.Map.add x tau D) T) (ChorEnv.add A x tau (Actor.Map.add A D T)))
    by ChorEnv.solve;
    rewrite Heq; clear Heq
  end.

Ltac right_associate A :=
  try unfold ChorEnv.add;
  match goal with
  | [ H : A <> ?B |- context[Actor.Map.add A _ (Actor.Map.add ?B _ _)]] =>
    rewrite (ChorEnv.ce_actor_add_neq_sym A B); auto
  | [ H : ?B <> A |- context[Actor.Map.add A _ (Actor.Map.add ?B _ _)]] =>
    rewrite (ChorEnv.ce_actor_add_neq_sym A B); auto
  end.


(*
Definition render_Qoreo (b : Backend) (ps : list Actor.t)
                        (M : Qoreo (list Var.t)) 
  : option (list AppFile.t) :=
  let (st, xs) := M empty_state in
  let f := fun (env : Actor.Map.t (list Var.t)) (p : Actor.t) =>
    Actor.Map.add p (epp_vars p (vars st) xs) env
  in
  let env_map : Actor.Map.t (list Var.t) :=
      List.fold_left f ps (Actor.Map.empty _)
  in
  NetQasm.render_parties b (chor st)
          ps
          env_map.
          *)