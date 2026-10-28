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


(** [state] tracks variable ownership and the choreography being constructed.
    - [vars]: Maps variables to their owning actors
*)
  Record state :=
  {
    vars : Var.Map.t Actor.t;
  }.

  (** Expressions of type Qoreo A construct a choreography under the hood *)
  Definition Qoreo A := state -> state * A.

  Definition ret {A} (a : A) : Qoreo A := fun m => (m, a).
  Definition bind {A B} (m : Qoreo A) (f : A -> Qoreo B) : Qoreo B :=
    fun s =>
      let (s', a) := m s in
      f a s'.


  Definition empty_state : state :=
  {|
    vars := Var.Map.empty _
  |}.

  (** Extract the underlying choreography from a monadic computation. *)
  Definition run {T} (m : Qoreo T) : T :=
    let (st, v) := m empty_state in 
    v.

  (** Allocate a fresh variable and map it to the actor [A] in the underlying state. *)
  Definition fresh A : Qoreo Var.t :=
    fun s =>
      let x := Var.fresh (vars s) in
      let s' := {| vars := Var.Map.add x A (vars s); |} in
      (s', x).

    
  (** Notation for monadic sequencing (similar to Haskell's do-notation). *)
  Notation "'do' x '←' m ';;' e" := (bind m (fun x => e))
      (right associativity, at level 90) : example_scope.
  Notation "'do' ( x , y ) '←' m ';;' e" := (bind m (fun z => let (x,y) := z in e))
      (right associativity, at level 90) : example_scope.
  Open Scope example_scope.

  Fixpoint freshC (τ : Choreography.Typ.t) : Qoreo Choreography.Pattern.t :=
    match τ with
    | Choreography.Typ.Local A _ =>
      do x ← fresh A ;;
      ret (Choreography.Pattern.Var A x)
    | Choreography.Typ.Unit => ret (Choreography.Pattern.Unit)
    | Choreography.Typ.Pair τ1 τ2 =>
      do p1 ← freshC τ1 ;;
      do p2 ← freshC τ2 ;;
      ret (Choreography.Pattern.Pair p1 p2)
    end.

  Definition letin (A : Actor.t)
                   (m : Qoreo Choreography.t)
                   (f : Var.t -> Qoreo Choreography.t)
                   : Qoreo Choreography.t :=
    do C ← m ;;
    do x ← fresh A ;;
    do C' ← f x ;;
    ret (Choreography.LetIn (Choreography.Pattern.Var A x) C C').

  Definition letbang (A : Actor.t)
                   (m : Qoreo Choreography.t)
                   (f : Var.t -> Qoreo Choreography.t)
                   : Qoreo Choreography.t :=
    do C ← m ;;
    do x ← fresh A ;;
    do C' ← f x ;;
    ret (Choreography.LetIn (Choreography.Pattern.Bang A x) C C').

  Definition letpair (A1 A2 : Actor.t)
                   (m : Qoreo Choreography.t)
                   (f : Var.t -> Var.t -> Qoreo Choreography.t)
                   : Qoreo Choreography.t :=
    do C ← m ;;
    do x1 ← fresh A1 ;;
    do x2 ← fresh A2 ;;
    do C' ← f x1 x2 ;;
    let p := Choreography.Pattern.Pair
                (Choreography.Pattern.Var A1 x1)
                (Choreography.Pattern.Var A2 x2) in
    ret (Choreography.LetIn p C C').
  Definition letlocpair (A : Actor.t)
                   (m : Qoreo Choreography.t)
                   (f : Var.t -> Var.t -> Qoreo Choreography.t)
                   : Qoreo Choreography.t :=
    do C ← m ;;
    do x1 ← fresh A ;;
    do x2 ← fresh A ;;
    do C' ← f x1 x2 ;;
    let p := Choreography.Pattern.VarPair A x1 x2 in
    ret (Choreography.LetIn p C C').

  (** Notation for monadic sequencing (similar to Haskell's do-notation). *)
  Notation "'LET' x '@' A '←' m ';;' e" := (letin A m (fun x => e))
      (right associativity, at level 90) : example_scope.
  Notation "'LET!' x '@' A '←' m ';;' e" := (letbang A m (fun x => e))
      (right associativity, at level 90) : example_scope.
  (* TODO: support this operation?? *)
  Notation "'LET' '(' x '@' A ',' y '@' B ')' '←' m ';;' e" := (letpair A B m (fun x y => e))
      (right associativity, at level 90) : example_scope.
    
  Notation "'LET@' '(' x ',' y ')' '@' A '←' m ';;' e" := (letlocpair A m (fun x y => e))
      (right associativity, at level 90) : example_scope.


  (** ** Quantum Operations: constructs common quantum protocol operations. *)

  (** Create an entangled pair (EPR pair) between actors [A] and [B]. *)
  Definition get_entangled_pair (A B : Actor.t) : Qoreo Choreography.t :=
    ret (Choreography.EPR A B).

  (** Bind the expression [e] to a fresh variable [x] at [A], and return [x]. *)
  Definition local A e : Qoreo Choreography.t :=
    ret (Choreography.Loc A e).

  (** Create a new qubit initialized to |0⟩ owned by [A]. *)
  Definition new (A : Actor.t) : Qoreo Choreography.t :=
    local A (New (Bit false)).
  
  Coercion Var : Var.t >-> Expr.t.

  (** Measure qubit [q] owned by [A] in the computational basis. *)
  Definition meas (A : Actor.t) (q : Expr.t) : Qoreo Choreography.t :=
    local A (Meas q).

  Open Scope example_scope.

  Definition pair A1 A2 (C1 : Qoreo Choreography.t) (C2 : Qoreo Choreography.t) : Qoreo Choreography.t :=
    LET x1 @ A1 ← C1 ;;
    LET x2 @ A2 ← C2 ;;
    ret (Choreography.Pair (Choreography.Loc A1 x1) (Choreography.Loc A2 x2)).

  (** Send quantum data from actor [A] to actor [B]. *)
  Definition send A (e : Expr.t) B : Qoreo Choreography.t :=
    ret (Choreography.Send A e B).


  (*
  (** Conditionally apply X gate based on classical bit [e]. *)
  Definition if_X A (e : Expr.t) (q : Var.t) : Qoreo unit :=
    add_insn (Choreography.Insn.Let A q (Expr.If e (Unitary X q) q)).
  (** Conditionally apply Z gate based on classical bit [e]. *)
  Definition if_Z A (e : Expr.t) (q : Var.t) : Qoreo unit :=
    add_insn (Choreography.Insn.Let A q (Expr.If e (Unitary Z q) q)).
  *)

  (** Convenient notations for local quantum operations. *)
  Notation "A '[-' e '-]'" :=
    (local A e)
    (no associativity, at level 50) : example_scope.


(* Tactics for typechecking examples *)


Import Actor.Map.


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


  (** Send a qubit from Alice to Bob via teleportation. *)
  Definition teleport (Alice Bob : Actor.t) (q : Var.t) : Qoreo Choreography.t :=
    LET (a @ Alice, b @ Bob)   ← get_entangled_pair Alice Bob ;;
    LET@ (q, a) @Alice ← Alice [- Unitary CNOT (Pair q a) -] ;;
    LET  q @ Alice ← Alice [- Unitary H q -] ;;
    LET! z @ Alice ← Alice [- Meas q -] ;;
    LET! x @ Alice ← Alice [- Meas a -] ;;
    LET! z @ Bob   ← send Alice z Bob ;;
    LET! x @ Bob   ← send Alice x Bob ;;
    LET  b @ Bob   ← Bob [- Expr.If z (Unitary Z b) b -] ;;
    Bob [- Expr.If x (Unitary X b) b -].


Definition render_Qoreo (b : Backend)
                        (M : Qoreo Choreography.t) 
  : option (list AppFile.t) :=
  let C := run M in
  NetQasm.render_parties b C (Actor.FSet.elements (Choreography.actors C)).