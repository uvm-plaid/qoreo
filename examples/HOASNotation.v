From Stdlib Require Import String.
From Stdlib Require Lists.List.
From Stdlib Require Import extraction.ExtrOcamlNativeString.
Import List.ListNotations.

From Qoreo Require Import Base Expr Choreography.
From Qoreo Require Import Network NetQasm.
From QoreoExamples Require Import Notation.
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
    - [chor]: List of choreography instructions *)
  Record state :=
  {
    vars : Var.Map.t Actor.t;
    chor : Choreography.t
  }.

  (** Expressions of type Qoreo A construct a choreography under the hood *)
  Definition Qoreo A := state -> state * A.

  Definition ret {A} (a : A) : Qoreo A := fun m => (m, a).
  Definition bind {A B} (m : Qoreo A) (f : A -> Qoreo B) : Qoreo B :=
    fun s =>
      let (s', a) := m s in
      f a s'.

  (** Notation for monadic sequencing (similar to Haskell's do-notation). *)
  Notation "'do' x '←' m ';;' e" := (bind m (fun x => e))
      (right associativity, at level 90) : example_scope.
  Notation "'do' ( x , y ) '←' m ';;' e" := (bind m (fun z => let (x,y) := z in e))
      (right associativity, at level 90) : example_scope.

  Definition empty_state : state :=
  {|
    vars := Var.Map.empty _;
    chor := []
  |}.

  (** Extract the underlying choreography from a monadic computation. *)
  Definition mk {T} (m : Qoreo T) : Choreography.t :=
    let (s,_) := m empty_state in
    chor s.

  (** Allocate a fresh variable and map it to the actor [A] in the underlying state. *)
  Definition fresh A : Qoreo Var.t :=
    fun s =>
      let x := Var.fresh (vars s) in
      let s' := {|
        vars := Var.Map.add x A (vars s);
        chor := chor s
      |} in
      (s', x).

  (** Append instruction [I] to the choreography in the current state *)
  Definition add_insn (I : Choreography.Insn.t) : Qoreo unit :=
    fun s =>
      let s' := {|
        vars := vars s;
        chor := (chor s ++ [I])%list
      |} in
      (s', tt).

  Open Scope example_scope.

  (** ** Quantum Operations: constructs common quantum protocol operations. *)

  (** Create an entangled pair (EPR pair) between actors [A] and [B]. *)
  Definition get_entangled_pair (A B : Actor.t) : Qoreo (Var.t * Var.t) :=
    do xA ← fresh A ;;
    do xB ← fresh B ;;
    do _  ← add_insn (Choreography.Insn.EPR A xA B xB) ;;
    ret (xA, xB).

  (** Create a new qubit initialized to |0⟩ owned by [A]. *)
  Definition new (A : Actor.t) : Qoreo Var.t :=
    do q ← fresh A ;;
    do _ ← add_insn (Choreography.Insn.Let A q (New (Bit false))) ;;
    ret q.
  
  Coercion Var : Var.t >-> Expr.t.

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

  (** Measure qubit [q] owned by [A] in the computational basis. *)
  Definition meas (A : Actor.t) (q : Var.t) : Qoreo Var.t :=
    do x ← fresh A ;;
    do _ ← add_insn (Choreography.Insn.Let A x (Meas (Var q)));;
    ret q.

  (** Send quantum data from actor [A] to actor [B]. *)
  Definition send A (e : Expr.t) B : Qoreo Var.t :=
    do x ← fresh B;;
    do _ ← add_insn (Choreography.Insn.Send A e B x);;
    ret x.

  (** Conditionally apply X gate based on classical bit [e]. *)
  Definition if_X A (e : Expr.t) (q : Var.t) : Qoreo unit :=
    add_insn (Choreography.Insn.Let A q (If e (Unitary X q) q)).
  (** Conditionally apply Z gate based on classical bit [e]. *)
  Definition if_Z A (e : Expr.t) (q : Var.t) : Qoreo unit :=
    add_insn (Choreography.Insn.Let A q (If e (Unitary Z q) q)).

  (** Convenient notations for local quantum operations. *)
  Notation "A '[-' e '-]'" :=
    (local A e)
    (no associativity, at level 50) : example_scope.
  Notation "A '[--' e '-]'" :=
    (localPair A e)
    (no associativity, at level 50) : example_scope.


Module ExampleExtraction.
  Definition render_party (choreo : Choreography.t) (p : Actor.t)
    : option AppFile.t :=
    match Network.epp p choreo with
    | Some proc =>
        Some {| AppFile.party := p; AppFile.source := render_app p proc |}
    | None => None
    end.

  Fixpoint render_parties (choreo : Choreography.t) (ps : list Actor.t)
    : option (list AppFile.t) :=
    match ps with
    | [] => Some []
    | p :: ps' =>
        match render_party choreo p, render_parties choreo ps' with
        | Some app, Some apps => Some (app :: apps)
        | _, _ => None
        end
    end.
End ExampleExtraction.
