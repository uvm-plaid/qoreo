
From Stdlib Require Import String.
From Qoreo Require Import Base.Config Expr.Expr Choreography.Choreography.
Import Config.Unitary.
Import Expr.

From Qoreo.Choreography Require Import Notation.

From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Import List.ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope example_scope.

Module ConditionalTest.

  (* This helper function solves the type mismatch issue *)
  Definition add_chor (C : Choreography.t) : Qoreo unit :=
    fun s =>
      ({|
        vars := vars s;
        chor := Choreography.seq (chor s) C
      |}, tt).

  Definition conditional_test (Alice Bob Charlie : Actor.t) : Qoreo (list Var.t) :=
  (*Definition conditional_test (Alice Bob Charlie : Actor.t) : Qoreo (Var.t * (Var.t * Var.t)) := *)
    do q ← Alice [- Unitary H (New (Bit false)) -] ;;
    do m ← Alice [- Meas q -] ;;

    do _ ← add_chor (
      Choreography.If Alice (Var m)

        (* Alice measures 0 *)
        (mk (
          do a ← Alice [- Bit true -] ;;
          do b ← Bob [- Bit true -] ;;
          do c ← Charlie [- Bit true -];;
          do b_a ← send Bob b Alice ;;
          do c_a ← send Charlie c Alice ;;
          ret tt
        ))

        (* Alice measures 1 *)
        (mk (
          do a ← Alice [- Bit false -] ;;
          do b ← Bob [- Bit false -] ;;
          do c ← Charlie [- Bit false -];;
          do b_a ← send Bob b Alice ;;
          do c_a ← send Charlie c Alice ;;
          ret tt
        ))

        Choreography.Empty
    ) ;;
(*
    do bob_result ← send Alice m Bob ;;
    do charlie_result ← send Alice m Charlie ;;

  do alice_final ← Alice [- Var m -] ;;
  do bob_final ← Bob [- Var bob_result -] ;;
  do charlie_final ← Charlie [- Var charlie_result -] ;;

  (*ret (alice_final, (bob_final, charlie_final)). *)*)
  (*ret tt.*)
  ret [].

  Definition choreo : Choreography.t :=
    mk (do result ← conditional_test "alice" "bob" "charlie" ;;
    ret result).

  Definition parties : list Actor.t :=
    ["alice"; "bob"; "charlie"].

  Definition apps : option (list AppFile.t) :=
    Notation.render_Qoreo NetSquid parties (conditional_test "alice" "bob" "charlie").

End ConditionalTest.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Definition example_apps := ConditionalTest.apps.
Extraction "ConditionalTest.ml" example_apps.


(*The error version

From Stdlib Require Import String.
From Qoreo Require Import Base.Config Expr.Expr Choreography.Choreography.
Import Config.Unitary.
Import Expr.

From QoreoExamples Require Import Notation.
Import ExampleExtraction.

From Stdlib Require Import extraction.ExtrOcamlNativeString.
From Qoreo Require Import NetQasm.

Import List.ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope example_scope.

Module ConditionalTest.

  Definition conditional_test (Alice Bob Charlie : Actor.t) : Qoreo unit :=
    do q ← Alice [- Unitary H (New (Bit false)) -] ;;
    do m ← Alice [- Meas q -] ;;

    do _ ← Choreography.If Alice (Var m)

      (*Do if Alice measures 0*)
      (mk (
        do a ← Alice [- Bit true -] ;;
        do b ← Bob [- Bit true -] ;;
        Charlie [- Bit true -]
        ret tt.
      ))

      (*Do if Alice measures 1*)
      (mk (
        do a ← Alice [- Bit false -] ;;
        do b ← Bob [- Bit false -] ;;
        Charlie [- Bit false -]
        ret tt.
      ))

      Choreography.Empty ;;

    ret tt.

  Definition choreo : Choreography.t :=
    mk (
      do result ← conditional_test "alice" "bob" "charlie" ;;
      ret result
    ).

  Definition parties : list Actor.t :=
    ["alice"; "bob"; "charlie"].

  Definition apps : option (list AppFile.t) :=
    ExampleExtraction.render_parties choreo parties.

End ConditionalTest.

Extraction Language OCaml.
Set Extraction Output Directory "extracted".
Extraction "ConditionalTest.ml" ConditionalTest.apps.

*)