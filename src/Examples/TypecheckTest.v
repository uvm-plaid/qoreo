From Stdlib Require Import String.
From Qoreo Require Import Base.Config Expr.Expr Choreography.Choreography.


From Qoreo.Choreography Require Import Notation Typecheck.
Import List.ListNotations.

Open Scope string_scope.
Open Scope example_scope.
From Stdlib Require Import List.
Import ListNotations.


Definition letbang : Qoreo unit :=
    do x0 ← "alice" [!- Bang (Bit false) -] ;;
    ret ().
Lemma typecheck_letbang :
    Typecheck.toplevel_typecheck ChorEnv.empty (mk letbang)
    = Typecheck.success.
Proof.
    reflexivity.
Qed.

Import Network.Choreography.
Print Choreography.t.

Definition initmeas : Qoreo unit :=
    do x ← "alice" [!- Meas (New (Bit false)) -] ;;
    ret ().
Lemma typecheck_initmeas :
    Typecheck.toplevel_typecheck ChorEnv.empty (mk initmeas)
    = Typecheck.success.
Proof. reflexivity. Qed.

Definition conditional : Qoreo unit :=
    do _ ← "alice"
      [!- Bang (Expr.If (Bit true) (Bit false) (Bit true)) -] ;;
    ret ().
Lemma typecheck_conditional :
    Typecheck.toplevel_typecheck ChorEnv.empty (mk conditional)
    = Typecheck.success.
Proof. reflexivity. Qed.

Definition newmeas : Qoreo unit :=
    do q ← "alice" [- New (Bit false) -] ;;
    do _ ← "alice" [!- Meas q -] ;;
    ret ().
Lemma typecheck_newmeas :
    Typecheck.toplevel_typecheck ChorEnv.empty (mk newmeas)
    = Typecheck.success.
Proof. reflexivity. Qed.

Definition sendbit : Qoreo unit :=
    do _ ← send "alice" (Bang (Bit true)) "bob" ;;
    ret ().
Lemma typecheck_sendbit :
    Typecheck.toplevel_typecheck ChorEnv.empty (mk sendbit)
    = Typecheck.success.
Proof. reflexivity. Qed.

Definition measure_epr : Qoreo unit :=
    do (qA, qB) ← get_entangled_pair "alice" "bob" ;;
    do _ ← "alice" [!- Meas qA -] ;;
    do _ ← "bob" [!- Meas qB -] ;;
    ret ().
Lemma typecheck_measure_epr :
    Typecheck.toplevel_typecheck ChorEnv.empty (mk measure_epr)
    = Typecheck.success.
Proof. reflexivity. Qed.
