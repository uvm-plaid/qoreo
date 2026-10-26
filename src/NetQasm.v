From Stdlib Require Import Ascii String.
From Stdlib Require Import Numbers.DecimalString QArith.
From Stdlib Require Lists.List.
Import List.ListNotations.
Open Scope list_scope.
Open Scope string_scope.

From Qoreo Require Base.Var Base.Config Expr.Expr Choreography.Choreography Network.Network.
Import Config.
Import Choreography.


Module AppFile.
  Record t := {
    party : Actor.t;
    source : string;
  }.
End AppFile.

Definition nl : string := String (ascii_of_nat 10) EmptyString.
Definition dq : string := String (ascii_of_nat 34) EmptyString.
Infix "+:+" := String.append (at level 60, right associativity).

Definition unsupported : string := "unsupported".

Fixpoint repeat_string (n : nat) (s : string) : string :=
  match n with
  | O => EmptyString
  | S n' => s +:+ repeat_string n' s
  end.

Definition indent (n : nat) : string := repeat_string n "    ".

Definition line (n : nat) (s : string) : string := indent n +:+ s +:+ nl.

Fixpoint join (sep : string) (xs : list string) : string :=
  match xs with
  | [] => EmptyString
  | [x] => x
  | x :: xs' => x +:+ sep +:+ join sep xs'
  end.

(*

Definition nat_to_decimal (n : nat) : string :=
  NilZero.string_of_uint (Nat.to_uint n).

Definition var_name (x : Var.t) : string := "x" +:+ nat_to_decimal x.
*)

Module Var.
  From Stdlib Require Import Strings.String Strings.Ascii Arith.

  Open Scope nat_scope.
  Open Scope string_scope.

  Definition ascii_to_nat (a : ascii) : nat :=
    nat_of_ascii a.

  Fixpoint encode (s : string) : nat :=
    match s with
    | EmptyString => 0
    | String c s' =>
        1 + ascii_to_nat c + 256 * encode s'
    end.

  Fixpoint decode (fuel n : nat) : string :=
    match fuel with
    | 0 => EmptyString
    | S fuel' =>
        match n with
        | 0 => EmptyString
        | S n' =>
            String (ascii_of_nat (n' mod 256))
                  (decode fuel' (n' / 256))
        end
    end.

End Var.

Definition var_name (x : Var.t) : string := Var.decode x x.

Definition actor_literal (a : Actor.t) : string := dq +:+ a +:+ dq.

Definition bool_literal (b : bool) : string :=
  if b then "True" else "False".

Definition emit_call (fn : string) (args : list string) : string :=
  fn +:+ "(" +:+ join ", " args +:+ ")".

Import Unitary.
Definition render_unitary (u : Unitary.t) : string :=
  match u with
  | H => "H"
  | X => "X"
  | Y => "Y"
  | Z => "Z"
  | CNOT => "CNOT"
  | CS => "CS"
  | CT => "CT"
  | CSdag => "CSdag"
  | CTdag => "CTdag"
  | SGATE => "SGATE"
  | Sdag => "Sdag"
  | TGATE => "TGATE"
  | Tdag => "Tdag"
  | RZ _ => "RZ"
  | CRZ _ => "CRZ"
  end.

(* Argument to qr.Unitary: the quoted gate name, or for rotations by a·π,
   the name with a's numerator and denominator, e.g. ("RZ", 1, 4). *)
Definition render_gate (u : Unitary.t) : string :=
  let name := dq +:+ render_unitary u +:+ dq in
  match u with
  | RZ a | CRZ a =>
      "(" +:+ name +:+ ", " +:+ NilZero.string_of_int (Z.to_int (Qnum a))
          +:+ ", " +:+ NilZero.string_of_uint (Pos.to_uint (Qden a)) +:+ ")"
  | _ => name
  end.

Fixpoint render_expr (e : Expr.t) : string :=
  match e with
  | Expr.Var x => var_name x
  | Expr.Bang e1 => emit_call "qr.Bang" [render_expr e1]
  | Expr.Bit b => bool_literal b
  | Expr.If e0 e1 e2 =>
      "(" +:+ render_expr e1 +:+ " if " +:+ render_expr e0 +:+ " else " +:+ render_expr e2 +:+ ")"
  | Expr.Pair e1 e2 => "(" +:+ render_expr e1 +:+ ", " +:+ render_expr e2 +:+ ")"
  | Expr.LetBang x e1 e2 =>
      match e1 with
      | Expr.Var y =>
          if Var.eq_dec x y
          then render_expr e2
          else unsupported
      | _ => unsupported
      end
  | Expr.Meas e1 => emit_call "rt.Meas" [render_expr e1]
  | Expr.New (Expr.Bit b) => emit_call "rt.new" [bool_literal b]
  | Expr.Unitary u e1 =>
      emit_call "qr.Unitary" [render_gate u; render_expr e1]
  | _ => unsupported
  end.

(*
Fixpoint add_actor (a : Actor.t) (xs : list Actor.t) : list Actor.t :=
  match xs with
  | [] => [a]
  | x :: xs' =>
      if Actor.eq_dec a x
      then x :: xs'
      else x :: add_actor a xs'
  end.
*)
Module Process := Network.Process.
Fixpoint classical_peers (P : Process.t) : Actor.FSet.t :=
  match P with
  | Process.Ret _ | Process.Unit | Process.EPR _ =>
    Actor.FSet.empty
  | Process.LetIn _ P1 P2 | Process.Pair P1 P2 =>
    Actor.FSet.union (classical_peers P1) (classical_peers P2)
  | Process.Send _ A | Process.Receive A =>
    Actor.FSet.singleton A
  | Process.SendIf _ peers P1 P2 =>
    Actor.FSet.union peers
    (Actor.FSet.union (classical_peers P1) (classical_peers P2))
  | Process.ReceiveIf peer P1 P2 =>
    Actor.FSet.add peer
    (Actor.FSet.union (classical_peers P1) (classical_peers P2))
  end.
  

Fixpoint epr_peers (P : Network.Process.t) : Actor.FSet.t :=
  match P with
  | Process.EPR B => Actor.FSet.singleton B
  | Process.Ret _ | Process.Unit
  | Process.Send _ _ | Process.Receive _ =>
    Actor.FSet.empty
  | Process.LetIn _ P1 P2 | Process.Pair P1 P2
  | Process.SendIf _ _ P1 P2 | Process.ReceiveIf _ P1 P2 =>
    Actor.FSet.union (epr_peers P1) (epr_peers P2)
  end.

Definition render_peer_list (xs : Actor.FSet.t) : string :=
  "[" +:+ join ", " (List.map actor_literal (Actor.FSet.elements xs)) +:+ "]".

(*To check empty branches*)  
Definition render_branch (depth : nat) (body : string) : string :=
  match body with
  | EmptyString => line depth "pass"
  | _ => body
  end.

Fixpoint render_pattern (p : Network.Pattern.t) : string :=
  match p with
  | Network.Pattern.Var x | Network.Pattern.Bang x => var_name x
  | Network.Pattern.Unit => "_"
  | Network.Pattern.Pair p1 p2 =>
    "(" +:+ render_pattern p1 +:+ ", " +:+ render_pattern p2
  end.

(* To render a process into Python, we will need to turn it
   into the form
    LetIn p PE P'
   where PE is a process expression:
    PE ::= e | Unit | Pair PE PE
         | Send e B | Receive B | EPR B
     
  A process body is a linearized form of processes:
    PB ::= LetIn p PE PB
         | Ret PE
         | LocalIf e then PB else PB
*)
Module ProcessBody.
  Inductive pexpr :=
  | eRet : Expr.t -> pexpr
  | eUnit : pexpr
  | ePair : pexpr -> pexpr -> pexpr
  | eSend : Expr.t -> Actor.t -> pexpr
  | eReceive : Actor.t -> pexpr
  | eEPR : Actor.t -> pexpr
  .

  Fixpoint render_pexpr (e : pexpr) : string :=
    match e with
    | eRet e0 => render_expr e0
    | eUnit => "()"
    | ePair e1 e2 =>
      "(" +:+ render_pexpr e1 +:+ ", " +:+ render_pexpr e2 +:+ ")"
    | eSend e0 peer =>
      emit_call "rt.send" [actor_literal peer; render_expr e0]
    | eReceive peer =>
      emit_call "rt.recv" [actor_literal peer]
    | eEPR peer =>
      emit_call "rt.epr" [actor_literal peer]
    end.

  Inductive pbody :=
  | bLetIn : Network.Pattern.t -> pexpr -> pbody -> pbody
  | bRet   : pexpr -> pbody
  | bIf    : pexpr -> pbody -> pbody -> pbody
  .

  Fixpoint render_pbody (depth : nat) b : string :=
    match b with
    | bRet e => line depth ("return " +:+ render_pexpr e)
    | bLetIn p e b' =>
      line depth (render_pattern p +:+ " = " +:+ render_pexpr e)
      +:+ render_pbody depth b'
    | bIf e b1 b2 =>
      line depth ("if " +:+ render_pexpr e +:+ ":")
      +:+ (render_pbody (1+depth) b1)
      +:+
      line depth "else:"
      +:+ (render_pbody (1+depth) b2)
    end.


  Fixpoint bPair' (e1 : pexpr) (b2 : pbody) : pbody :=
    match b2 with
    | bLetIn p e2 b2' => bLetIn p e2 (bPair' e1 b2')
    | bRet e2 => bRet (ePair e1 e2)
    | bIf e b21 b22 =>
      bIf e (bPair' e1 b21) (bPair' e1 b22)
    end.
  Fixpoint bPair (b1 b2 : pbody) : pbody :=
    match b1 with
    | bLetIn p e1 b1' => bLetIn p e1 (bPair b1' b2)
    | bRet e1 => bPair' e1 b2
    | bIf e b11 b12 =>
      bIf e (bPair b11 b2) (bPair b12 b2)
    end.

  Fixpoint bBroadcast e tgts continuation :=
    match tgts with
    | [] => continuation
    | A::tgts' => bLetIn Network.Pattern.Unit (eSend e A)
                  (bBroadcast e tgts' continuation)
    end.

  Fixpoint bLet p (b1 b2 : pbody) : pbody :=
    match b1 with
    | bRet e1 => bLetIn p e1 b2
    | bLetIn p1 e1 b1' => bLetIn p1 e1 (bLet p b1' b2)
    | bIf e1 b11 b12   =>
      bIf e1 (bLet p b11 b2) (bLet p b12 b2)
    end.

  Fixpoint pbody_of_process (P : Process.t) : pbody :=
    match P with
    | Process.Ret e => bRet (eRet e)
    | Process.Unit => bRet eUnit
    | Process.Pair P1 P2 =>
      bPair (pbody_of_process P1) (pbody_of_process P2)
    | Process.Send e A => bRet (eSend e A)
    | Process.Receive A => bRet (eReceive A)
    | Process.EPR A => bRet (eEPR A)
    | Process.SendIf e As P1 P2 =>
      bBroadcast e (Actor.FSet.elements As)
      (bIf (eRet e)
           (pbody_of_process P1)
           (pbody_of_process P2)
      )
    | Process.ReceiveIf A P1 P2 =>
      bIf (eReceive A) (pbody_of_process P1) (pbody_of_process P2)
    | Process.LetIn p P1 P2 =>
      bLet p (pbody_of_process P1) (pbody_of_process P2)
    end.

End ProcessBody.

Definition render_process_body depth P : string :=
      ProcessBody.render_pbody depth
        (ProcessBody.pbody_of_process P).


Inductive Backend := NetSquid | NetQASM.

Definition render_import (b : Backend) :=
  match b with
  | NetSquid => "import qoreo_netsquid_runtime as qr"
  | NetQASM  => "import qoreo_netqasm_runtime as qr"
  end.

Definition render_app (b : Backend) (self : Actor.t) (P : Network.Process.t) (xs : list Var.t) : string :=
  let classicals := classical_peers P in
  let eprs := epr_peers P in
  render_import b +:+ nl +:+ nl +:+
  "def main(app_config=None):" +:+ nl +:+
  line 1 ("rt = qr.Runtime(" +:+
            actor_literal self +:+ ", app_config, " +:+
            render_peer_list classicals +:+ ", " +:+
            render_peer_list eprs +:+ ")") +:+
  line 1 "with rt.connection():" +:+
  render_process_body 2 P.
  
  Definition epp_vars (p : Actor.t) (env : Var.Map.t Actor.t) (xs : list Var.t) 
              : list Var.t :=
    let f := fun x =>
      match Var.Map.find x env with
      | Some A => if Actor.eq_dec p A then true else false
      | _ => false
      end
    in
    List.filter f xs.

  Definition render_party (b : Backend) (choreo : Choreography.t)
                          (p : Actor.t)
                          (xs : list Var.t)
    : option AppFile.t :=
    match Network.epp p choreo with
    | proc =>
        Some {| AppFile.party := p;
                AppFile.source := render_app b p proc xs
             |}
    end.

  Fixpoint render_parties b (choreo : Choreography.t)
                            (ps : list Actor.t)
                            (return_values : Actor.Map.t (list Var.t))
                            : option (list AppFile.t) :=
    match ps with
    | [] => Some []
    | p :: ps' =>
      let p_xs := Prelim.maybe (Actor.Map.find p return_values) [] in
        match render_party b choreo p p_xs,
              render_parties b choreo ps' return_values with
        | Some app, Some apps => Some (app :: apps)
        | _, _ => None
        end
    end.
