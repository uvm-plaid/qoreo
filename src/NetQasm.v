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

Definition nat_to_decimal (n : nat) : string :=
  NilZero.string_of_uint (Nat.to_uint n).

Definition var_name (x : Var.t) : string := "x" +:+ nat_to_decimal x.

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
Fixpoint classical_peers (P : Network.Process.t) : Actor.FSet.t :=
  match P with
  | Process.Empty => Actor.FSet.empty
  | Process.Do (Network.Insn.Send _ peer) P'
  | Process.Do (Network.Insn.Receive _ peer) P' =>
    Actor.FSet.add peer (classical_peers P')
  | Process.Do _ P' => classical_peers P'

  | Process.MulticastIf _ peers P1 P2 P' =>
    (Actor.FSet.union peers
      (Actor.FSet.union (classical_peers P1)
      (Actor.FSet.union (classical_peers P2) 
                        (classical_peers P'))))
  
  | Process.ReceiveIf peer P1 P2 P' =>
    Actor.FSet.add peer
      (Actor.FSet.union (classical_peers P1)
      (Actor.FSet.union (classical_peers P2) 
                        (classical_peers P')))
  end.

Fixpoint epr_peers (P : Network.Process.t) : Actor.FSet.t :=
  match P with
  | Process.Empty => Actor.FSet.empty
  | Process.Do (Network.Insn.EPR _ peer) P' =>
    Actor.FSet.add peer (epr_peers P')
  | Process.Do _ P' => epr_peers P'

  | Process.MulticastIf _ _ P1 P2 P'
  | Process.ReceiveIf _ P1 P2 P' =>
    (Actor.FSet.union (epr_peers P1)
    (Actor.FSet.union (epr_peers P2) 
                      (epr_peers P')))
  end.

Definition render_peer_list (xs : Actor.FSet.t) : string :=
  "[" +:+ join ", " (List.map actor_literal (Actor.FSet.elements xs)) +:+ "]".

Definition render_insn (indent : nat) (insn : Network.Insn.t) : string :=
  match insn with
  | Network.Insn.Let x e =>
      line indent (var_name x +:+ " = " +:+ render_expr e)
  | Network.Insn.LetBang x e =>
      line indent (var_name x +:+ " = " +:+ render_expr e)
  | Network.Insn.LetPair x y e =>
      line indent (var_name x +:+ ", " +:+ var_name y +:+ " = " +:+ render_expr e)
  | Network.Insn.Send e peer =>
      line indent (emit_call "rt.send" [actor_literal peer; render_expr e])
  | Network.Insn.Receive x peer =>
      line indent (var_name x +:+ " = " +:+ emit_call "rt.recv" [actor_literal peer])
  | Network.Insn.EPR x peer =>
      line indent (var_name x +:+ " = " +:+ emit_call "rt.epr" [actor_literal peer])
  end.
(*To check empty branches*)  
Definition render_branch (depth : nat) (body : string) : string :=
  match body with
  | EmptyString => line depth "pass"
  | _ => body
  end.
Fixpoint render_process_body
  (depth : nat)
  (P : Network.Process.t) : string :=
  match P with

  | Process.Empty =>
      EmptyString

  | Process.Do insn P' =>
      render_insn depth insn
      +:+ render_process_body depth P'

  | Process.MulticastIf e targets P1 P2 P' =>
    let condition := render_expr e in
    let broadcasts :=
    String.concat ""
    (List.map
      (fun peer =>
        line depth
          (emit_call "rt.send" [actor_literal peer; condition]))
      (Actor.FSet.elements targets))
    in
    broadcasts
    +:+ line depth ("if " +:+ condition +:+ ":")
    +:+ render_branch (S depth) (render_process_body (S depth) P1)
    +:+ line depth "else:"
    +:+ render_branch (S depth) (render_process_body (S depth) P2)
    +:+ render_process_body depth P'

| Process.ReceiveIf source P1 P2 P' =>
    line depth ("if " +:+ emit_call "rt.recv" [actor_literal source] +:+ ":")
    +:+ render_branch (S depth) (render_process_body (S depth) P1)
    +:+ line depth "else:"
    +:+ render_branch (S depth) (render_process_body (S depth) P2)
    +:+ render_process_body depth P'

  end.
Fixpoint last_bound_var (P : Network.Process.t) : option Var.t :=
  match P with
  | Process.Empty => None
  | Process.Do insn Process.Empty =>
      match insn with
      | Network.Insn.Let x _ => Some x
      | Network.Insn.LetBang x _ => Some x
      | Network.Insn.LetPair x _ _ => Some x
      | Network.Insn.Receive x _ => Some x
      | Network.Insn.EPR x _ => Some x
      | Network.Insn.Send _ _ => None
      end
  | Process.Do _ P'
  | Process.MulticastIf _ _ _ _ P'
  | Process.ReceiveIf _ _ _ P' => last_bound_var P'
  end.

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
  render_process_body 1 P +:+
  line 2 ("return (" +:+ join ", " (List.map var_name xs) +:+ ")").
  
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
    | Some proc =>
        Some {| AppFile.party := p;
                AppFile.source := render_app b p proc xs
             |}
    | None => None
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
