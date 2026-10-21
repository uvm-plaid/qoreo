(* Algorithmic type checking *) 

From Stdlib Require Export FSets.FMapList FSets.FSetList FSets.FMapFacts OrderedType OrderedTypeEx.
From QuantumLib Require Export Matrix Pad Quantum.
From Qoreo Require Export Expr.Expr.
From Qoreo Require Export Expr.Typecheck.
From Qoreo Require Export Choreography.Choreography.
Export Var.Map.Tactics.

Structure ltap := { Df : ChorEnv.t Expr.Typ.t; Tf : ChorEnv.t nat }.

Fixpoint typecheck (G D : ChorEnv.t Expr.Typ.t) (T : ChorEnv.t nat ) (C : Choreography.t) : option ltap :=
  match C with
  | Choreography.Empty => Some {| Df := D; Tf := T |}
  | Choreography.Do (Insn.EPR A x B y) C =>
      if Actor.eq_dec A B then None else
        match Var.Map.find x (ChorEnv.find A D), Var.Map.find y (ChorEnv.find B D) with
        | None, None =>
            match typecheck (ChorEnv.remove B y (ChorEnv.remove A x G))
                    (ChorEnv.add B y Expr.Typ.QUBIT (ChorEnv.add A x Expr.Typ.QUBIT D)) T C
            with
            | Some {| Df := D'; Tf := _ |} as sltap =>
                match Var.Map.find x (ChorEnv.find A D'), Var.Map.find y (ChorEnv.find B D') with
                | None, None => sltap
                | _, _ => None
                end
            | None => None
            end
        | _, _ => None
        end
  | Choreography.Do (Insn.Send A e B y) C =>
      match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
      | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := BANG t|} =>
          typecheck (ChorEnv.add B y t G) (Actor.Map.add A Delta D) (Actor.Map.add A Theta T) C
      | _ => None           
      end 
  | Choreography.Do (Insn.LetBang A x e) C =>
      match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
      | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := BANG t|} =>
          typecheck (ChorEnv.add A x t G) (Actor.Map.add A Delta D) (Actor.Map.add A Theta T) C
      | _ => None           
      end 
  | Choreography.Do (Insn.Let A x e) C =>
      match Expr.Typecheck.typecheck (ChorEnv.find A G) (ChorEnv.find A D) (ChorEnv.find A T) e with
      | Some {| Expr.Typecheck.Df := Delta;
               Expr.Typecheck.Tf := Theta;
               Expr.Typecheck.tf := t|} =>
          match typecheck
                  (ChorEnv.add A x t G)
                  (Actor.Map.add A Delta D)
                  (Actor.Map.add A Theta T) C with
          | Some ltap as sltap =>
              match Var.Map.find x (ChorEnv.find A ltap.(Df)) with
              | None => sltap
              | _ => None
              end
          | _ => None
          end
      | _ => None           
      end 
  | _ => None (* WIP *)
  end.

Variant typecheck_result : Type := success | failure.

Definition essentially_empty {A} (CE : ChorEnv.t A) : bool :=
  let f := fun _ m b =>  Var.Map.domain_eqb m (Var.Map.empty A) && b in
  Actor.Map.M.fold f CE true.

Definition toplevel_typecheck (T : ChorEnv.t nat ) (C : Choreography.t) : typecheck_result :=
  match typecheck ChorEnv.empty ChorEnv.empty T C with
  | None => failure
  | Some {| Df := D; Tf := _ |} => if essentially_empty D then success else failure
  end.
