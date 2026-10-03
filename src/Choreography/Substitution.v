
(*** Substitution lemma for non-linear variables *)
Lemma wt_subst_bang : forall C tau G D T A x v,
    WellTyped (ChorEnv.add A x tau G) D T C ->
    Expr.WellTyped (Var.Map.empty _) (Var.Map.empty _) (Var.Map.empty _) v tau ->
    WellTyped G D T (Choreography.subst A x v C).
Proof.
    intros C. induction C as [| I C IHC ].
    
  (* Case C = Nil *)
    - intros tau G D T A x v HWT HWTV.
      unfold Choreography.subst.
      inversion HWT; subst.
      apply Nil; auto.

    (* Case C = I::C' *) 
    - intros tau G D T A x v HWT HWTV.
      destruct I as [ A' e B y | A' y B z | A' y e | A' y e | A' y z e ].

      (* Case Send *)
      + inversion HWT; subst.

        specialize (IHC tau
                      (ChorEnv.add B y tau0 G)
                      (Actor.Map.add A' DeltaA2 D)
                      (Actor.Map.add A' ThetaA2 T)
                      A x v).
        
        assert (A = A' \/ A <> A') as HCasesAeqA'.
        tauto.
        
        destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
        
        (* Case A = A' *)
        {
          rewrite <- HCasesAeqA'L in *.

          unfold ChorEnv.add in H8.
          rewrite -> find_add in H8.
          pose proof
            (Expr.wt_subst_bang e tau (ChorEnv.find A G) DeltaA1 ThetaA1 x v (Expr.BANG tau0)
            HWTV H8) as HEWTSB.

          - eapply Send; auto.

            {
              destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              { eauto. }
              { contradiction. }
            }

            { 
              fold Choreography.subst.
              unfold Insn.rebound_in.
              destruct (Insn.bind_eqb (A, x) (B, y)) eqn:Hbeq.
              { 
                destruct (beq A B x y) as [HbeqL _].
                destruct (HbeqL Hbeq) as [HABeq _].
                contradiction.
              }
              {
                rewrite addadd5 in H9; auto.
              }
            }

            { auto. }
            { auto. }
        }
        (* Case A <> A' *)
        {
          rewrite find_ab_neq1 in H8; auto.

          eapply Send; auto.
                   
          {
            destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. }
          }
            { 
              fold Choreography.subst.
              unfold Insn.rebound_in.
              destruct (Insn.bind_eqb (A, x) (B, y)) eqn:Hbeq.
              { 
                destruct (beq A B x y) as [HbeqL _].
                destruct (HbeqL Hbeq) as [HABeqL HABeqR].
                rewrite <- HABeqL in *.
                rewrite <- HABeqR in *.
                rewrite overwrite in H9.
                eauto.
              }
              {
                rewrite addadd5 in H9; auto.
              }
            }

            { auto. }
            
            { auto. }
        }

      (* Case EPR *)
      + inversion HWT; subst.
        
        assert (A = A' \/ A <> A') as HCasesAeqA'.
        tauto.
        
        destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
        
        (* Case A = A' *)
        {
          rewrite <- HCasesAeqA'L in *.

          eapply EPR; auto.

          {
            fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.EPR A y B z)) eqn:Hrin.
            {
              unfold Insn.rebound_in in Hrin.
              rewrite orb_true_iff in Hrin.
              destruct Hrin.
              {
                destruct (beq A A x y) as [HbeqL _].
                destruct (HbeqL H) as [_ HAAeqR].
                rewrite <- HAAeqR in *.
                rewrite rmadd1 in H8.
                auto.
              }
              {
                destruct (beq A B x z) as [HbeqL _].
                destruct (HbeqL H) as [HAAeqL _].
                contradiction.
              }
            }
            {
              unfold Insn.rebound_in in Hrin.
              rewrite orb_false_iff in Hrin.
              destruct Hrin as [HbeqA HbeqB].

              rewrite rmadd2 in H8; auto.
              rewrite rmadd2 in H8; auto.
              
              apply (IHC tau
                       (ChorEnv.remove B z (ChorEnv.remove A y G))
                       (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A y Expr.QUBIT D))
                       T A x v H8 HWTV).
            }
          }
        }
        {
          apply EPR; auto.
          
          {
            fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.EPR A' y B z)) eqn:Hrin.
            {
              unfold Insn.rebound_in in Hrin.
              rewrite orb_true_iff in Hrin.
              destruct Hrin.
              {
                destruct (beq A A' x y) as [HbeqL _].
                destruct (HbeqL H) as [HAAeqL _].
                contradiction.
              }
              {
                assert (Insn.bind_eqb (A, x) (A', y) <> true) as HnbeqAA'.
                apply (nbeq A A' x y HCasesAeqA'R).
                destruct (not_true_iff_false (Insn.bind_eqb (A, x) (A', y))) as [HntL _].
                pose proof (HntL HnbeqAA').
                destruct (beq A B x z) as [HbeqL _].
                destruct (HbeqL H) as [HABeqL HABeqR].
                rewrite <- HABeqL in *.
                rewrite <- HABeqR in *.
                rewrite -> rmadd2 in H8; auto.
                rewrite -> (rmadd1 (ChorEnv.remove A' y G) A x tau) in H8.
                auto.
              }
            }
            {
              unfold Insn.rebound_in in Hrin.
              rewrite orb_false_iff in Hrin.
              destruct Hrin as [HneqA HneqB].
              rewrite rmadd2 in H8; auto.
              rewrite rmadd2 in H8; auto.
              apply (IHC
                       tau 
                       (ChorEnv.remove B z (ChorEnv.remove A' y G))
                       (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A' y Expr.QUBIT D))
                       T A x v H8 HWTV).
            }
          }
        }

      (* Case Let *)
      +  inversion HWT; subst.
        
         assert (A = A' \/ A <> A') as HCasesAeqA'.
         tauto.
         
         destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
         
         (* Case A = A' *)
         {
           rewrite <- HCasesAeqA'L in *.
           
           eapply LetIn; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
             {
               unfold ChorEnv.add in H3.
               rewrite find_add in H3.
               pose proof
                 (Expr.wt_subst_bang e tau (ChorEnv.find A G) DeltaA1 ThetaA1 x v tau0
                    HWTV H3) as HEWTSB.
               eauto.
             }
             { contradiction. }
           }

           {
             fold Choreography.subst.
             unfold Insn.rebound_in.
             destruct (Insn.bind_eqb (A, x) (A, y)) eqn:Hbeq.
             { 
               destruct (beq A A x y) as [HbeqL _].
               destruct (HbeqL Hbeq) as [_ Heqxy].
               rewrite <- Heqxy in *.
               rewrite rmadd1 in H7.
               eauto.
             }
             {
               rewrite rmadd2 in H7; auto.
               apply (IHC tau
                        (ChorEnv.remove A y G)
                        (Actor.Map.add A (Var.Map.add y tau0 DeltaA2) D)
                        (Actor.Map.add A ThetaA2 T)
                        A x v H7 HWTV).
             }
           }

           { auto. }
           { auto. }
           { auto. }
         }
         {
           eapply LetIn; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
             { contradiction. }
             { 
               rewrite find_ab_neq1 in H3; auto.
               eauto.
             }
           }

           {
             fold Choreography.subst.
             unfold Insn.rebound_in.
             destruct (Insn.bind_eqb (A, x) (A', y)) eqn:Hbeq.
             { 
               destruct (beq A A' x y) as [HbeqL _].
               destruct (HbeqL Hbeq) as [HeqAB _].
               contradiction.
             }
             {
               rewrite rmadd2 in H7; auto.
               apply (IHC tau
                        (ChorEnv.remove A' y G)
                        (Actor.Map.add A' (Var.Map.add y tau0 DeltaA2) D)
                        (Actor.Map.add A' ThetaA2 T)
                        A x v H7 HWTV).
             }
           }

           { auto. }
           { auto. }
           { auto. }

         }

      (* Case LetBang *)
      +  inversion HWT; subst.
                 
         assert (A = A' \/ A <> A') as HCasesAeqA'.
         tauto.
         
         destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
         
         (* Case A = A' *)
         {
           rewrite <- HCasesAeqA'L in *.
           
           eapply LetBang; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
             {
               unfold ChorEnv.add in H6.
               rewrite find_add in H6.
               pose proof
                 (Expr.wt_subst_bang e tau (ChorEnv.find A G) DeltaA1 ThetaA1 x v (Expr.BANG tau0)
                    HWTV H6) as HEWTSB.
               eauto.
             }
             { contradiction. }
           }

           {
             fold Choreography.subst.
             unfold Insn.rebound_in.
             destruct (Insn.bind_eqb (A, x) (A, y)) eqn:Hbeq.
             { 
               destruct (beq A A x y) as [HbeqL _].
               destruct (HbeqL Hbeq) as [_ Heqxy].
               rewrite <- Heqxy in *.
               rewrite overwrite in H7.
               eauto.
             }
             {
               rewrite addadd5 in H7; auto.
               apply (IHC tau
                        (ChorEnv.add A y tau0 G)
                        (Actor.Map.add A DeltaA2 D)
                        (Actor.Map.add A ThetaA2 T)
                        A x v H7 HWTV).
             }
           }

           { auto. }
           { auto. }
         }
         {
           eapply LetBang; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
             { contradiction. }
             { 
               rewrite find_ab_neq1 in H6; auto.
               eauto.
             }
           }

           {
             fold Choreography.subst.
             unfold Insn.rebound_in.
             destruct (Insn.bind_eqb (A, x) (A', y)) eqn:Hbeq.
             { 
               destruct (beq A A' x y) as [HbeqL _].
               destruct (HbeqL Hbeq) as [HeqAB _].
               contradiction.
             }
             {
               rewrite addadd5 in H7; auto.
               apply (IHC tau
                        (ChorEnv.add A' y tau0 G)
                        (Actor.Map.add A' DeltaA2 D)
                        (Actor.Map.add A' ThetaA2 T)
                        A x v H7 HWTV).
             }
           }

           { auto. }
           { auto. }
         }

      (* Case LetPair *)
      + inversion HWT; subst.
        
        assert (A = A' \/ A <> A') as HCasesAeqA'.
        tauto.
        
        destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].
        
        (* Case A = A' *)
        {
          rewrite <- HCasesAeqA'L in *.
          
          eapply LetPair; auto.
          
          {
            destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
            {
              unfold ChorEnv.add in H4.
              rewrite find_add in H4.
              pose proof
                (Expr.wt_subst_bang e tau
                   (ChorEnv.find A G) DeltaA1 ThetaA1
                   x v (Expr.Tensor tau1 tau2)
                   HWTV H4) as HEWTSB.
              eauto.
            }
            { contradiction. }
          }
          
          {
            fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.LetPair A y z e)) eqn:Hrbi.
            {
              unfold Insn.rebound_in in Hrbi.
              rewrite orb_true_iff in Hrbi.
              destruct Hrbi as [HrbiA | HrbiB].
              {
                rewrite remrem.
                rewrite remrem in H5.
                destruct (beq A A x y) as [HbeqL _].
                destruct (HbeqL HrbiA) as [_ Heqxy].
                rewrite <- Heqxy in *.
                rewrite rmadd1 in H5.
                eauto.
              }
              {
                destruct (beq A A x z) as [HbeqL _].
                destruct (HbeqL HrbiB) as [_ Heqxz].
                rewrite <- Heqxz in *.
                rewrite rmadd1 in H5.
                eauto.
              }                
            }
            {
              unfold Insn.rebound_in in Hrbi.
              rewrite orb_false_iff in Hrbi.
              destruct Hrbi as [HrbiA HrbiB].

              rewrite rmadd2 in H5; auto.
              rewrite rmadd2 in H5; auto.
               apply (IHC tau
                        (ChorEnv.remove A y (ChorEnv.remove A z G))
                        (Actor.Map.add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                        (Actor.Map.add A ThetaA2 T) 
                        A x v H5 HWTV).
            }
          }

          { auto. }
          { auto. }
          { auto. }
          { auto. }
        }
        {
          eapply LetPair; auto.

           {
             destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
             { contradiction. }
             { 
               rewrite find_ab_neq1 in H4; auto.
               eauto.
             }
           }

           {
             fold Choreography.subst.
             destruct (Insn.rebound_in A x (Insn.LetPair A' y z e)) eqn:Hrbi.
             {
               unfold Insn.rebound_in in Hrbi.
               rewrite orb_true_iff in Hrbi.
               destruct Hrbi as [HrbiA | HrbiB].
               {
                 destruct (beq A A' x y) as [HbeqL _].
                 destruct (HbeqL HrbiA) as [HeqAB _].
                 contradiction.
               }
               {
                 destruct (beq A A' x z) as [HbeqL _].
                 destruct (HbeqL HrbiB) as [HeqAB _].
                 contradiction.                 
               }
             }
             {
               unfold Insn.rebound_in in Hrbi.
               rewrite orb_false_iff in Hrbi.
               destruct Hrbi as [HrbiA HrbiB].
               {
                 rewrite rmadd2 in H5; auto.
                 rewrite rmadd2 in H5; auto.
                 apply (IHC tau
                          (ChorEnv.remove A' y (ChorEnv.remove A' z G))
                          (Actor.Map.add A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                          (Actor.Map.add A' ThetaA2 T)
                          A x v H5 HWTV).
               }
             }
           }
           { auto. }
           { auto. }
           { auto. }
           { auto. }
         }
Qed.        

(** Substitution is the identity for variables that don't occur free in C *)
Lemma subst_not_in : forall C A x v G D T,
    WellTyped G D T C ->
    ~ (Var.Map.In x (ChorEnv.find A D)) ->
    ~ (Var.Map.In x (ChorEnv.find A G)) ->
    (Choreography.subst A x v C) = C.
Proof.
  intros C A x v. 

  induction C as [| I C].

  - intros G D T HWTC HninD HninG.
    simpl; auto.

  - intros G D T HWTC HninD HninG.
    destruct I as [ A' e B y | A' y B z | A' y e | A' y e | A' y z e ].

    (* Case Send *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.

      assert
        ((if Actor.FSet.MF.eq_dec A A' then Expr.subst x v e else e) = e) as Hgoale.
      {
        destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
        {
          subst.

          apply(Expr.subst_not_in e x v 
                  (ChorEnv.find A' G) DeltaA1 ThetaA1 (Expr.BANG tau)
                  H8 HninG
                  (nin_partition x (ChorEnv.find A' D) DeltaA1 DeltaA2 HninD H10)).
        }
        { auto. }
      }

      assert
        ((if Insn.rebound_in A x (Insn.Send A' e B y) then C else Choreography.subst A x v C) = C) as HgoalC.
      {
        unfold Insn.rebound_in.
        destruct (Insn.bind_eqb (A, x) (B, y)) eqn:Hbeq.
        {
          setoid_rewrite Hbeq.
          auto.
        }
        {
          setoid_rewrite Hbeq.

          specialize (IHC
                        (ChorEnv.add B y tau G)
                        (Actor.Map.add A' DeltaA2 D)
                        (Actor.Map.add A' ThetaA2 T)
                        H9).

          pose proof (find_nbeq G A x B y tau Hbeq HninG) as Hnbeq.

          assert (~ Var.Map.In x (ChorEnv.find A (Actor.Map.add A' DeltaA2 D))) as HninDadd.
          {
            assert (A = A' \/ A <> A') as HAA'eq.
            tauto.
            destruct HAA'eq as [HAA'eqL |  HAA'eqR].
            {
              rewrite <- HAA'eqL in *.
              rewrite find_add; auto.
              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A D) DeltaA1 DeltaA2 H10) as Hpart.
              apply (nin_partition x (ChorEnv.find A D) DeltaA2 DeltaA1 HninD Hpart).
            }
            {
              rewrite (find_ab_neq2 A A' DeltaA2 D HAA'eqR).
              auto.
            }
          }

          apply (IHC HninDadd Hnbeq).
        }
      }
      
      setoid_rewrite Hgoale.
      setoid_rewrite HgoalC.
      auto.

    (* Case EPR *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.

      assert
        ((if Insn.rebound_in A x (Insn.EPR A' y B z) then C else Choreography.subst A x v C) = C)
        as HgoalC.
      {
        destruct (Insn.rebound_in A x (Insn.EPR A' y B z)) eqn:Hrbi.
        { auto. }
        {
          unfold Insn.rebound_in in Hrbi.
          rewrite orb_false_iff in Hrbi.
          destruct Hrbi as [HrbiA HrbiB].
          
          specialize (IHC
                        (ChorEnv.remove B z (ChorEnv.remove A' y G))
                        (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A' y Expr.QUBIT D))
                        T
                        H8).

          pose proof (nin_remove_ce (ChorEnv.remove A' y G) A x B z
                        (nin_remove_ce G A x A' y HninG)) as HninGzy.

          pose proof (find_nbeq
                        (ChorEnv.add A' y Expr.QUBIT D)
                        A x B z Expr.QUBIT HrbiB
                        (find_nbeq D A x A' y Expr.QUBIT HrbiA HninD)) as HninDzy.

          apply (IHC HninDzy HninGzy).
        }
      }

      setoid_rewrite HgoalC; auto.

      (* Case Let *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.
      
      assert
        ((if Actor.FSet.MF.eq_dec A A' then Expr.subst x v e else e) = e) as Hgoale.
      {
        destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
        {
          subst.

          apply(Expr.subst_not_in e x v 
                  (ChorEnv.find A' G) DeltaA1 ThetaA1 tau
                  H3 HninG
                  (nin_partition x (ChorEnv.find A' D) DeltaA1 DeltaA2 HninD H8)).
        }
        { auto. }
      }

      assert
        ((if Insn.rebound_in A x (Insn.Let A' y e) then C else Choreography.subst A x v C) = C) as HgoalC.
      {
        unfold Insn.rebound_in.
        destruct (Insn.bind_eqb (A, x) (A', y)) eqn:Hbeq.
        {
          setoid_rewrite Hbeq.
          auto.
        }
        {
          setoid_rewrite Hbeq.

          specialize (IHC
                        (ChorEnv.remove A' y G)
                        (Actor.Map.add A' (Var.Map.add y tau DeltaA2) D) 
                        (Actor.Map.add A' ThetaA2 T)
                        H7).

          pose proof (nin_remove_ce G A x A' y HninG) as Hnbeq.

          assert (~ Var.Map.In x (ChorEnv.find A (Actor.Map.add A' (Var.Map.add y tau DeltaA2) D)))
            as HninDadd.
          {
            assert (A = A' \/ A <> A') as HAA'eq.
            tauto.
            destruct HAA'eq as [HAA'eqL |  HAA'eqR].
            {
              rewrite <- HAA'eqL in *.
              rewrite find_add; auto.

              
              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A D) DeltaA1 DeltaA2 H8) as Hpart.
              
              apply (nin_mapl DeltaA2 x y tau (nbeqeq A x y Hbeq)
                       (nin_partition x (ChorEnv.find A D) DeltaA2 DeltaA1 HninD Hpart)).
            }
            {
              rewrite (find_ab_neq2 A A' (Var.Map.add y tau DeltaA2) D HAA'eqR).
              auto.
            }
          }

          apply (IHC HninDadd Hnbeq).
        }
      }

      setoid_rewrite Hgoale.
      setoid_rewrite HgoalC.
      auto.

    (* Case LetBang *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.

      assert
        ((if Actor.FSet.MF.eq_dec A A' then Expr.subst x v e else e) = e) as Hgoale.
      {
        destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
        {
          subst.

          apply(Expr.subst_not_in e x v 
                  (ChorEnv.find A' G) DeltaA1 ThetaA1 (Expr.BANG tau)
                  H6 HninG
                  (nin_partition x (ChorEnv.find A' D) DeltaA1 DeltaA2 HninD H8)).
        }
        { auto. }
      }

      assert
        ((if Insn.rebound_in A x (Insn.LetBang A' y e) then C else Choreography.subst A x v C) = C) as HgoalC.
      {
        unfold Insn.rebound_in.
        destruct (Insn.bind_eqb (A, x) (A', y)) eqn:Hbeq.
        {
          setoid_rewrite Hbeq.
          auto.
        }
        {
          setoid_rewrite Hbeq.

          specialize (IHC
                        (ChorEnv.add A' y tau G)
                        (Actor.Map.add A' DeltaA2 D)
                        (Actor.Map.add A' ThetaA2 T)
                        H7).

          pose proof (find_nbeq G A x A' y tau Hbeq HninG) as Hnbeq.

          assert (~ Var.Map.In x (ChorEnv.find A (Actor.Map.add A' DeltaA2 D))) as HninDadd.
          {
            assert (A = A' \/ A <> A') as HAA'eq.
            tauto.
            destruct HAA'eq as [HAA'eqL |  HAA'eqR].
            {
              rewrite <- HAA'eqL in *.
              rewrite find_add; auto.
              pose proof (@Var.Map.Properties.Partition_sym _
                            (ChorEnv.find A D) DeltaA1 DeltaA2 H8) as Hpart.
              apply (nin_partition x (ChorEnv.find A D) DeltaA2 DeltaA1 HninD Hpart).
            }
            {
              rewrite (find_ab_neq2 A A' DeltaA2 D HAA'eqR).
              auto.
            }
          }

          apply (IHC HninDadd Hnbeq).
        }
      }
      
      setoid_rewrite Hgoale.
      setoid_rewrite HgoalC.
      auto.

    (* Case LetPair *)
    + inversion HWTC; subst.
      unfold Choreography.subst.
      fold Choreography.subst.
      unfold Insn.subst.
      
      assert
        ((if Actor.FSet.MF.eq_dec A A' then Expr.subst x v e else e) = e) as Hgoale.
      {
        destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
        {
          subst.

          apply(Expr.subst_not_in e x v 
                  (ChorEnv.find A' G) DeltaA1 ThetaA1 (Expr.Tensor tau1 tau2)
                  H4 HninG
                  (nin_partition x (ChorEnv.find A' D) DeltaA1 DeltaA2 HninD H9)).
        }
        { auto. }
      }

      assert
        ((if Insn.rebound_in A x (Insn.LetPair A' y z e) then C else Choreography.subst A x v C) = C) as HgoalC.
      {
        destruct (Insn.rebound_in A x (Insn.LetPair A' y z e)) eqn:Hrbi.
        { auto. }        
        {
          unfold Insn.rebound_in in Hrbi.
          rewrite orb_false_iff in Hrbi.
          destruct Hrbi as [HrbiA HrbiB].
          {
            specialize (IHC
                          (ChorEnv.remove A' y (ChorEnv.remove A' z G))
                          (Actor.Map.add A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                          (Actor.Map.add A' ThetaA2 T)                          
                          H5).

            pose proof (nin_remove_ce (ChorEnv.remove A' z G) A x A' y
                          (nin_remove_ce G A x A' z HninG)) as HninGzy.

            assert (~ Var.Map.In x
                      (ChorEnv.find A
                         (Actor.Map.add A'
                            (Var.Map.add y tau1
                               (Var.Map.add z tau2 DeltaA2)) D)))
              as HninDadd.
            {
              assert (A = A' \/ A <> A') as HAA'eq.
              tauto.
              destruct HAA'eq as [HAA'eqL |  HAA'eqR].
              {
                rewrite <- HAA'eqL in *.
                rewrite find_add; auto.

                pose proof (nbeqeq A x y HrbiA) as Hnexy.
                pose proof (nbeqeq A x z HrbiB) as Hnexz.
                
                pose proof (@Var.Map.Properties.Partition_sym _
                              (ChorEnv.find A D) DeltaA1 DeltaA2 H9) as Hpart.

                pose proof (nin_partition x (ChorEnv.find A D) DeltaA2 DeltaA1 HninD Hpart) as HninDA2.

                apply (nin_mapl (Var.Map.add z tau2 DeltaA2) x y tau1 Hnexy
                              (nin_mapl DeltaA2 x z tau2 Hnexz HninDA2)).
              }
              {
                rewrite (find_ab_neq2 A A' (Var.Map.add y tau1  (Var.Map.add z tau2 DeltaA2)) D HAA'eqR).
                auto.
              }
            }
            
            apply (IHC HninDadd HninGzy).
          }
        }
      }
      
      setoid_rewrite Hgoale.
      setoid_rewrite HgoalC.
      auto.
Qed.

(** Substitution lemma for linear varibles *)
Lemma wt_subst_lin : forall C ThetaA1 ThetaA2 tau G D T A x v,
    Expr.WellTyped (Var.Map.empty _) (Var.Map.empty _) ThetaA1 v tau ->
    WellTyped G (ChorEnv.add A x tau D) (Actor.Map.add A ThetaA2 T) C ->
    Var.Map.Partition (ChorEnv.find A T) ThetaA1 ThetaA2 ->
    ~ Var.Map.In x (ChorEnv.find A G) ->
    ~ Var.Map.In x (ChorEnv.find A D) ->
    WellTyped G D T (Choreography.subst A x v C).
Proof.
  intros C. induction C as [| I C IHC ].

  (* Case C = Nil is not possible. *)
  - intros ThetaA1 ThetaA2 tau G D T A x v Hv HC HinG HinD HninD.
    inversion HC; subst.
    pose proof (add_empty_delta A x tau D).
    contradiction.
    
  (* Case C = I::C' *) 
  - intros ThetaA1 ThetaA2 tau G D T A x v Hv HC HinT HninG HninD.
    destruct I as [ A' e B y | A' y B z | A' y e | A' y e | A' y z e ].

    (* Case Send *)
    + inversion HC. subst.

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.
        
        assert (Var.Map.In x DeltaA1 \/ ~ Var.Map.In x DeltaA1) as HESL.
        tauto.

        destruct HESL as [HinDA | HninDA]. 
        (* Case x in e *)          
        {
          (* prepare witness for expression e typing and partioning facts. *)
          rewrite -> (add_find D A x tau) in H10.
          pose proof (inin (ChorEnv.find A D) DeltaA1 DeltaA2
                        x tau H10 HinDA) as Hinin.
          destruct (mapsto_destruct x tau DeltaA1 Hinin) as [DeltaA1' HDA'].
          destruct HDA' as [HDA'A HDA'B].
          rewrite -> HDA'A in H8.
          pose proof 
            (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
               (Var.Map.concat ThetaA1 ThetaA0) x v (Expr.BANG tau0) Hv H8) as HWTS.
          rewrite -> (find_add A ThetaA2 T) in H11.
          
          (* partioning facts. *)
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H11)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          (* e typing witness. *)
          specialize (HWTS HPartitionA HninG HDA'B).
          
          (* prepare witness for choreography C typing *)
          rewrite -> (ChorEnv.addadd1 A D DeltaA2 x tau) in H9.
          rewrite -> (ChorEnv.addadd2 A T ThetaA3 ThetaA2) in H9.
          
          (* prepare hypotheses for partitioning requirements *)
          assert (H : Var.Map.Equal (Var.Map.add x tau DeltaA1') DeltaA1).
          { symmetry. auto. }
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau H H10 HninD HDA'B) as Hnin.
          pose proof (subst_not_in
                        C A x v
                        (ChorEnv.add B y tau0 G)
                        (Actor.Map.add A DeltaA2 D)
                        (Actor.Map.add A ThetaA3 T)
                        H9) as HCSL.
          rewrite -> (find_add A DeltaA2 D) in HCSL.
          destruct Hnin as [HninA HninB].
          
          (* prove main goal in subcases *)
          - eapply Send.
            
            + auto.
              
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              { eauto. }
              { contradiction. }
              
            + fold Choreography.subst.
              destruct (Insn.rebound_in A x) eqn:Heq.
              {
                assert (~ (Insn.rebound_in A x (Insn.Send A e B y) = true)).
                simpl.
                eapply (nbeq A B x y H7).
                contradiction.
              }
              {
                rewrite (find_ab_neq1 A B y tau0 G H7) in HCSL.
                specialize (HCSL HninA HninG).
                rewrite -> HCSL.
                eauto.
              }
              
            + auto.
              
            + auto.
        }
        (* case x not in e *)
        {
          pose proof (Expr.subst_not_in e x v
                        (ChorEnv.find A G) DeltaA1 ThetaA0 (Expr.BANG tau0)
                        H8 HninG HninDA) as Hesubst.
          rewrite -> (add_find D A x tau) in H10.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H10 HninDA) as Hini.

          (* partioning facts *)
          rewrite -> (find_add A ThetaA2 T) in H11.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H11)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          
          (* prove main goal in subcases *)
          - eapply Send.
            
            + auto.
              
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              {
                rewrite -> Hesubst.
                eauto.
              }
              { auto. }
              
            + fold Choreography.subst.
              destruct (Insn.rebound_in A x (Insn.Send A e B y)) eqn:Heq.
              { 
                assert (~ (Insn.rebound_in A x (Insn.Send A e B y) = true)).
                simpl.
                apply (nbeq A B x y H7).
                contradiction.
              }
              {
                (* specialize and apply IH *)
                specialize (IHC ThetaA1 ThetaA3 tau
                              (ChorEnv.add B y tau0 G)
                              (Actor.Map.add A (Var.Map.remove x DeltaA2) D)
                              (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T)
                              A x v
                              Hv).
                assert (IHWT : WellTyped (ChorEnv.add B y tau0 G)
                                         (ChorEnv.add A x tau (Actor.Map.add A
                                            (Var.Map.remove (elt:=Expr.typ) x DeltaA2) D))
                                         (Actor.Map.add A ThetaA3
                                            (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T))
                                         C).
                {
                  eapply WellTypedProper; eauto.
                  + reflexivity.
                  + 
                    rewrite add_remove; auto.
                    unfold ChorEnv.add.
                    rewrite ChorEnv.addadd2.
                    reflexivity.
                  + rewrite ChorEnv.addadd2. rewrite ChorEnv.addadd2. reflexivity. 
                }
                specialize (IHC IHWT).
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                specialize (IHC HPartitionB).
                rewrite -> (find_ab_neq1 A B y tau0 G H7) in IHC.
                specialize (IHC HninG).
                rewrite -> (find_add A (Var.Map.remove (elt:=Expr.typ) x DeltaA2) D) in IHC.
                specialize (IHC (nin_remove DeltaA2 x)).
                eauto.
              }
              
            + apply (partition_remove (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H10 HninD HninDA).
              
            + auto.
        }
      }
      (* Case A <> A' *)
      {
        - eapply Send.

          + auto.

          + destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. }

          + fold Choreography.subst.          
            rewrite -> (addadd3 D A x tau A' DeltaA2) in H9; auto.
            
            destruct (Insn.rebound_in A x (Insn.Send A' e B y)) eqn:Heq.
            {
              assert  (~ Insn.rebound_in A x (Insn.Send A' e B y) = true).

              unfold Insn.rebound_in.
              destruct (Insn.bind_eqb_false (A,x) (B,y)) as [HBEQA HBEQB].
              destruct (not_true_iff_false (Insn.bind_eqb (A, x) (B, y))) as [HNTFA HNTFB].
              apply HNTFB.
              apply HBEQB.

              pose proof (wt_disjoint C A
                            (ChorEnv.add B y tau0 G)
                            (ChorEnv.add A x tau (Actor.Map.add A' DeltaA2 D))
                            (Actor.Map.add A' ThetaA3 (Actor.Map.add A ThetaA2 T))
                            H9) as HWTDJ.

              assert (A = B \/ A <> B) as HCasesAeqB.
              tauto.
              
              destruct HCasesAeqB as [HCasesAeqBL | HCasesAeqBR].
              
              {
                rewrite <- HCasesAeqBL in *.
                assert (A <> A'); auto.
                pose proof (nin_dj x
                              (ChorEnv.find A (ChorEnv.add A y tau0 G))
                              (ChorEnv.find A (ChorEnv.add A x tau (Actor.Map.add A' DeltaA2 D)))
                              HWTDJ
                              (in_beq (Actor.Map.add A' DeltaA2 D) A x tau)) as Hnindj.
                rewrite -> (add_find G A y tau0) in Hnindj.
                pose proof (nin_nxeq (ChorEnv.find A G) x y tau0 Hnindj).
                apply (Insn.nbeqlr (A,x) (A,y)).
                auto.
              }
              {
                apply (Insn.nbeqlr (A,x) (B,y)).
                auto.
              }

              contradiction.
            }
            {
              (* specialize and apply IH *)
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H9.
              specialize (IHC ThetaA1 ThetaA2 tau
                            (ChorEnv.add B y tau0 G)
                            (Actor.Map.add A' DeltaA2 D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hv H9).
              rewrite -> (find_ab_neq2 A A' ThetaA3 T HCasesAeqA'R) in IHC.
              rewrite -> (find_ab_neq2 A A' DeltaA2 D HCasesAeqA'R) in IHC.
              simpl in Heq.
              pose proof (find_nbeq G A x B y tau0 Heq HninG) as HninG'.
              eapply (IHC HinT HninG' HninD).
            }

          + rewrite -> (find_ab_neq1 A' A x tau D) in H10; auto.

          + rewrite -> (find_ab_neq2 A' A ThetaA2 T) in H11; auto.
      }

    (* Case EPR *)
    + inversion HC. subst.
      pose proof (nin_nbeq D A x tau A' y H9) as HninAA'.
      pose proof (nin_nbeq D A x tau B z H10) as HninAB.
      rewrite -> (addadd5 D A' y Expr.QUBIT A x tau HninAA') in H8.
      rewrite -> (addadd5 (ChorEnv.add A' y Expr.QUBIT D) B z Expr.QUBIT A x tau HninAB) in H8.
      
      pose proof (nin_nbeq_add1 D A x A' y Expr.QUBIT HninAA' HninD) as HaddAA'.
      pose proof (nin_nbeq_add1 (ChorEnv.add A' y Expr.QUBIT D) A x B z
                    Expr.QUBIT HninAB HaddAA') as HaddAB.

      pose proof (nin_remove_ce G A x A' y HninG) as HninGy.
      pose proof (nin_remove_ce (ChorEnv.remove A' y G) A x B z HninGy) as HninGyz.

      (* specialize and apply IH *)
      specialize (IHC ThetaA1 ThetaA2 tau (ChorEnv.remove B z (ChorEnv.remove A' y G))
                    (ChorEnv.add B z Expr.QUBIT (ChorEnv.add A' y Expr.QUBIT D))
                    T A x v Hv H8 HinT HninGyz HaddAB).

      eapply EPR; auto.

      fold Choreography.subst.
      destruct (Insn.rebound_in A x (Insn.EPR A' y B z)) eqn:Heq.      
      {
        simpl in Heq.
        destruct (Insn.bind_eqb (A, x) (A', y)) eqn:H.
        {
          setoid_rewrite -> HninAA' in H.
          discriminate.
        }
        {
          simpl in Heq.
          setoid_rewrite -> HninAB in Heq.
          discriminate.
        }
      }

      auto.
      
      setoid_rewrite <- (Insn.bind_eqb_symmetric (A', y) (A, x)) in HninAA'.
      apply (nin_nbeq_add2 D A' y A x tau HninAA') in H9.
      auto.
      
      setoid_rewrite <- (Insn.bind_eqb_symmetric (B, z) (A, x)) in HninAB.
      apply (nin_nbeq_add2 D B z A x tau HninAB) in H10.
      auto.

    (* Case Let *)
    + inversion HC; subst.

      pose proof (nin_remove_ce G A x A' y HninG) as HninGy.   

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.

        assert (Var.Map.In x DeltaA1 \/ ~ Var.Map.In x DeltaA1) as HESL.
        tauto.

        destruct HESL as [HinDA | HninDA].
        (* Case x in e *) 
        {
          (* prepare witness for expression e typing and partioning facts. *)
          rewrite -> (add_find D A x tau) in H8.
          pose proof (inin (ChorEnv.find A D) DeltaA1 DeltaA2
                        x tau H8 HinDA) as Hinin.
          destruct (mapsto_destruct x tau DeltaA1 Hinin) as [DeltaA1' HDA'].
          destruct HDA' as [HDA'A HDA'B].
          rewrite -> HDA'A in H3.
          pose proof
            (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
               (Var.Map.concat ThetaA1 ThetaA0) x v tau0 Hv H3) as HWTS.
          pose proof (find_add A ThetaA2 T) as HFA.
          rewrite -> HFA in H9.
          (* partioning facts. *)
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          (* e typing witness. *)
          specialize (HWTS HPartitionA HninG HDA'B).

          (* prepare witness for choreography C typing *)
          rewrite -> (ChorEnv.addadd1 A D (Var.Map.add y tau0 DeltaA2) x tau) in H7. 
          rewrite -> (ChorEnv.addadd2 A T ThetaA3 ThetaA2) in H7.

          (* prepare hypotheses for partitioning requirements *)
          assert (Var.Map.Equal (Var.Map.add x tau DeltaA1') DeltaA1).
          { symmetry. auto. }
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau H H8 HninD HDA'B) as Hnin.
          pose proof (subst_not_in
                        C A x v
                        (ChorEnv.remove A y G)
                        (Actor.Map.add A  (Var.Map.add y tau0 DeltaA2) D)
                        (Actor.Map.add A ThetaA3 T)
                        H7) as HCSL.
          rewrite -> (find_add A (Var.Map.add y tau0 DeltaA2) D) in HCSL.
          destruct Hnin as [HninA HninB].

          (* prove main goal in subcases *)
          - eapply LetIn.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              { eauto. }
              { contradiction. }
              
            + fold Choreography.subst.
              destruct (Insn.rebound_in A x) eqn:Heq.
              {
                eauto.
              }
              {
                unfold Insn.rebound_in in Heq.
                specialize (HCSL
                              (nin_mapl DeltaA2 x y tau0 (nbeqeq A x y Heq) HninA)
                              (nin_remove_ce G A x A y HninG)).
                rewrite -> HCSL.
                eauto.
              }
              
            + auto.
              
            + auto.

            + auto.
        }
        (* case x not in e *)
        {
          pose proof (Expr.subst_not_in e x v
                        (ChorEnv.find A G) DeltaA1 ThetaA0 tau0
                        H3 HninG HninDA) as Hesubst.
          rewrite -> (add_find D A x tau) in H8.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H8 HninDA) as Hini.

          (* (de)construct environment for typing C *)
          pose proof (mapsto_destruct x tau DeltaA2 Hini) as HDA2.
          destruct HDA2 as [DeltaA2'].
          destruct H as [HDA2A HDA2B].

          (* partioning facts. *)
          rewrite -> (find_add A ThetaA2 T) in H9.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9) 
            as HPartition.                
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          
          (* prove main goal in subcases *)
          - eapply LetIn.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              {
                rewrite -> Hesubst.
                eauto.
              }
              { auto. }

            + fold Choreography.subst.
              destruct (Insn.rebound_in A x (Insn.Let A y e)) eqn:Heq.
              (* impossible case x = y *)
              {
                (* Note to ces: This case is provable constructively as follows, but instantiates
                   existential variables that falsify the hypotheses for subsequent case. *)
                (*
                  rewrite -> (ChorEnv.addadd1 A D (Var.Map.add y tau0 DeltaA2) x tau) in H7.
                  rewrite -> (ChorEnv.addadd2 A T ThetaA3 ThetaA2) in H7.
                  eauto.
                 *)
                pose proof (beqeq A x y Heq).
                pose proof (map_in DeltaA2 x tau Hini).
                rewrite <- H in H10.
                contradiction.
              }
              (* case x <> y *)
              {
                (* prepare C typing. *)
                rewrite -> (ChorEnv.addadd1 A D (Var.Map.add y tau0 DeltaA2) x tau) in H7.
                rewrite -> HDA2A in H7.
                rewrite -> (addadd6 x tau y tau0 DeltaA2') in H7.
                rewrite -> (ChorEnv.addadd2 A T ThetaA3 ThetaA2) in H7.
                
                               
                (* specialize and apply IH. *)
                specialize (IHC ThetaA1 ThetaA3 tau
                              (ChorEnv.remove A y G)
                              (Actor.Map.add A (Var.Map.add y tau0 DeltaA2') D)
                              (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T)
                              A x v Hv).
                
                unfold ChorEnv.add in IHC.
                rewrite -> (find_add A (Var.Map.add y tau0 DeltaA2') D) in IHC.
                rewrite -> (ChorEnv.addadd2 A D (Var.Map.add x tau (Var.Map.add y tau0 DeltaA2'))) in IHC.
                rewrite -> (ChorEnv.addadd2 A T ThetaA3 (Var.Map.concat ThetaA1 ThetaA3)) in IHC.
                specialize (IHC H7).

                unfold Insn.rebound_in in Heq.
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                specialize (IHC HPartitionB HninGy
                              (nin_mapl DeltaA2' x y tau0 (nbeqeq A x y Heq) HDA2B)).                

                eauto.

                apply (nbeqeq A x y Heq).
              }
              
            + pose proof (partition_remove (ChorEnv.find A D) DeltaA1 DeltaA2 x tau
                            H8 HninD HninDA).
              rewrite -> (remove_add x tau DeltaA2' DeltaA2 HDA2B HDA2A) in H.
              auto.

            + auto.

            + rewrite -> HDA2A in H10.
              pose proof (nin_mapr DeltaA2' y x tau (nin_nxeq DeltaA2' y x tau H10) H10).
              auto.
        }
      }
      (* Case A <> A' *)
      {
        - eapply LetIn.
          
          + destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. } 
            
          + fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.Let A' y e)) eqn:Heq.
            {
              unfold Insn.rebound_in in Heq.
              pose proof (beq A A' x y).
              destruct H.
              specialize (H Heq).
              destruct H.
              contradiction.
            }
            {
              (* prepare C typing *)
              rewrite -> (addadd3 D A x tau A' (Var.Map.add y tau0 DeltaA2) HCasesAeqA'R) in H7.
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H7.
              
              (* specialize and apply IH *)
              specialize (IHC ThetaA1 ThetaA2 tau (ChorEnv.remove A' y G)
                            (Actor.Map.add A' (Var.Map.add y tau0 DeltaA2) D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hv H7).
 
              rewrite -> (find_ab_neq2 A A' ThetaA3 T HCasesAeqA'R) in IHC.
              rewrite -> (find_ab_neq2 A A' (Var.Map.add y tau0 DeltaA2) D HCasesAeqA'R) in IHC.
              specialize (IHC HinT HninGy HninD).
              eauto.
            }

            + assert (A' <> A).
              auto.
              rewrite -> (find_ab_neq1 A' A x tau D H) in H8.
              auto.

            + assert (A' <> A).
              auto.
              rewrite -> (find_ab_neq2 A' A ThetaA2 T H) in H9.
              auto.

            + auto.
      }

    (* Case LetBang *)
    + inversion HC; subst.

      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.

        rewrite -> (ChorEnv.addadd1 A D DeltaA2 x tau) in H7.
        rewrite -> (ChorEnv.addadd2 A T ThetaA3 ThetaA2) in H7.
        
        assert (Var.Map.In x DeltaA1 \/ ~ Var.Map.In x DeltaA1) as HESL.
        tauto.

        (* Case x in e *) 
        destruct HESL as [HinDA | HninDA].   
        {          
          (* prepare witness for expression e typing and partioning facts. *)
          rewrite -> (add_find D A x tau) in H8.
          pose proof (inin (ChorEnv.find A D) DeltaA1 DeltaA2
                        x tau H8 HinDA) as Hinin.
          destruct (mapsto_destruct x tau DeltaA1 Hinin) as [DeltaA1' HDA'].
          destruct HDA' as [HDA'A HDA'B].
          rewrite -> HDA'A in H6.
          
          (* partioning facts. *)
          rewrite -> (find_add A ThetaA2 T) in H9.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          assert (H : Var.Map.Equal (Var.Map.add x tau DeltaA1') DeltaA1).
          { symmetry; auto. }
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau H H8 HninD HDA'B) as Hnin.
          destruct Hnin as [HninA HninB].
               
          eapply LetBang.
          
          + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
            {
            
              pose proof
                (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
                   (Var.Map.concat ThetaA1 ThetaA0) x v (Expr.BANG tau0)
                   Hv H6 HPartitionA HninG HDA'B) as HWTS.
              eauto.
            }
            {
              contradiction.
            }

          +  fold Choreography.subst.
             destruct (Insn.rebound_in A x) eqn:Heq.
             { eauto. }
             {
               pose proof (subst_not_in
                             C A x v
                             (ChorEnv.add A y tau0 G)
                             (Actor.Map.add A DeltaA2 D)
                             (Actor.Map.add A ThetaA3 T)
                             H7) as HCSL.
               rewrite -> (find_add A DeltaA2 D) in HCSL.
               specialize (HCSL HninA (find_nbeq G A x A y tau0 Heq HninG)).
               rewrite -> HCSL.
               eauto.
             }
             
          + auto.

          + auto.
        }
        (* case x not in e *)
        {
          pose proof (Expr.subst_not_in e x v 
                        (ChorEnv.find A G) DeltaA1 ThetaA0 (Expr.BANG tau0)
                        H6 HninG HninDA) as Hesubst.
          rewrite -> (add_find D A x tau) in H8.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H8 HninDA) as Hini.
          
          (* (de)construct environment for typing C *)
          pose proof (mapsto_destruct x tau DeltaA2 Hini) as HDA2.
          destruct HDA2 as [DeltaA2'].
          destruct H as [HDA2A HDA2B].
          
          (* partioning facts. *)
          rewrite -> (find_add A ThetaA2 T) in H9.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H9)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          
          (* prove main goal in subcases *)
          - eapply LetBang.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              {
                rewrite -> Hesubst.
                eauto.
              }
              { auto. }
              
            + fold Choreography.subst.
              (* impossible case due to env disjointness *)
              destruct (Insn.rebound_in A x (Insn.LetBang A y e)) eqn:Heq.
              {
                unfold Insn.rebound_in in Heq.
                pose proof (beqeq A x y Heq).
                rewrite <- H in *.

                pose proof (wt_disjoint C A (ChorEnv.add A x tau0 G) (Actor.Map.add A DeltaA2 D)
                              (Actor.Map.add A ThetaA3 T) H7) as Hwtdj.
                rewrite (find_add A DeltaA2 D) in Hwtdj.

                pose proof (nin_dj x (ChorEnv.find A (ChorEnv.add A x tau0 G)) DeltaA2
                              Hwtdj (map_in DeltaA2 x tau Hini)) as Hcontra1.
                pose proof (in_beq G A x tau0) as Hcontra2.
                contradiction.
              }
              {          
                rewrite -> HDA2A in H7.
                rewrite -> (addadd8 D A x tau DeltaA2') in H7.

                (* specialize and apply IH *)
                specialize (IHC ThetaA1 ThetaA3 tau
                              (ChorEnv.add A' y tau0 G)
                              (Actor.Map.add A DeltaA2' D)
                              (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T)
                              A x v
                              Hv).

                rewrite <- HCasesAeqA'L in IHC.
                rewrite -> (ChorEnv.addadd2 A T ThetaA3 (Var.Map.concat ThetaA1 ThetaA3)) in IHC.
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                rewrite -> (find_add A DeltaA2' D) in IHC.
                pose proof (nin_nbeq_add1 G A x A y tau0 Heq HninG) as HninGy.
                
                specialize (IHC H7 HPartitionB HninGy HDA2B).

                eauto.
              }

            +  assert (Var.Map.Equal (Var.Map.add x tau DeltaA2') DeltaA2) as Hdel.
               { symmetry. auto. }
               pose proof (@Var.Map.Properties.Partition_sym _
                             (Var.Map.add x tau (ChorEnv.find A D)) DeltaA1 DeltaA2 H8) as Hpart.
               pose proof (nin
                             (ChorEnv.find A D) DeltaA2' DeltaA2 DeltaA1
                             x tau Hdel Hpart HninD HDA2B) as Hnin.
               destruct Hnin as [HninA HninB].
               pose proof (@Var.Map.Properties.Partition_sym _
                             (ChorEnv.find A D) DeltaA2' DeltaA1 HninB).
               auto.

            + auto.
        }
      }
      (* Case A <> A' *)
      {
        - eapply LetBang.
          
          + destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. } 
            
          + fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.LetBang A' y e)) eqn:Heq.
            {
              unfold Insn.rebound_in in Heq.
              pose proof (beq A A' x y).
              destruct H.
              specialize (H Heq).
              destruct H.
              contradiction.
            }
            {
              (* prepare C typing *)
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H7.
              rewrite -> (addadd3 D A x tau A' DeltaA2 HCasesAeqA'R) in H7.

              (* specialize and apply IH *)
              specialize (IHC ThetaA1 ThetaA2 tau
                            (ChorEnv.add A' y tau0 G)
                            (Actor.Map.add A' DeltaA2 D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hv H7).
              rewrite -> (find_ab_neq2 A A' ThetaA3 T HCasesAeqA'R) in IHC.
              rewrite -> (find_ab_neq2 A A' DeltaA2 D HCasesAeqA'R) in IHC.
              simpl in Heq.
              pose proof (find_nbeq G A x A' y tau0 Heq HninG) as HninG'.
              eapply (IHC HinT HninG' HninD).
            }

            + assert (A' <> A).
              auto.
              rewrite -> (find_ab_neq1 A' A x tau D H) in H8.
              auto.

            + assert (A' <> A).
              auto.
              rewrite -> (find_ab_neq2 A' A ThetaA2 T H) in H9.
              auto.
      }
      
      (* Case LetPair *)
    + inversion HC; subst.

      pose proof (nin_remove_ce G A x A' z HninG) as HninGz.
      pose proof (nin_remove_ce (ChorEnv.remove A' z G) A x A' y HninGz) as HninGzy.
      
      assert (A = A' \/ A <> A') as HCasesAeqA'.
      tauto.

      destruct HCasesAeqA' as [HCasesAeqA'L | HCasesAeqA'R].

      (* Case A = A' *)
      {
        rewrite <- HCasesAeqA'L in *.

        rewrite -> (ChorEnv.addadd1 A D (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) x tau) in H5.
        rewrite -> (ChorEnv.addadd2 A T ThetaA3 ThetaA2) in H5.
        
        assert (Var.Map.In x DeltaA1 \/ ~ Var.Map.In x DeltaA1) as HESL.
        tauto.

        destruct HESL as [HinDA | HninDA].
        (* Case x in e *)
        {
          (* prepare witness for expression e typing and partioning facts. *)
          rewrite -> (add_find D A x tau) in H9.
          pose proof (inin (ChorEnv.find A D) DeltaA1 DeltaA2
                        x tau H9 HinDA) as Hinin.
          destruct (mapsto_destruct x tau DeltaA1 Hinin) as [DeltaA1' HDA'].
          destruct HDA' as [HDA'A HDA'B].
          rewrite -> HDA'A in H4.
          pose proof
            (Expr.wt_subst e ThetaA1 ThetaA0 tau (ChorEnv.find A G) DeltaA1'
               (Var.Map.concat ThetaA1 ThetaA0) x v (Expr.Tensor tau1 tau2) Hv H4) as HWTS.
          pose proof (find_add A ThetaA2 T) as HFA.
          rewrite -> HFA in H10.
          (* partioning facts. *)
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H10)
            as HPartition.
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          (* e typing witness. *)
          specialize (HWTS HPartitionA HninG HDA'B).

          (* prepare hypotheses for partitioning requirements *)
          assert (Var.Map.Equal (Var.Map.add x tau DeltaA1') DeltaA1).
          { symmetry. auto. }
          pose proof (nin (ChorEnv.find A D) DeltaA1' DeltaA1 DeltaA2 x tau H H9 HninD HDA'B) as Hnin.
          pose proof (subst_not_in
                        C A x v
                        (ChorEnv.remove A y (ChorEnv.remove A z G))
                        (Actor.Map.add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                        (Actor.Map.add A ThetaA3 T)
                        H5) as HCSL.
          rewrite -> (find_add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D) in HCSL.
          destruct Hnin as [HninA HninB].

          (* prove main goal in subcases *)
          - eapply LetPair.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              { eauto. }
              { contradiction. }
              
            + fold Choreography.subst.
              destruct (Insn.rebound_in A x) eqn:Heq.
              {
                eauto.
              }
              {
                unfold Insn.rebound_in in Heq.

                (* NOTE: nice boolean eq rewrite Lemma from Bool.Bool *)
                rewrite orb_false_iff in Heq.
                destruct Heq as [HeqA HeqB].
                
                pose proof (nin_mapl DeltaA2 x z tau2 (nbeqeq A x z HeqB) HninA) as Hninz.
                specialize (HCSL (nin_mapl (Var.Map.add z tau2 DeltaA2)
                                    x y tau1 (nbeqeq A x y HeqA) Hninz) HninGzy).

                rewrite -> HCSL.
                eauto.
              }
              
            + auto.
              
            + auto.

            + auto.

            + auto.

            + auto.
        }
        (* case x not in e *)
        {
          pose proof (Expr.subst_not_in e x v
                        (ChorEnv.find A G) DeltaA1 ThetaA0 (Expr.Tensor tau1 tau2)
                        H4 HninG HninDA) as Hesubst.
          rewrite -> (add_find D A x tau) in H9.
          pose proof (ini (ChorEnv.find A D) DeltaA1 DeltaA2 x tau H9 HninDA) as Hini.

          (* (de)construct environment for typing C *)
          pose proof (mapsto_destruct x tau DeltaA2 Hini) as HDA2.
          destruct HDA2 as [DeltaA2'].
          destruct H as [HDA2A HDA2B].

          (* partioning facts. *)
          rewrite -> (find_add A ThetaA2 T) in H10.
          pose proof
            (partitioning (ChorEnv.find A T) ThetaA0 ThetaA1 ThetaA2 ThetaA3 HinT H10) 
            as HPartition.                
          destruct HPartition as [HPartitionA [HPartitionB [HPartitionC HPartitionD]]].
          
          (* prove main goal in subcases *)
          - eapply LetPair.
            
            + destruct (Actor.FSet.MF.eq_dec A A) eqn:Heq.
              {
                rewrite -> Hesubst.
                eauto.
              }
              { auto. }

            + fold Choreography.subst.
              destruct (Insn.rebound_in A x (Insn.LetPair A y z e)) eqn:Heq.
              (* impossible case x = y *)
              {
                unfold Insn.rebound_in in Heq.

                (* NOTE: nice boolean eq rewrite Lemma from Bool.Bool *)
                rewrite orb_true_iff in Heq.
                destruct Heq as [HeqA | HeqB].
                {
                  pose proof (beqeq A x y HeqA).
                  rewrite <- H in *.
                  pose proof (map_in DeltaA2 x tau Hini).
                  contradiction.
                }
                {
                  pose proof (beqeq A x z HeqB).
                  pose proof (map_in DeltaA2 x tau Hini).
                  rewrite <- H in H12.
                  contradiction.
                }
              }
              (* case x <> y,z *)
              {
                unfold Insn.rebound_in in Heq.
                rewrite orb_false_iff in Heq.
                destruct Heq as [HeqA HeqB].
                pose proof (nbeqeq A x y HeqA).
                pose proof (nbeqeq A x z HeqB).
                
                (* prepare C typing. *)
                rewrite -> HDA2A in H5.                
                rewrite -> (addadd6 x tau z tau2 DeltaA2' H0) in H5.
                rewrite -> (addadd6 x tau y tau1 (Var.Map.add z tau2 DeltaA2') H) in H5.
                rewrite -> (addadd8 D A x tau (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2'))) in H5.

                specialize (IHC ThetaA1 ThetaA3 tau
                              (ChorEnv.remove A y (ChorEnv.remove A z G))
                              (Actor.Map.add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2')) D)
                              (Actor.Map.add A (Var.Map.concat ThetaA1 ThetaA3) T)
                              A x v Hv).

                rewrite -> (ChorEnv.addadd2 A T ThetaA3 (Var.Map.concat ThetaA1 ThetaA3)) in IHC.
                rewrite -> (find_add A (Var.Map.concat ThetaA1 ThetaA3) T) in IHC.
                rewrite -> (find_add A (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2')) D) in IHC.

               
                pose proof (nin_mapl DeltaA2' x z tau2 H0 HDA2B) as Hninz.
                pose proof (nin_mapl (Var.Map.add z tau2 DeltaA2') x y tau1 H Hninz) as Hniny.
                
                specialize (IHC H5 HPartitionB HninGzy Hniny).
                eauto.
              }

            + pose proof (partition_remove (ChorEnv.find A D) DeltaA1 DeltaA2 x tau
                            H9 HninD HninDA).
              rewrite -> (remove_add x tau DeltaA2' DeltaA2 HDA2B HDA2A) in H.
              auto.

            + auto.

            + rewrite -> HDA2A in H11.
              pose proof (nin_mapr DeltaA2' y x tau (nin_nxeq DeltaA2' y x tau H11) H11).
              auto.

            + rewrite -> HDA2A in H12.
              pose proof (nin_mapr DeltaA2' z x tau (nin_nxeq DeltaA2' z x tau H12) H12).
              auto.

            + auto.
        }
      }
      (* Case A <> A' *)
      {
        - eapply LetPair.

          + destruct (Actor.FSet.MF.eq_dec A A') eqn:Heq.
            { contradiction. }
            { eauto. } 

          + fold Choreography.subst.
            destruct (Insn.rebound_in A x (Insn.LetPair A' y z e)) eqn:Heq.
            {
              unfold Insn.rebound_in in Heq.
              rewrite orb_true_iff in Heq.
              destruct Heq as [Heqxy | Heqxz].
              {
                pose proof (beq A A' x y).
                destruct H as [HA HB].
                specialize (HA Heqxy).
                destruct HA.
                contradiction.
              }
              {
                pose proof (beq A A' x z).
                destruct H as [HA HB].
                specialize (HA Heqxz).
                destruct HA.
                contradiction.
              }
            }
            { 
              (* prepare C typing *)
              rewrite -> (addadd3 D A x tau A'
                            (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) HCasesAeqA'R) in H5.
              rewrite -> (addadd4 T A ThetaA2 A' ThetaA3 HCasesAeqA'R) in H5.
              
              (* specialize and apply IH *)
              specialize (IHC ThetaA1 ThetaA2 tau (ChorEnv.remove A' y (ChorEnv.remove A' z G))
                            (Actor.Map.add A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2)) D)
                            (Actor.Map.add A' ThetaA3 T)
                            A x v Hv H5).
 
              rewrite -> (find_ab_neq2 A A' ThetaA3 T HCasesAeqA'R) in IHC.
              rewrite -> (find_ab_neq2 A A' (Var.Map.add y tau1 (Var.Map.add z tau2 DeltaA2))
                            D HCasesAeqA'R) in IHC.

              specialize (IHC HinT HninGzy HninD).
              eauto.
            }

          + assert (A' <> A).
            auto.
            rewrite -> (find_ab_neq1 A' A x tau D H) in H9.
            auto.
            
          + assert (A' <> A).
            auto.
            rewrite -> (find_ab_neq2 A' A ThetaA2 T H) in H10.
            auto.
            
          + auto.

          + auto.

          + auto.
      }
Qed.