{-# OPTIONS --no-sized-types --safe #-}
open import constantparameters

module Complex-Model.terminating.ledger.Ledger-Complex-Model-improved-terminate (param : ConstantParameters) where

open import Data.Nat
open import Agda.Builtin.Nat using (_-_; _*_)
open import Data.Unit
open import Data.List
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe  hiding (_>>=_)
open import Data.String hiding (length; show) renaming (_++_ to _++str_)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Show
open import Data.Empty


-- our work
open import Complex-Model.ccomand.ccommands-cresponse
open import basicDataStructure
open import libraries.natCompare
open import libraries.Mainlibrary
open import Complex-Model.ledgerversion.Ledger-Complex-Model


mutual

  evaluateTerminatingAuxStep2 : Ledger
                                    → (stateEF : StateExecFun)
                                    → (numberOfSteps : ℕ)
                                    → stepEFgasAvailable param stateEF ≦r numberOfSteps
                                    → Ledger × MsgOrErrorWithGas
  evaluateTerminatingAuxStep2 oldLedger (stateEF currentLedger [] initialAddr lastCallAddr calledAddr (return cost ms)
                              gasLeft  funNameevalState msgevalState)
                              numberOfSteps numberOfStepsLessGas
                              = evaluateAuxfinal0' param oldLedger currentLedger
                                  initialAddr lastCallAddr calledAddr cost ms gasLeft funNameevalState msgevalState (compareLeq cost gasLeft)

  evaluateTerminatingAuxStep2 oldLedger (stateEF currentLedger s initialAddr lastCallAddr calledAddr (error msgg debugInfo)
                               gasLeft  funNameevalState msgevalState)
                               numberOfSteps numberOfStepsLessGas
                            = addWeiToLedger param oldLedger initialAddr (GastoWei param gasLeft) ,,
                              (err msgg ⟨  lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩ , gasLeft gas)
  evaluateTerminatingAuxStep2 oldLedger evals (suc numberOfSteps) numberOfStepsLessGas
                             = evaluateTerminatingAuxStep3 oldLedger evals numberOfSteps numberOfStepsLessGas
                               (compareLeq (stepEFgasNeeded param evals) (stepEFgasAvailable param evals))

  evaluateTerminatingAuxStep2 oldLedger
                               (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr nextstep gasLeft funNameevalState msgevalState) 0 numberOfStepsLessGas
                               = oldLedger ,,  (err outOfGasError ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩ , 0 gas)

                          --

  evaluateTerminatingAuxStep3 : Ledger
                                    → (stateEF : StateExecFun)
                                    → (numberOfSteps : ℕ)
                                    → stepEFgasAvailable param stateEF ≦r suc numberOfSteps
                                    → OrderingLeq (stepEFgasNeeded param stateEF) (stepEFgasAvailable param stateEF)
                                    → Ledger × MsgOrErrorWithGas
  evaluateTerminatingAuxStep3 oldLedger state numberOfSteps numberOfStepsLessgas (leq x)
               = evaluateTerminatingAuxStep2 oldLedger
                 (deductGas param (stepEF param oldLedger state) (suc (stepEFgasNeeded param state))) numberOfSteps
                 (lemmaxSucY (gasLeft (stepEF param oldLedger state)) numberOfSteps (stepEFgasNeeded param state)
                   (lemma=≦r (gasLeft (stepEF param oldLedger state)) (gasLeft state) (suc numberOfSteps)
                             (lemmaStepEFpreserveGas2 param oldLedger state) numberOfStepsLessgas))


  evaluateTerminatingAuxStep3 oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr nextstep gasLeft₁ funNameevalState msgevalState)
                                  numberOfSteps numberOfStepsLessgas (greater x)
                                  = oldLedger ,,  (err outOfGasError ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩ , 0 gas)



evaluateTerminatingAuxStep1 : (ledger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → FunctionName
                          → Msg
                          → (gasreserved : ℕ)
                          → (cp  : OrderingLeq (GastoWei param gasreserved) (ledger initialAddr .amount))
                          → Ledger × MsgOrErrorWithGas
evaluateTerminatingAuxStep1 ledger initialAddr lastCallAddr calledAddr funname msg gasreserved  (leq leqpr)
                           = let
                               ledgerDeducted : Ledger
                               ledgerDeducted = deductGasFromLedger param ledger initialAddr (GastoWei param gasreserved) leqpr
                             in evaluateTerminatingAuxStep2 ledgerDeducted
                                     (stateEF ledgerDeducted [] initialAddr lastCallAddr calledAddr (ledgerDeducted calledAddr .fun funname msg)
                                     gasreserved  funname msg) gasreserved (refl≦r gasreserved)

evaluateTerminatingAuxStep1 ledger initialAddr lastCallAddr calledAddr funname msg gasreserved  (greater greaterpr)
                           = ledger ,,  (err outOfGasError ⟨ lastCallAddr >> initialAddr ∙ funname [ msg ]⟩ , 0 gas)

evaluateTerminatingfinal : (ledger : Ledger)
                         → (initialAddr : Address)
                            -- Initial address is the address from which the very first call was made
                         → (lastCallAddr : Address)
                            -- lastCallAddr is the address from which the current call of a function in
                            --         calledAddr is made
                         → (calledAddr : Address)
                            -- calledAddr is the address where a function call is currently executed
                            --            it was called from calledAddr
                         → FunctionName
                         → Msg
                         → (gasreserved : ℕ)
                         → Ledger × MsgOrErrorWithGas
evaluateTerminatingfinal ledger initialAddr lastCallAddr calledAddr funname msg gasreserved
                      =  evaluateTerminatingAuxStep1 ledger initialAddr lastCallAddr calledAddr funname msg gasreserved
                         (compareLeq (GastoWei param gasreserved) (ledger initialAddr .amount))

