open import constantparameters

module Complex-Model.ledgerversion.Ledger-Complex-Model-improved-terminate (param : ConstantParameters) where

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
open import libraries.Mainlibrary-new-version
open import Complex-Model.ledgerversion.Ledger-Complex-Model-with-reentrancy-attack


{-   TERMINATING VERSION OF THE ABOVE
     in evaluateTerminatingAuxfinal0
     we have additional parameter numberOfSteps : ℕ
     which is initialised with gasLeft
     and we add a proof that   numberOfSteps <= gasLeft
     in addition we make sure that gas is in each step reduced by 1 more than what is specified
     that shows that numberOfSteps <= gasLeft is an invariant

-}

mutual

  evaluateTerminatingAuxfinal0 : Ledger
                                    → (stateEF : StateExecFun)
                                    → (numberOfSteps : ℕ)
                                    → stepEFgasAvailable param stateEF ≦r numberOfSteps
                                    → Ledger × MsgOrErrorWithGas
  evaluateTerminatingAuxfinal0 oldLedger (stateEF currentLedger [] initialAddr lastCallAddr calledAddr (return ms)
                              gasLeft  funNameevalState msgevalState amountReceived listEvent)
                              numberOfSteps numberOfStepsLessGas
                              = evaluateAuxfinalStep3 param oldLedger currentLedger
                                  initialAddr lastCallAddr calledAddr (param .costofreturn) ms gasLeft funNameevalState msgevalState amountReceived listEvent
                                  (compareLeq (param .costofreturn) gasLeft)

  evaluateTerminatingAuxfinal0 oldLedger (stateEF currentLedger s initialAddr lastCallAddr calledAddr (error msgg debugInfo)
                               gasLeft  funNameevalState msgevalState amountReceived listEvent)
                               numberOfSteps numberOfStepsLessGas
                            = addWeiToLedger param oldLedger initialAddr (GastoWei param gasLeft) ,, 
                              (err msgg ⟨  lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]∙ listEvent ⟩ , gasLeft gas, listEvent)

  evaluateTerminatingAuxfinal0 oldLedger evals (suc numberOfSteps) numberOfStepsLessGas
                             = evaluateTerminatingAuxfinal0aux oldLedger evals numberOfSteps numberOfStepsLessGas
                               (compareLeq (stepEFgasNeeded param evals) (stepEFgasAvailable param evals))

  evaluateTerminatingAuxfinal0 oldLedger
                               (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr nextstep gasLeft funNameevalState msgevalState amountReceived listEvent)
                               0 numberOfStepsLessGas
                               = oldLedger ,,  (err outOfGasError ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]∙ listEvent ⟩ , 0 gas, listEvent)

                          

  evaluateTerminatingAuxfinal0aux : Ledger
                                    → (evals : StateExecFun)
                                    → (numberOfSteps : ℕ)
                                    → stepEFgasAvailable param evals ≦r suc numberOfSteps
                                    → OrderingLeq (stepEFgasNeeded param evals) (stepEFgasAvailable param evals)
                                    → Ledger × MsgOrErrorWithGas
  evaluateTerminatingAuxfinal0aux oldLedger state numberOfSteps numberOfStepsLessgas (leq x)
               = evaluateTerminatingAuxfinal0 oldLedger
                 (deductGas param (stepEF param oldLedger state) (suc (stepEFgasNeeded param state))) numberOfSteps
                 (lemmaxSucY (gasLeft (stepEF param oldLedger state)) numberOfSteps (stepEFgasNeeded param state)
                   (lemma=≦r (gasLeft (stepEF param oldLedger state)) (gasLeft state) (suc numberOfSteps)
                             (lemmaStepEFpreserveGas2 param oldLedger state) numberOfStepsLessgas))

  evaluateTerminatingAuxfinal0aux oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr nextstep gasLeft₁ funNameevalState msgevalState amountReceived listEvent)
                                  numberOfSteps numberOfStepsLessgas (greater x)
                  = oldLedger ,,  (err outOfGasError ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]∙ listEvent ⟩ , 0 gas, listEvent)



evaluateTerminatingAuxfinal : (ledger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → FunctionName
                          → Msg
                          → (amountReceived : Amount)
                          → (listEvent : List String)
                          → (gasreserved : ℕ)
                          → (cp  : OrderingLeq (GastoWei param gasreserved) (ledger initialAddr .amount))
                          → Ledger × MsgOrErrorWithGas
evaluateTerminatingAuxfinal ledger initialAddr lastCallAddr calledAddr funname msg amountReceived listEvent gasreserved  (leq leqpr)
                           = let
                               ledgerDeducted : Ledger
                               ledgerDeducted = deductGasFromLedger param ledger initialAddr (GastoWei param gasreserved) leqpr
                             in evaluateTerminatingAuxfinal0 ledgerDeducted
                                     (stateEF ledgerDeducted [] initialAddr initialAddr  lastCallAddr
                                     (exec (callc calledAddr funname msg  amountReceived) (λ _ → 1) return)
                                     gasreserved  funname msg amountReceived listEvent) gasreserved (refl≦r gasreserved)

evaluateTerminatingAuxfinal ledger initialAddr lastCallAddr calledAddr funname msg amountReceived listEvent gasreserved  (greater greaterpr)
                           = ledger ,,  (err outOfGasError ⟨ lastCallAddr >> initialAddr ∙ funname [ msg ]∙ listEvent ⟩ , 0 gas, listEvent)

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
                         → (amountReceived : Amount)
                         → (listEvent : List String)
                         → (gasreserved : ℕ)
                         → Ledger × MsgOrErrorWithGas
evaluateTerminatingfinal ledger initialAddr lastCallAddr calledAddr funname msg amountReceived listEvent gasreserved
                      =  evaluateTerminatingAuxfinal ledger initialAddr lastCallAddr calledAddr funname msg amountReceived listEvent gasreserved
                         (compareLeq (GastoWei param gasreserved) (ledger initialAddr .amount))

