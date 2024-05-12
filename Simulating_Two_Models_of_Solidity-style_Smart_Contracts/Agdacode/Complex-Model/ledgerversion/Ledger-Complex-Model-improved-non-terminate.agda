open import constantparameters

module Complex-Model.ledgerversion.Ledger-Complex-Model-improved-non-terminate (param : ConstantParameters) where

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



{-# NON_TERMINATING #-}
evaluateNonTerminatingAuxfinal0 : Ledger → StateExecFun → (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingAuxfinal0 oldLedger (stateEF currentLedger [] initialAddr lastCallAddr calledAddr (return cost ms)
                            gasLeft  funNameevalState msgevalState)
                            = evaluateAuxfinal0' param oldLedger currentLedger
                                initialAddr lastCallAddr calledAddr cost ms gasLeft funNameevalState msgevalState (compareLeq cost gasLeft)

evaluateNonTerminatingAuxfinal0 oldLedger (stateEF currentLedger s initialAddr lastCallAddr calledAddr (error msgg debugInfo)
                             gasLeft  funNameevalState msgevalState)
                          = addWeiToLedger param oldLedger initialAddr (GastoWei param gasLeft) ,,
                            (err msgg ⟨  lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩ , gasLeft gas)
evaluateNonTerminatingAuxfinal0 oldLedger evals
                          = evaluateNonTerminatingAuxfinal0 oldLedger (stepEFwithGasError param oldLedger evals)


evaluateNonTerminatingAuxfinal : (ledger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → FunctionName
                          → Msg
                          → (gasreserved : ℕ)

                          → (cp  : OrderingLeq (GastoWei param gasreserved) (ledger initialAddr .amount))
                          → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingAuxfinal ledger initialAddr lastCallAddr calledAddr funname msg gasreserved  (leq leqpr)
                           = let
                               ledgerDeducted : Ledger
                               ledgerDeducted = deductGasFromLedger param ledger initialAddr (GastoWei param gasreserved) leqpr
                             in just (evaluateNonTerminatingAuxfinal0 ledgerDeducted
                                     (stateEF ledgerDeducted [] initialAddr lastCallAddr calledAddr (ledgerDeducted calledAddr .fun funname msg)
                                     gasreserved  funname msg))

evaluateNonTerminatingAuxfinal ledger initialAddr lastCallAddr calledAddr funname msg gasreserved  (greater greaterpr)
                           = nothing


evaluateNonTerminatingfinal : (ledger : Ledger)
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

                         → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingfinal ledger initialAddr lastCallAddr calledAddr funname msg gasreserved
                      =  evaluateNonTerminatingAuxfinal ledger initialAddr lastCallAddr calledAddr funname msg gasreserved
                         (compareLeq (GastoWei param gasreserved) (ledger initialAddr .amount))




