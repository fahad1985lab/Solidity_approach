
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
open import libraries.Mainlibrary-new-version
open import Complex-Model.ledgerversion.Ledger-Complex-Model-with-reentrancy-attack






{-# NON_TERMINATING #-}
evaluateNonTerminatingStep2 : Ledger → StateExecFun → (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingStep2 oldLedger (stateEF currentLedger [] initialAddr lastCallAddr calledAddr (return msg) gasLeft funNameevalState msgevalState amountReceived listEvent)
                            =
                                evaluateAuxfinalStep3 param oldLedger currentLedger initialAddr lastCallAddr calledAddr (param .costofreturn)
                                msg gasLeft funNameevalState msgevalState amountReceived 
                                listEvent (compareLeq (param .costofreturn) gasLeft)
evaluateNonTerminatingStep2 oldLedger (stateEF currentLedger s initialAddr lastCallAddr calledAddr (error msgg debugInfo)
                             gasLeft  funNameevalState msgevalState amountReceived listEvent)
                          = addWeiToLedger param oldLedger initialAddr (GastoWei param gasLeft) ,,
                            ((err msgg ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]∙ listEvent ⟩) , gasLeft gas, listEvent)
                            
evaluateNonTerminatingStep2 oldLedger evals = evaluateNonTerminatingStep2 oldLedger (stepEFwithGasError param oldLedger evals)



evaluateNonTerminatingStep1 : (ledger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → (gasreserved : ℕ)
                          → FunctionName
                          → Msg                          
                          → (amountReceived : Amount)
                          → (listEvent : List String)
                          → (cp  : OrderingLeq (GastoWei param gasreserved) (ledger initialAddr .amount))
                          → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingStep1 ledger initialAddr lastCallAddr calledAddr gasreserved funname msg  amountReceived listEvent (leq leqpr)
                           = let
                               ledgerDeducted : Ledger
                               ledgerDeducted = deductGasFromLedger param ledger initialAddr (GastoWei param gasreserved) leqpr
                             in just (evaluateNonTerminatingStep2 ledgerDeducted

   (stateEF ledgerDeducted [] initialAddr initialAddr  lastCallAddr (exec (callc calledAddr funname msg  amountReceived) (λ _ → 1) return) 
                               gasreserved  funname msg  amountReceived listEvent))

evaluateNonTerminatingStep1 ledger initialAddr lastCallAddr calledAddr gasreserved funname msg  amountReceived listEvent (greater greaterpr)
                           = nothing


evaluateNonTerminatingfinalstep : (ledger : Ledger)
                         → (initialAddr : Address)
                            -- Initial address is the address from which the very first call was made
                         → (lastCallAddr : Address)
                            -- lastCallAddr is the address from which the current call of a function in
                            --         calledAddr is made
                         → (calledAddr : Address)
                            -- calledAddr is the address where a function call is currently executed
                            --            it was called from calledAddr
                         → (gasreserved : ℕ)
                         → FunctionName
                         → Msg
                         → (amountReceived : Amount)
                         → (listEvent : List String)
                         → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingfinalstep ledger initialAddr lastCallAddr calledAddr gasreserved funname msg  amountReceived listEvent
                      =  evaluateNonTerminatingStep1 ledger initialAddr lastCallAddr calledAddr gasreserved funname msg {-(nat 100)-}  amountReceived listEvent
                         (compareLeq (GastoWei param gasreserved) (ledger initialAddr .amount))

















































































 ---##################################################################################
{- before add listevent to MsgOrErrorWithGas



{-# NON_TERMINATING #-}
evaluateNonTerminatingStep2 : Ledger → StateExecFun → (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingStep2 oldLedger (stateEF currentLedger [] initialAddr lastCallAddr calledAddr (return msg) gasLeft funNameevalState msgevalState amountReceived listEvent)   =
                                evaluateAuxfinalStep3 param oldLedger currentLedger initialAddr lastCallAddr calledAddr (param .costofreturn)
                                msg {- if i chang it to (nat 100) it works, but with msg does not work-}
                                gasLeft funNameevalState msgevalState amountReceived listEvent (compareLeq (param .costofreturn) gasLeft)
evaluateNonTerminatingStep2 oldLedger (stateEF currentLedger s initialAddr lastCallAddr calledAddr (error msgg debugInfo)
                             gasLeft  funNameevalState msgevalState amountReceived listEvent)
                          = addWeiToLedger param oldLedger initialAddr (GastoWei param gasLeft) ,,
                            ((err msgg
                            --⟨  lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩
                            ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]∙ listEvent ⟩) , gasLeft gas)
                            
evaluateNonTerminatingStep2 oldLedger evals = evaluateNonTerminatingStep2 oldLedger (stepEFwithGasError param oldLedger evals)

{- old

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



-}


evaluateNonTerminatingStep1 : (ledger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → (gasreserved : ℕ)
                          → FunctionName
                          → Msg                          
                          → (amountReceived : Amount)
                          → (listEvent : List String)
                          → (cp  : OrderingLeq (GastoWei param gasreserved) (ledger initialAddr .amount))
                          → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingStep1 ledger initialAddr lastCallAddr calledAddr gasreserved funname msg  amountReceived listEvent (leq leqpr)
                           = let
                               ledgerDeducted : Ledger
                               ledgerDeducted = deductGasFromLedger param ledger initialAddr (GastoWei param gasreserved) leqpr
                             in just (evaluateNonTerminatingStep2 ledgerDeducted

   (stateEF ledgerDeducted [] initialAddr initialAddr  lastCallAddr (exec (callc calledAddr funname msg  amountReceived) (λ _ → 1) return) 
                               gasreserved  funname msg  amountReceived listEvent))

evaluateNonTerminatingStep1 ledger initialAddr lastCallAddr calledAddr gasreserved funname msg  amountReceived listEvent (greater greaterpr)
                           = nothing
{-
{- old version
                               (ledgerDeducted calledAddr .fun funname msg)
                               notes : execute the body of the function old solution and did not execute the transfer
                             the new solution it will execute the function even transfer and when finish it will return -}
                             -- old version
-- (stateEF ledgerDeducted [] initialAddr lastCallAddr calledAddr (exec (callc calledAddr funname msg amountReceived) (λ _ → 1) return)
-}

evaluateNonTerminatingfinalstep : (ledger : Ledger)
                         → (initialAddr : Address)
                            -- Initial address is the address from which the very first call was made
                         → (lastCallAddr : Address)
                            -- lastCallAddr is the address from which the current call of a function in
                            --         calledAddr is made
                         → (calledAddr : Address)
                            -- calledAddr is the address where a function call is currently executed
                            --            it was called from calledAddr
                         → (gasreserved : ℕ)
                         → FunctionName
                         → Msg
                         → (amountReceived : Amount)
                         → (listEvent : List String)
                         → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingfinalstep ledger initialAddr lastCallAddr calledAddr gasreserved funname msg  amountReceived listEvent
                      =  evaluateNonTerminatingStep1 ledger initialAddr lastCallAddr calledAddr gasreserved funname msg {-(nat 100)-}  amountReceived listEvent
                         (compareLeq (GastoWei param gasreserved) (ledger initialAddr .amount))





-}






{- old version

change order

from
             → (amountReceived : Amount)
             → (gasreserved : ℕ)

to
             → (gasreserved : ℕ)
             → (amountReceived : Amount)

evaluateNonTerminatingAuxfinal : (ledger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → FunctionName
                          → Msg
                          → (amountReceived : Amount)
                          → (gasreserved : ℕ)
                          → (cp  : OrderingLeq (GastoWei param gasreserved) (ledger initialAddr .amount))
                          → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingAuxfinal ledger initialAddr lastCallAddr calledAddr funname msg amountReceived gasreserved  (leq leqpr)
                           = let
                               ledgerDeducted : Ledger
                               ledgerDeducted = deductGasFromLedger param ledger initialAddr (GastoWei param gasreserved) leqpr
                             in just (evaluateNonTerminatingAuxfinal0 ledgerDeducted
                                     (stateEF ledgerDeducted [] initialAddr lastCallAddr calledAddr (ledgerDeducted calledAddr .fun funname msg)
                                     gasreserved  funname msg amountReceived))

evaluateNonTerminatingAuxfinal ledger initialAddr lastCallAddr calledAddr funname msg amountReceived gasreserved  (greater greaterpr)
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
                         → (amountReceived : Amount)
                         → (gasreserved : ℕ)
                         → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingfinal ledger initialAddr lastCallAddr calledAddr funname msg amountReceived gasreserved
                      =  evaluateNonTerminatingAuxfinal ledger initialAddr lastCallAddr calledAddr funname msg amountReceived gasreserved
                         (compareLeq (GastoWei param gasreserved) (ledger initialAddr .amount))










-}


----#######

{- old version on 29.11.2023

evaluateAuxfinalStep3 : (oldLedger : Ledger)
                          → (currentLedger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → (cost : ℕ)
                          → (returnvalue : Msg)
                          → (gasLeft : ℕ)
                          → (funNameevalState : FunctionName)
                          → (msgevalState : Msg)
                          → (amountReceived : Amount)
                          → (cp  : OrderingLeq cost gasLeft)
                          → (Ledger × MsgOrErrorWithGas)
evaluateAuxfinalStep3 oldLedger currentLedger initialAddr lastCallAddr calledAddr cost ms gasLeft funNameevalState msgevalState amountReceived (leq x)
                               =  (addWeiToLedger param currentLedger initialAddr
                                   (GastoWei param (gasLeft - cost))) ,, ((theMsg ms) , ((gasLeft - cost)) gas)
                                 -- test this function by replacing ms to (nat 100) and it works
evaluateAuxfinalStep3 oldLedger currentLedger initialAddr lastCallAddr calledAddr cost returnvalue gasLeft funNameevalState msgevalState amountReceived (greater x)
                               = oldLedger ,, (((err (strErr " Out Of Gass ") ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩) , gasLeft gas))




{-# NON_TERMINATING #-}
evaluateNonTerminatingStep2 : Ledger → StateExecFun → (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingStep2 oldLedger (stateEF currentLedger [] initialAddr lastCallAddr calledAddr (return msg) gasLeft funNameevalState msgevalState amountReceived)   =
                                evaluateAuxfinalStep3 {-param-} oldLedger currentLedger initialAddr lastCallAddr calledAddr (param .costofreturn)
                                msg {- if i chang it to (nat 100) it works, but with msg does not work-}
                                gasLeft funNameevalState msgevalState amountReceived (compareLeq (param .costofreturn) gasLeft)
evaluateNonTerminatingStep2 oldLedger (stateEF currentLedger s initialAddr lastCallAddr calledAddr (error msgg debugInfo)
                             gasLeft  funNameevalState msgevalState amountReceived)
                          = addWeiToLedger param oldLedger initialAddr (GastoWei param gasLeft) ,,
                            ((err msgg ⟨  lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩) , gasLeft gas)
                            
evaluateNonTerminatingStep2 oldLedger evals = evaluateNonTerminatingStep2 oldLedger (stepEFwithGasError param oldLedger evals)


evaluateNonTerminatingStep1 : (ledger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → FunctionName
                          → Msg
                          → (gasreserved : ℕ)
                          → (amountReceived : Amount)
                          → (cp  : OrderingLeq (GastoWei param gasreserved) (ledger initialAddr .amount))
                          → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingStep1 ledger initialAddr lastCallAddr calledAddr funname msg gasreserved amountReceived (leq leqpr)
                           = let
                               ledgerDeducted : Ledger
                               ledgerDeducted = deductGasFromLedger param ledger initialAddr (GastoWei param gasreserved) leqpr
                             in just (evaluateNonTerminatingStep2 ledgerDeducted

   (stateEF ledgerDeducted [] initialAddr initialAddr  lastCallAddr (exec (callc calledAddr funname msg  amountReceived) (λ _ → 1) return) 
                               gasreserved  funname msg  amountReceived))

evaluateNonTerminatingStep1 ledger initialAddr lastCallAddr calledAddr funname msg gasreserved amountReceived (greater greaterpr)
                           = nothing


evaluateNonTerminatingfinalstep : (ledger : Ledger)
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
                         → (amountReceived : Amount)
                         → Maybe (Ledger × MsgOrErrorWithGas)
evaluateNonTerminatingfinalstep ledger initialAddr lastCallAddr calledAddr funname msg gasreserved amountReceived
                      =  evaluateNonTerminatingStep1 ledger initialAddr lastCallAddr calledAddr funname msg {-(nat 100)-} gasreserved amountReceived
                         (compareLeq (GastoWei param gasreserved) (ledger initialAddr .amount))


-}
