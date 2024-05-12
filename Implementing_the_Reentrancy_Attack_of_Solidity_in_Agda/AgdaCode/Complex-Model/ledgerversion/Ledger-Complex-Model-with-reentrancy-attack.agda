

open import constantparameters

module Complex-Model.ledgerversion.Ledger-Complex-Model-with-reentrancy-attack (param : ConstantParameters) where

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


-- update view function in the ledger
updateLedgerpurefun : Ledger → Address → FunctionName
       → ((Msg → MsgOrError) → (Msg → MsgOrError))
       → ((Msg → MsgOrError) → (Msg → ℕ) → Msg → ℕ)
       → Ledger
updateLedgerpurefun ledger changedAddr changedFname f g a .amount = ledger a .amount
updateLedgerpurefun ledger changedAddr changedFname f g a .fun  = ledger a .fun
updateLedgerpurefun ledger changedAddr changedFname f g a .viewFunction fname =
       if (changedFname ≡fun fname) then  f (ledger a .viewFunction fname)
                         else  ledger a .viewFunction fname
updateLedgerpurefun ledger changedAddr changedFname f g a .viewFunctionCost fname =
          if (changedFname ≡fun fname) then  g (ledger a .viewFunction fname) (ledger a .viewFunctionCost fname)
                         else  ledger a .viewFunctionCost fname




--update ledger amount
updateLedgerAmount : (ledger : Ledger)
               →  (calledAddr destinationAddr : Address) (amount' : Amount)
               → (correctAmount : amount' ≦r  ledger calledAddr .amount)
                → Ledger
updateLedgerAmount ledger calledAddr destinationAddr amount' correctAmount addr .amount
     = if addr ≡ᵇ calledAddr
     then subtract (ledger calledAddr .amount) amount' correctAmount
     else (if addr ≡ᵇ destinationAddr
     then ledger destinationAddr .amount + amount'
       else ledger addr .amount)
updateLedgerAmount ledger calledAddr newAddr amount' correctAmount addr .fun
     =  ledger addr .fun
updateLedgerAmount ledger calledAddr newAddr amount' correctAmount addr .viewFunction
     = ledger addr .viewFunction
updateLedgerAmount ledger calledAddr newAddr amount' correctAmount addr .viewFunctionCost = ledger addr .viewFunctionCost


--This function we use it to update the gas by decucting from the ledger
deductGasFromLedger : (ledger : Ledger)
   → (calledAddr : Address) (gascost : ℕ)
   → (correctAmount :
         gascost ≦r ledger calledAddr .amount)
   → Ledger
deductGasFromLedger ledger calledAddr gascost correctAmount addr .amount
     = if addr ≡ᵇ calledAddr
     then subtract (ledger calledAddr .amount) gascost correctAmount
     else  ledger addr .amount
deductGasFromLedger ledger calledAddr gascost correctAmount addr .fun
    = ledger addr .fun
deductGasFromLedger ledger calledAddr gascost correctAmount addr .viewFunction
    = ledger addr .viewFunction
deductGasFromLedger ledger calledAddr gascost correctAmount addr .viewFunctionCost
    = ledger addr .viewFunctionCost

-- this function below we use it to refuend in two cases with stepEF
-- 1) when finish (first case)
-- 2) when we have error (the last case)
addWeiToLedger : (ledger : Ledger)
   → (address : Address) (amount' : Amount)
   → Ledger
addWeiToLedger ledger address amount' addr .amount
       =   if addr ≡ᵇ address
           then ledger address .amount + amount'
           else ledger addr .amount
addWeiToLedger ledger address amount' addr .fun
       =   ledger addr .fun
addWeiToLedger ledger address amount' addr .viewFunction
       = ledger addr .viewFunction
addWeiToLedger ledger address amount' addr .viewFunctionCost = ledger addr .viewFunctionCost




--- we define execute transfer Aux with one more parameter (bool)
-- if it true it will execute it without using fallback function
-- if it false it will use fallback function
executeTransferAux : (oldLedger : Ledger)
     → (currentledger : Ledger)
     → (executionStack : ExecutionStack)
     → (initialAddr : Address)
     → (lastCallAddr calledAddr : Address)
     → (cont : Msg → SmartContract Msg)
     → (gasleft : ℕ)
     → (gascost : Msg → ℕ)
     → (funNameevalState : FunctionName)
     → (msgevalState : Msg)
     → (amountSent : Amount)
     → (destinationAddr : Address)
     → (prevAmountReceived : Amount)
     → (events : List String)
     → (runfallback : Bool)
     → (cp  : OrderingLeq amountSent (currentledger calledAddr .amount))
     → StateExecFun
executeTransferAux oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr cont gasleft gascost
                      funNameevalState msgevalState amountSent destinationAddr prevAmountReceived events false (leq x)
                      = stateEF (updateLedgerAmount currentledger calledAddr destinationAddr amountSent x)
                        executionStack
                        initialAddr lastCallAddr calledAddr (cont msgevalState )
                        gasleft funNameevalState msgevalState amountSent events

executeTransferAux oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr cont gasleft gascost
                      funNameevalState msgevalState amountSent destinationAddr prevAmountReceived events true (leq x)
                      = stateEF (updateLedgerAmount currentledger calledAddr destinationAddr amountSent x)
                        (execStackEl lastCallAddr calledAddr cont gascost funNameevalState msgevalState prevAmountReceived ∷ executionStack)
                        initialAddr calledAddr destinationAddr (currentledger  destinationAddr .fun fallback (nat amountSent) )
                        gasleft fallback (nat amountSent) amountSent events
executeTransferAux oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr cont gasleft gascost
                      funNameevalState msgevalState amountSent destinationAddr prevAmountReceived events runfallback (greater x)
                      = stateEF oldLedger executionStack initialAddr lastCallAddr
                        calledAddr (error (strErr "not enough money")
                        ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]∙ events ⟩)
                        gasleft funNameevalState msgevalState amountSent events


-- lemmaExecuteTransferAuxGasEq function we added a bool parameter and we use it to prove gas
lemmaExecuteTransferAuxGasEq : (oldLedger : Ledger)
     → (currentledger : Ledger)
     → (executionStack : ExecutionStack)
     → (initialAddr : Address)
     → (lastCallAddr calledAddr : Address)
     → (cont : Msg → SmartContract Msg)
     → (gasleft1 : ℕ)
     → (gascost : Msg → ℕ)
     → (funNameevalState : FunctionName)
     → (msgevalState : Msg)
     → (amountSent : Amount)
     → (destinationAddr : Address)
     → (prevAmountReceived : Amount)
     → (events : List String)
     → (runfallback : Bool)
     → (cp  : OrderingLeq amountSent (currentledger calledAddr .amount))
     → gasleft1 ==r gasLeft
                    (executeTransferAux oldLedger currentledger executionStack initialAddr
                     lastCallAddr calledAddr cont gasleft1 gascost funNameevalState
                     msgevalState amountSent destinationAddr prevAmountReceived events runfallback cp)

lemmaExecuteTransferAuxGasEq oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr cont gasleft1 gascost
                              funNameevalState msgevalState amount' destinationAddr amountSent events false (leq x) = refl==r gasleft1
lemmaExecuteTransferAuxGasEq oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr cont gasleft1 gascost
                              funNameevalState msgevalState amount' destinationAddr amountSent events true (leq x) = refl==r gasleft1
lemmaExecuteTransferAuxGasEq oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr cont gasleft1
                             gascost funNameevalState msgevalState amount' destinationAddr amountSent events false (greater x) = refl==r gasleft1 
lemmaExecuteTransferAuxGasEq oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr cont gasleft1
                             gascost funNameevalState msgevalState amount' destinationAddr amountSent events true (greater x) = refl==r gasleft1 


-- execute transfer we added an extra element (bool value)
executeTransfer : (oldLedger : Ledger)
      → (currentledger : Ledger)
      → (execStack : ExecutionStack)
      → (initialAddr : Address)
      → (lastCallAddr calledAddr : Address)
      → (cont : Msg → SmartContract Msg)
      → (gasleft : ℕ)
      → (gascost : Msg → ℕ)
      → (funNameevalState : FunctionName)
      → (msgevalState : Msg)
      → (amountTransferred : Amount)
      → (destinationAddr : Address)
      → (prevAmountReceived : Address)
      → (events : List String)
      → (runfallback : Bool)
      → StateExecFun
executeTransfer oldLedger currentledger execStack initialAddr lastCallAddr calledAddr
                cont gasleft gascost funNameevalState msgevalState amountTransferred destinationAddr prevAmountReceived events runfallback
         = executeTransferAux oldLedger currentledger execStack initialAddr lastCallAddr calledAddr
            cont gasleft  gascost funNameevalState msgevalState amountTransferred
            destinationAddr prevAmountReceived events runfallback (compareLeq amountTransferred (currentledger calledAddr .amount))



 -- the stepEF without deducting the gasLeft
stepEF : Ledger → StateExecFun → StateExecFun
stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (callView addr fname msg) costcomputecont cont) gasLeft
                  funNameevalState msgevalState amountSent listEvent)
                  = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                    (cont (currentLedger addr .viewFunction fname msg))
                    gasLeft  fname msg amountSent listEvent
                                   

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec currentAddrLookupc costcomputecont cont) gasLeft
                  funNameevalState msgevalState amountSent listEvent)
       = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
          (cont calledAddr) gasLeft  funNameevalState msgevalState amountSent listEvent 

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec callAddrLookupc costcomputecont cont) gasLeft
                  funNameevalState msgevalState amountSent listEvent)
       = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr (cont lastCallAddr)
          gasLeft  funNameevalState msgevalState amountSent listEvent

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (updatec changedFname changedPFun cost) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = stateEF (updateLedgerpurefun currentLedger calledAddr changedFname  changedPFun cost)
          executionStack initialAddr lastCallAddr calledAddr (cont tt) gasLeft
            funNameevalState msgevalState amountSent listEvent


stepEF oldLedger (stateEF currentLedger executionStack initialAddr oldlastCallAddr oldcalledAddr
                 (exec (callc newaddr fname msg amountSent) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState prevAmountReceived listEvent)
            =  (stateEF currentLedger executionStack initialAddr oldlastCallAddr oldcalledAddr
                 (exec (transfercWithoutFallBack amountSent newaddr) (λ _ → 0)  
                 λ _ → exec (callcAssumingTransferc newaddr fname msg amountSent) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState prevAmountReceived listEvent)

stepEF oldLedger (stateEF currentLedger executionStack initialAddr oldlastCallAddr oldcalledAddr
                 (exec (callcAssumingTransferc newaddr fname msg amountTransferred) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState prevAmountReceived listEvent)
           = stateEF currentLedger
           (execStackEl oldlastCallAddr oldcalledAddr cont costcomputecont funNameevalState msgevalState prevAmountReceived  ∷ executionStack)
           initialAddr oldcalledAddr newaddr (currentLedger newaddr .fun fname msg)
           gasLeft  fname msg amountTransferred listEvent

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (transferc amountSent destinationAddr) costcomputecont cont)
                  gasLeft  funNameevalState msgevalState prevAmountReceived listEvent)
       = executeTransfer oldLedger currentLedger executionStack initialAddr lastCallAddr calledAddr
       cont gasLeft costcomputecont  funNameevalState msgevalState
           amountSent destinationAddr prevAmountReceived listEvent true

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (transfercWithoutFallBack amountSent destinationAddr) costcomputecont cont)
                  gasLeft  funNameevalState msgevalState prevAmountReceived listEvent)
       = executeTransfer oldLedger currentLedger executionStack initialAddr lastCallAddr calledAddr
       cont gasLeft costcomputecont  funNameevalState msgevalState
           amountSent destinationAddr prevAmountReceived listEvent false

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (getAmountc addrLookedUp) costcomputecont cont) gasLeft
                   funNameevalState msgevalState amountSent listEvent)
       = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
           (cont (currentLedger addrLookedUp .amount)) gasLeft
              funNameevalState msgevalState amountSent listEvent

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec getTransferAmount costcomputecont cont) gasLeft funNameevalState msgevalState amountReceived listEvent)
       = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (cont amountReceived) gasLeft funNameevalState msgevalState amountReceived listEvent

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (error errorMsg debugInfo) gasLeft  funNameevalState msgevalState amountSent listEvent)
       = stateEF oldLedger executionStack initialAddr lastCallAddr calledAddr
         (error errorMsg debugInfo)  gasLeft  funNameevalState msgevalState amountSent listEvent

stepEF oldLedger (stateEF currentLedger [] initialAddr lastCallAddr calledAddr
                 (return result) gasLeft  funNameevalState msgevalState amountSent listEvent)
       = stateEF currentLedger [] initialAddr lastCallAddr calledAddr
         (return result) gasLeft  funNameevalState msgevalState amountSent listEvent 

stepEF oldLedger (stateEF currentLedger (execStackEl prevLastCallAddress prevCalledAddress prevContinuation
                 prevCostCont prevFunName prevMsgExec prevamountSent ∷ executionStack)
                  initialAddr lastCallAddr calledAddr (return result) gasLeft funNameevalState msgevalState amountSent listEvent)
            = stateEF currentLedger executionStack initialAddr prevLastCallAddress prevCalledAddress
                        (prevContinuation result) gasLeft prevFunName prevMsgExec prevamountSent listEvent

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (eventc str) costcomputecont cont) gasLeft
                  funNameevalState msgevalState amountSent listEvent)
       = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr (cont tt)
          gasLeft  funNameevalState msgevalState amountSent (str ∷ listEvent)



lemmaStepEFpreserveGas : (oldLedger : Ledger) → (state : StateExecFun) →
                         gasLeft state ==r gasLeft (stepEF oldLedger state)

lemmaStepEFpreserveGas oldLedger (stateEF ledger [] initialAddr lastCallAddr calledAddr
  (return x) gasLeft1 funNameevalState msgevalState amountSent listEvent) = refl==r gasLeft1

lemmaStepEFpreserveGas oldLedger (stateEF ledger (x₂ ∷ executionStack₁) initialAddr lastCallAddr calledAddr
  (return x) gasLeft1 funNameevalState msgevalState amountSent listEvent) = refl==r gasLeft1

lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (error x x₁) gasLeft1 funNameevalState msgevalState amountSent listEvent) = refl==r gasLeft1

lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec (callView x₂ x₃ x₄) x x₁) gasLeft1 funNameevalState msgevalState amountSent listEvent) = refl==r gasLeft1

lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec (updatec x₂ x₃ x₄) x x₁) gasLeft1 funNameevalState msgevalState amountSent listEvent) = refl==r gasLeft1


lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec (transferc amount destinationAddr) costcomputecont cont) gasLeft1 funNameevalState msgevalState prevAmountReceived listEvent)
   = lemmaExecuteTransferAuxGasEq oldLedger ledger executionStack
     initialAddr lastCallAddr calledAddr cont gasLeft1 costcomputecont funNameevalState msgevalState amount destinationAddr prevAmountReceived
     listEvent true ((compareLeq amount (ledger calledAddr .Contract.amount)))

lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec (transfercWithoutFallBack amount destinationAddr) costcomputecont cont) gasLeft1 funNameevalState msgevalState prevAmountReceived listEvent)
   = lemmaExecuteTransferAuxGasEq oldLedger ledger executionStack
     initialAddr lastCallAddr calledAddr cont gasLeft1 costcomputecont funNameevalState msgevalState amount destinationAddr prevAmountReceived
     listEvent false ((compareLeq amount (ledger calledAddr .Contract.amount))) 


lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec (callc newaddr fname msg amountSent) cost cont) gasLeft1 funNameevalState msgevalState prevAmountReceived listEvent)
 = refl==r gasLeft1


lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec (callcAssumingTransferc newaddr fname msg amountSent) cost cont) gasLeft1 funNameevalState msgevalState prevAmountReceived listEvent)
 = refl==r gasLeft1

lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec currentAddrLookupc x x₁) gasLeft1 funNameevalState msgevalState amountSent listEvent)
 = refl==r gasLeft1

lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec callAddrLookupc x x₁) gasLeft1 funNameevalState msgevalState amountSent listEvent)
 = refl==r gasLeft1

lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec (getAmountc x₂) x x₁) gasLeft1 funNameevalState msgevalState amountSent listEvent)
 = refl==r gasLeft1

lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec getTransferAmount x x₁) gasLeft1 funNameevalState msgevalState amountSent listEvent)
 = refl==r gasLeft1

lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
  (exec (eventc x₂) x x₁) gasLeft1 funNameevalState msgevalState amountSent listEvent)
 = refl==r gasLeft1



lemmaStepEFpreserveGas2 : (oldLedger : Ledger) → (state : StateExecFun) →
                          gasLeft (stepEF oldLedger state) ==r gasLeft state
lemmaStepEFpreserveGas2 oldLedger state = sym== (gasLeft state) (gasLeft (stepEF oldLedger state))
                                          (lemmaStepEFpreserveGas oldLedger state)


-- stepEFgasAvailable which returns gasLeft
stepEFgasAvailable : StateExecFun → ℕ
stepEFgasAvailable (stateEF ledger executionStack initialAddr
                   lastCallAddr calledAddr
                   nextstep gasLeft  funNameevalState msgevalState amountSent listEvent)
                   = gasLeft


--this function simliar to stepEF and deduct the gasleft
--which returns the gas deducted
stepEFgasNeeded : StateExecFun → ℕ
stepEFgasNeeded (stateEF currentLedger [] initialAddr lastCallAddr calledAddr
                 (return result) gasLeft  funNameevalState msgevalState amountSent listEvent)
       = param .costreturn msgevalState
stepEFgasNeeded  (stateEF currentLedger (execSEl ∷ executionStack) initialAddr lastCallAddr calledAddr
                 (return result) gasLeft  funNameevalState msgevalState amountSent listEvent)
       = param .costreturn msgevalState

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec currentAddrLookupc costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = costcomputecont calledAddr

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec callAddrLookupc costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = costcomputecont lastCallAddr

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (updatec changedFname changedPufun cost) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = cost (currentLedger calledAddr .viewFunction changedFname) (currentLedger calledAddr .viewFunctionCost changedFname) msgevalState + (costcomputecont tt)

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr oldlastCallAddr oldcalledAddr
                 (exec (callc newaddr fname msg amount) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = costcomputecont msg

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr oldlastCallAddr oldcalledAddr
                 (exec (callcAssumingTransferc newaddr fname msg amount) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = costcomputecont msg


stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (transferc amount destinationAddr) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = costcomputecont emptymsg

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (transfercWithoutFallBack amount destinationAddr) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = costcomputecont emptymsg

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (getAmountc  addrLookedUp) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = costcomputecont (currentLedger addrLookedUp .amount)

stepEFgasNeeded (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                (exec getTransferAmount costcomputecont cont) gasLeft funNameevalState msgevalState amountSent listEvent)
                = costcomputecont amountSent

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (callView addr fname msg) costcompute cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = (currentLedger calledAddr .viewFunctionCost fname msg) + costcompute (currentLedger calledAddr .viewFunction fname msg)

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (error errorMsg debuginfo) gasLeft  funNameevalState msgevalState amountSent listEvent)
       = param .costerror errorMsg

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (eventc  str) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState amountSent listEvent)
       = costcomputecont tt


--This function we use it to deduct gas from evalstate not ledger
deductGas :  (statefun : StateExecFun) (gasDeducted : ℕ) → StateExecFun
deductGas (stateEF ledger executionStack initialAddr lastCallAddr calledAddr nextstep
            gasLeft  funNameevalState msgevalState amountSent listEvent) gasDeducted
       = stateEF ledger executionStack initialAddr lastCallAddr calledAddr nextstep
       (gasLeft - gasDeducted)  funNameevalState msgevalState amountSent listEvent


-- this function we use it to cpmare gas in stepEFgasNeeded with stepEFgasAvailable
stepEFAuxCompare : (oldLedger : Ledger) → (statefun : StateExecFun)
  → OrderingLeq (suc (stepEFgasNeeded statefun))(stepEFgasAvailable statefun)
  → StateExecFun
stepEFAuxCompare oldLedger statefun (leq x) = deductGas (stepEF oldLedger statefun) (suc (stepEFgasNeeded statefun))
stepEFAuxCompare oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr nextstep
                           gasLeft  funNameevalState msgevalState amountSent listEvent) (greater x)
        = stateEF oldLedger executionStack initialAddr lastCallAddr calledAddr
        (error outOfGasError ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]∙ listEvent ⟩)
           0 funNameevalState msgevalState amountSent listEvent


-- definition of stepEFwithGasError
stepEFwithGasError : (oldLedger : Ledger) → (evals : StateExecFun) → StateExecFun
stepEFwithGasError oldLedger evals  = stepEFAuxCompare oldLedger evals
                                      (compareLeq (suc (stepEFgasNeeded evals))
                                      (stepEFgasAvailable evals))

-- definition of stepEFntimes
stepEFntimes : Ledger → StateExecFun → (ntimes : ℕ) → StateExecFun
stepEFntimes oldLedger ledgerstateexecfun 0
             = ledgerstateexecfun
stepEFntimes oldLedger ledgerstateexecfun (suc n)
             = stepEFwithGasError oldLedger (stepEFntimes oldLedger ledgerstateexecfun n)
  


-- definition of stepEFntimes list
stepEFntimesList : Ledger → StateExecFun → (ntimes : ℕ) → List StateExecFun
stepEFntimesList oldLedger ledgerstateexecfun 0
                 = ledgerstateexecfun ∷ []
stepEFntimesList oldLedger ledgerstateexecfun (suc n)
                 = stepEFntimes oldLedger ledgerstateexecfun (suc n)
                   ∷ stepEFntimesList oldLedger ledgerstateexecfun n


--this function below we use it to refund as a part of septEF
---- we use stepEFwithGasError instead of stepEF in refund and stepEFntimesWithRefund
refund : StateExecFun → StateExecFun
refund (stateEF currentLedger [] initialAddr lastCallAddr calledAddr (return result)
        gasLeft  funNameevalState msgevalState amountSent listEvent)
            = stateEF (addWeiToLedger currentLedger lastCallAddr (GastoWei param gasLeft))
              [] initialAddr lastCallAddr calledAddr (return result)
               gasLeft
               funNameevalState msgevalState amountSent listEvent

refund (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
        nextstep gasLeft  funNameevalState msgevalState amountSent listEvent)
            = stepEFwithGasError ledger (stateEF ledger executionStack
              initialAddr lastCallAddr calledAddr nextstep gasLeft
                funNameevalState msgevalState amountSent listEvent)



stepEFntimesWithRefund : Ledger → StateExecFun → (ntimes : ℕ) → StateExecFun
stepEFntimesWithRefund oldLedger ledgerstateexecfun 0
                       = ledgerstateexecfun
stepEFntimesWithRefund oldLedger ledgerstateexecfun (suc n)
                       = refund (stepEFntimes oldLedger ledgerstateexecfun n)


---## similar to above but we use it with the new version of stepEFwithGasError
--initialAddr lastCallAddr calledAddr
stepLedgerFunntimesAux : (ledger : Ledger) → (initialAddr : Address) → (lastCallAddr : Address) → (calledAddr : Address) → FunctionName
                        → Msg  → Amount → (listEvent : List String) → (gascost : ℕ)  → (ntimes : ℕ)
                        → (cp  : OrderingLeq (GastoWei param gascost) (ledger lastCallAddr .amount))
                        → Maybe StateExecFun
stepLedgerFunntimesAux ledger initialAddr lastCallAddr calledAddr funname msg amounttransfered listEvent gascost  ntimes  (leq leqpro)
                             = let
                                 ledgerDeducted : Ledger
                                 ledgerDeducted = deductGasFromLedger ledger lastCallAddr (GastoWei param gascost) leqpro
                               in just ((stepEFntimes ledgerDeducted
                               (stateEF ledgerDeducted [] initialAddr lastCallAddr calledAddr
                               (ledgerDeducted calledAddr .fun funname msg)
                               gascost funname msg amounttransfered listEvent)
                               ntimes))

stepLedgerFunntimesAux ledger initialAddr lastCallAddr calledAddr funname msg amounttransfered listEvent gascost ntimes (greater greaterpro)
                             = nothing



--stepLedgerFunntimesAux ledger callAddr currentAddr funname msg gasreserved ntimes
--                       (compareLeq (GastoWei param gasreserved) (ledger callAddr .amount))
-- NNN here we need before running stepEFntimes  deduct the gas from ledger
-- NNN    it needs as argument just one gas parameter which is set to both oldgas and newgas
-- NNN    if there is not enough money in the account, then we should fail (not an error but fail)
-- NNN    so return type  should be Maybe StateExecFun

stepLedgerFunntimes : (ledger : Ledger)
                      → (initialAddr : Address)
                      → (lastCallAddr : Address)
                      → (calledAddr : Address)
                      → FunctionName
                      → Msg
                      → Amount
                      → (listEvent : List String)                      
                      → (gasreserved : ℕ)
                      → (ntimes : ℕ)
                      → Maybe StateExecFun
stepLedgerFunntimes ledger initialAddr lastCallAddr calledAddr funname msg amounttransfered listEvent gasreserved  ntimes
                     = stepLedgerFunntimesAux ledger initialAddr lastCallAddr calledAddr
                       funname msg amounttransfered listEvent gasreserved  ntimes
                       (compareLeq (GastoWei param gasreserved) (ledger lastCallAddr .amount))


--with list
stepLedgerFunntimesListAux : (ledger : Ledger)
                           → (initialAddr : Address)
                           → (lastCallAddr : Address)
                           → (calledAddr : Address)
                           → FunctionName
                           → Msg
                           → Amount
                           → (listEvent : List String)
                           → (gasreserved : ℕ)
                           → (ntimes : ℕ)
                           → (cp  : OrderingLeq (GastoWei param gasreserved) (ledger lastCallAddr .amount))
                           → Maybe (List StateExecFun)
stepLedgerFunntimesListAux ledger initialAddr lastCallAddr calledAddr funname msg amounttransfered listEvent gasreserved  ntimes (leq leqpro)
                            = let
                               ledgerDeducted : Ledger
                               ledgerDeducted = deductGasFromLedger ledger lastCallAddr (GastoWei param gasreserved) leqpro
                            in
                              just ((stepEFntimesList ledgerDeducted
                                   (stateEF ledgerDeducted [] initialAddr lastCallAddr calledAddr
                                   (ledgerDeducted calledAddr .fun funname msg) gasreserved funname msg amounttransfered listEvent) ntimes))
stepLedgerFunntimesListAux ledger initialAddr lastCallAddr calledAddr funname msg amounttransfered listEvent gasreserved ntimes (greater greaterpro)
                            = nothing


stepLedgerFunntimesList : (ledger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → (funname : FunctionName)
                          → (msg : Msg)
                          → (amounttransfered : Amount)
                          → (listEvent : List String)
                          → (gasreserved : ℕ)
                          → (ntimes : ℕ)
                          → Maybe (List StateExecFun)
stepLedgerFunntimesList ledger initialAddr lastCallAddr calledAddr funname msg amounttransfered listEvent gasreserved  ntimes
                        = stepLedgerFunntimesListAux ledger initialAddr lastCallAddr calledAddr funname msg amounttransfered listEvent gasreserved  ntimes
                       (compareLeq (GastoWei param gasreserved) (ledger lastCallAddr .amount))



-- the below is the final step and we use it to solve the return cost

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
                          → (listEvent : List String)
                          → (cp  : OrderingLeq cost gasLeft)
                          → (Ledger × MsgOrErrorWithGas)
evaluateAuxfinalStep3 oldLedger currentLedger initialAddr lastCallAddr calledAddr cost ms gasLeft funNameevalState msgevalState amountReceived listEvent (leq x)
                               =  (addWeiToLedger currentLedger initialAddr
                                   (GastoWei param (gasLeft - cost))) ,, ((theMsg ms) , ((gasLeft - cost)) gas, listEvent)
                              
evaluateAuxfinalStep3 oldLedger currentLedger initialAddr lastCallAddr calledAddr cost returnvalue gasLeft funNameevalState msgevalState amountReceived listEvent (greater x)
                               = oldLedger ,, (((err (strErr " Out Of Gass ")
                                 ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]∙ listEvent ⟩) , gasLeft gas, listEvent))





























