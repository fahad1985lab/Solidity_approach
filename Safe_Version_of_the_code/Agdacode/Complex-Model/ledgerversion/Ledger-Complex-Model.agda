open import constantparameters

module Complex-Model.ledgerversion.Ledger-Complex-Model (param : ConstantParameters) where

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




-- update view function in the ledger
updateLedgerviewfun : Ledger → Address
       → FunctionName
       → ((Msg → MsgOrError) → (Msg → MsgOrError))
       → ((Msg → MsgOrError) → (Msg → ℕ) → Msg → ℕ)
       → Ledger
updateLedgerviewfun ledger changedAddr changedFname f g a .amount = ledger a .amount
updateLedgerviewfun ledger changedAddr changedFname f g a .fun  = ledger a .fun
updateLedgerviewfun ledger changedAddr changedFname f g a .viewFunction fname =
       if (changedFname ≡fun fname) then  f (ledger a .viewFunction fname)
                         else  ledger a .viewFunction fname
updateLedgerviewfun ledger changedAddr changedFname f g a .viewFunctionCost fname =
          if (changedFname ≡fun fname) then  g (ledger a .viewFunction fname) (ledger a .viewFunctionCost fname)
                         else  ledger a .viewFunctionCost fname



--update ledger amount
updateLedgerAmount : (ledger : Ledger)
                   → (calledAddr destinationAddr : Address) (amount' : Amount)
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
--rename gasPrice to gascost
deductGasFromLedger : (ledger : Ledger)
                    → (calledAddr : Address) (gascost : ℕ)
                    → (correctAmount : gascost ≦r ledger calledAddr .amount)
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


-- this function below we use it to refuend in two cases with steEF
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


-- execute transfer auxiliary
executeTransferAux : (oldLedger : Ledger)
                   → (currentledger : Ledger)
                   → (executionStack : ExecutionStack)
                   → (initialAddr : Address)
                   → (lastCallAddr calledAddr : Address)
                   → (cont : SmartContract Msg) → (gasleft : ℕ)
                   → (funNameevalState : FunctionName)
                   → (msgevalState : Msg)
                   → (amount' : Amount)
                   → (destinationAddr : Address)
                   → (cp  : OrderingLeq amount' (currentledger calledAddr .amount))
                   → StateExecFun
executeTransferAux oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr cont gasleft
                   funNameevalState msgevalState amount' destinationAddr (leq x)
         = stateEF (updateLedgerAmount currentledger calledAddr destinationAddr amount' x)
          executionStack initialAddr lastCallAddr calledAddr cont gasleft funNameevalState msgevalState
executeTransferAux oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr cont gasleft
                   funNameevalState msgevalState amount' destinationAddr (greater x)
          = stateEF oldLedger executionStack initialAddr lastCallAddr calledAddr
            (error  (strErr "not enough money")
            ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩)
             gasleft funNameevalState msgevalState


-- proof transfer Aux 
lemmaExecuteTransferAuxGasEq : (oldLedger : Ledger)
                              → (currentledger : Ledger)
                              → (executionStack : ExecutionStack)
                              → (initialAddr : Address)
                              → (lastCallAddr calledAddr : Address)
                              → (cont : SmartContract Msg) → (gasleft1 : ℕ)
                              → (funNameevalState : FunctionName)
                              → (msgevalState : Msg)
                              → (amount' : Amount)
                              → (destinationAddr : Address)
                              → (cp  : OrderingLeq amount' (currentledger calledAddr .amount))
                              → gasleft1 ==r gasLeft
                                 (executeTransferAux oldLedger currentledger executionStack initialAddr
                                  lastCallAddr calledAddr cont gasleft1 funNameevalState
                                  msgevalState amount' destinationAddr cp)
lemmaExecuteTransferAuxGasEq oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr
                             cont gasleft1 funNameevalState msgevalState amount' destinationAddr (leq x)     = refl==r gasleft1
lemmaExecuteTransferAuxGasEq oldLedger currentledger executionStack initialAddr lastCallAddr calledAddr
                             cont gasleft1 funNameevalState msgevalState amount' destinationAddr (greater x) = refl==r gasleft1


-- execute transfer
executeTransfer : (oldLedger : Ledger)
                → (currentledger : Ledger)
                → (execStack : ExecutionStack)
                → (initialAddr : Address)
                → (lastCallAddr calledAddr : Address)
                → (cont : SmartContract Msg)
                → (gasleft : ℕ)
                → (funNameevalState : FunctionName)
                → (msgevalState : Msg)
                → (amount' : Amount)
                → (destinationAddr : Address)
                → StateExecFun
--@END
executeTransfer oldLedger currentledger execStack initialAddr lastCallAddr calledAddr
                cont gasleft  funNameevalState msgevalState amount' destinationAddr
         = executeTransferAux oldLedger currentledger execStack initialAddr lastCallAddr calledAddr
            cont gasleft  funNameevalState msgevalState amount'
            destinationAddr (compareLeq amount' (currentledger calledAddr .amount))



-- the stepEF without deducting the gasLeft
stepEF : Ledger → StateExecFun → StateExecFun
stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec currentAddrLookupc costcomputecont cont) gasLeft funNameevalState msgevalState)
       = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
          (cont calledAddr) gasLeft  funNameevalState msgevalState 

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec callAddrLookupc costcomputecont cont) gasLeft funNameevalState msgevalState)
       = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr (cont lastCallAddr)
          gasLeft  funNameevalState msgevalState

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (updatec changedFname changedPFun cost) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState)
       = stateEF (updateLedgerviewfun currentLedger calledAddr changedFname  changedPFun cost)
          executionStack initialAddr lastCallAddr calledAddr (cont tt) gasLeft
            funNameevalState msgevalState

stepEF oldLedger (stateEF currentLedger executionStack initialAddr oldlastCallAddr oldcalledAddr
                 (exec (callc newaddr fname msg) costcomputecont cont) gasLeft funNameevalState msgevalState)
       = stateEF currentLedger
           (execStackEl oldlastCallAddr oldcalledAddr cont costcomputecont funNameevalState msgevalState ∷ executionStack)
           initialAddr oldcalledAddr newaddr (currentLedger newaddr .fun fname msg) gasLeft fname msg

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (transferc amount destinationAddr) costcomputecont cont) gasLeft  funNameevalState msgevalState)
       = executeTransfer oldLedger currentLedger executionStack initialAddr lastCallAddr calledAddr
       (cont tt) gasLeft  funNameevalState msgevalState amount destinationAddr

stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (getAmountc addrLookedUp) costcomputecont cont) gasLeft funNameevalState msgevalState)
       = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
           (cont (currentLedger addrLookedUp .amount)) gasLeft funNameevalState msgevalState


stepEF oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                   (exec (raiseException cost str) costcomputecont cont)
                   gasLeft funNameevalState msgevalState)
       = stateEF oldLedger executionStack initialAddr lastCallAddr calledAddr
         (error  (strErr str) ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩)
         gasLeft funNameevalState msgevalState


stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (error errorMsg debugInfo) gasLeft  funNameevalState msgevalState)
       = stateEF oldLedger executionStack initialAddr lastCallAddr calledAddr
         (error errorMsg debugInfo)  gasLeft  funNameevalState msgevalState


stepEF oldLedger (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (callView addr fname msg) costcomputecont cont) gasLeft
                  funNameevalState msgevalState)
       = stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
         (cont (currentLedger addr .viewFunction fname msg)) gasLeft fname msg


stepEF oldLedger (stateEF currentLedger [] initialAddr lastCallAddr calledAddr
                 (return cost result) gasLeft  funNameevalState msgevalState)
       = stateEF currentLedger [] initialAddr lastCallAddr calledAddr
         (return cost result) gasLeft  funNameevalState msgevalState 

stepEF oldLedger (stateEF currentLedger (execStackEl prevLastCallAddress prevCalledAddress prevContinuation
                 prevCostCont prevFunName prevMsgExec ∷ executionStack)
                  initialAddr lastCallAddr calledAddr (return cost result) gasLeft funNameevalState msgevalState)
       = stateEF currentLedger executionStack initialAddr prevLastCallAddress prevCalledAddress
          (prevContinuation result) gasLeft prevFunName prevMsgExec


--some lemmas to prove and we use them with our executevotingexample.agda
lemmaStepEFpreserveGas : (oldLedger : Ledger) → (state : StateExecFun) →
                         gasLeft state ==r gasLeft (stepEF oldLedger state)
lemmaStepEFpreserveGas oldLedger (stateEF ledger [] initialAddr lastCallAddr calledAddr
                       (return x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1
lemmaStepEFpreserveGas oldLedger (stateEF ledger (x₂ ∷ executionStack₁) initialAddr lastCallAddr calledAddr
                       (return x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1
lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                       (error x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1
lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                       (exec (callView x₂ x₃ x₄) x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1
lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                       (exec (updatec x₂ x₃ x₄) x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1
lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                       (exec (raiseException x₂ x₃) x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1
lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                       (exec (transferc amount destinationAddr) costcomputecont cont) gasLeft1 funNameevalState msgevalState)
                       = lemmaExecuteTransferAuxGasEq oldLedger ledger executionStack initialAddr lastCallAddr calledAddr
                       (cont tt) gasLeft1 funNameevalState msgevalState amount destinationAddr
                       ((compareLeq amount (ledger calledAddr .Contract.amount)))
lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                       (exec (callc x₂ x₃ x₄) x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1
lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                       (exec currentAddrLookupc x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1
lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                       (exec callAddrLookupc x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1
lemmaStepEFpreserveGas oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                       (exec (getAmountc x₂) x x₁) gasLeft1 funNameevalState msgevalState) = refl==r gasLeft1



lemmaStepEFpreserveGas2 : (oldLedger : Ledger) → (state : StateExecFun) →
                          gasLeft (stepEF oldLedger state) ==r gasLeft state
lemmaStepEFpreserveGas2 oldLedger state = sym== (gasLeft state) (gasLeft (stepEF oldLedger state))
                                          (lemmaStepEFpreserveGas oldLedger state)


-- stepEFgasAvailable which returns gasLeft
stepEFgasAvailable : StateExecFun → ℕ
stepEFgasAvailable (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                   nextstep gasLeft  funNameevalState msgevalState)
                   = gasLeft


--this function simliar to stepEF and deduct the gasleft
--which returns the gas deducted
stepEFgasNeeded : StateExecFun → ℕ
stepEFgasNeeded  (stateEF currentLedger [] initialAddr lastCallAddr calledAddr
                 (return cost result) gasLeft  funNameevalState msgevalState)
       = cost
stepEFgasNeeded  (stateEF currentLedger (execSEl ∷ executionStack) initialAddr lastCallAddr calledAddr
                 (return cost result) gasLeft  funNameevalState msgevalState)
       = cost

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec currentAddrLookupc costcomputecont cont)
                 gasLeft  funNameevalState msgevalState)
       = costcomputecont calledAddr

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec callAddrLookupc costcomputecont cont)
                 gasLeft  funNameevalState msgevalState)
       = costcomputecont lastCallAddr

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (updatec changedFname changedPufun cost) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState)
       = cost (currentLedger calledAddr .viewFunction changedFname) (currentLedger calledAddr .viewFunctionCost changedFname) msgevalState + (costcomputecont tt)


stepEFgasNeeded (stateEF currentLedger executionStack initialAddr oldlastCallAddr oldcalledAddr
                 (exec (callc newaddr fname msg) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState)
       = costcomputecont msg

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (transferc amount destinationAddr) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState)
       = costcomputecont tt

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (getAmountc  addrLookedUp) costcomputecont cont)
                 gasLeft  funNameevalState msgevalState)
       = costcomputecont (currentLedger addrLookedUp .amount)


stepEFgasNeeded (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
                 (exec (raiseException cost str) costcomputecont cont)
                 gasLeft funNameevalState msgevalState)
                 = cost

stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (exec (callView addr fname msg) costcompute cont)
                 gasLeft  funNameevalState msgevalState)
       = (currentLedger calledAddr .viewFunctionCost fname msg) + costcompute (currentLedger calledAddr .viewFunction fname msg)


stepEFgasNeeded (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
                 (error errorMsg debuginfo) gasLeft  funNameevalState msgevalState)
       = param .costerror errorMsg


--This function we use it to deduct gas from evalstate not ledger
deductGas :  (statefun : StateExecFun) (gasDeducted : ℕ) → StateExecFun
deductGas (stateEF ledger executionStack initialAddr lastCallAddr calledAddr nextstep
            gasLeft  funNameevalState msgevalState) gasDeducted
       = stateEF ledger executionStack initialAddr lastCallAddr calledAddr nextstep
       (gasLeft - gasDeducted)  funNameevalState msgevalState


-- this function we use it to cpmare gas in stepEFgasNeeded with stepEFgasAvailable
stepEFAuxCompare : (oldLedger : Ledger) → (statefun : StateExecFun)
                → OrderingLeq (suc (stepEFgasNeeded statefun))(stepEFgasAvailable statefun)
                → StateExecFun
stepEFAuxCompare oldLedger statefun (leq x) = deductGas (stepEF oldLedger statefun) (suc (stepEFgasNeeded statefun))
stepEFAuxCompare oldLedger (stateEF ledger executionStack initialAddr lastCallAddr calledAddr nextstep
                 gasLeft  funNameevalState msgevalState) (greater x)
        = stateEF oldLedger executionStack initialAddr lastCallAddr calledAddr (error outOfGasError
            ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩) 0
            funNameevalState msgevalState


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
refund (stateEF currentLedger [] initialAddr lastCallAddr calledAddr (return cost result)
        gasLeft  funNameevalState msgevalState)
            = stateEF (addWeiToLedger currentLedger lastCallAddr (GastoWei param gasLeft))
              [] initialAddr lastCallAddr calledAddr (return cost result)
               gasLeft funNameevalState msgevalState
refund (stateEF currentLedger executionStack initialAddr lastCallAddr calledAddr
       (error errorMsg debugInfo) gasLeft  funNameevalState msgevalState)
            = stateEF (addWeiToLedger currentLedger  lastCallAddr (GastoWei param gasLeft))
              executionStack initialAddr lastCallAddr calledAddr
              (error errorMsg debugInfo) gasLeft
               funNameevalState msgevalState
refund (stateEF ledger executionStack initialAddr lastCallAddr calledAddr
        nextstep gasLeft  funNameevalState msgevalState)
            = stepEFwithGasError ledger (stateEF ledger executionStack
              initialAddr lastCallAddr calledAddr nextstep gasLeft
                funNameevalState msgevalState)


stepEFntimesWithRefund : Ledger → StateExecFun → (ntimes : ℕ) → StateExecFun
stepEFntimesWithRefund oldLedger ledgerstateexecfun 0
                       = ledgerstateexecfun
stepEFntimesWithRefund oldLedger ledgerstateexecfun (suc n)
                       = refund (stepEFntimes oldLedger ledgerstateexecfun n)


---## similar to above but we use it with the new version of stepEFwithGasError
--initialAddr lastCallAddr calledAddr
stepLedgerFunntimesAux : (ledger : Ledger) → (initialAddr : Address) → (lastCallAddr : Address) → (calledAddr : Address) → FunctionName
                        → Msg  → (gascost : ℕ)  → (ntimes : ℕ)
                        → (cp  : OrderingLeq (GastoWei param gascost) (ledger lastCallAddr .amount))
                        → Maybe StateExecFun
stepLedgerFunntimesAux ledger initialAddr lastCallAddr calledAddr funname msg gascost  ntimes  (leq leqpro)
                             = let
                                 ledgerDeducted : Ledger
                                 ledgerDeducted = deductGasFromLedger ledger lastCallAddr (GastoWei param gascost) leqpro
                               in just (stepEFntimes ledgerDeducted
                               (stateEF ledgerDeducted [] initialAddr lastCallAddr calledAddr
                               (ledgerDeducted calledAddr .fun funname msg)
                               gascost funname msg)
                               ntimes)

stepLedgerFunntimesAux ledger initialAddr lastCallAddr calledAddr funname msg gascost ntimes (greater greaterpro)
                             = nothing

--stepLedgerFunntimesAux ledger callAddr currentAddr funname msg gasreserved ntimes
--                       (compareLeq (GastoWei param gasreserved) (ledger callAddr .amount))
-- NNN here we need before running stepEFntimes  deduct the gas from ledger
-- NNN    it needs as argument just one gas parameter which is set to both oldgas and newgas
-- NNN    if there is not enough money in the account, then we should fail (not an error but fail)
-- NNN    so return type  should be Maybe EvalState

stepLedgerFunntimes : (ledger : Ledger)
                      → (initialAddr : Address)
                      → (lastCallAddr : Address)
                      → (calledAddr : Address)
                      → FunctionName
                      → Msg
                      → (gasreserved : ℕ)
                      → (ntimes : ℕ)
                      → Maybe StateExecFun
stepLedgerFunntimes ledger initialAddr lastCallAddr calledAddr funname msg gasreserved  ntimes
                     = stepLedgerFunntimesAux ledger initialAddr lastCallAddr calledAddr
                       funname msg gasreserved  ntimes
                       (compareLeq (GastoWei param gasreserved) (ledger lastCallAddr .amount))


--with list
stepLedgerFunntimesListAux : (ledger : Ledger)
                           → (initialAddr : Address)
                           → (lastCallAddr : Address)
                           → (calledAddr : Address)
                           → FunctionName
                           → Msg
                           → (gasreserved : ℕ)
                           → (ntimes : ℕ)
                           → (cp  : OrderingLeq (GastoWei param gasreserved) (ledger lastCallAddr .amount))
                           → Maybe (List StateExecFun)
stepLedgerFunntimesListAux ledger initialAddr lastCallAddr calledAddr funname msg gasreserved  ntimes (leq leqpro)
                            = let
                               ledgerDeducted : Ledger
                               ledgerDeducted = deductGasFromLedger ledger lastCallAddr (GastoWei param gasreserved) leqpro
                            in
                              just (stepEFntimesList ledgerDeducted
                                   (stateEF ledgerDeducted [] initialAddr lastCallAddr calledAddr
                                   (ledgerDeducted calledAddr .fun funname msg) gasreserved funname msg) ntimes)
stepLedgerFunntimesListAux ledger initialAddr lastCallAddr calledAddr funname msg gasreserved ntimes (greater greaterpro)
                            = nothing


stepLedgerFunntimesList : (ledger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → (funname : FunctionName)
                          → (msg : Msg)
                          → (gasreserved : ℕ)
                          → (ntimes : ℕ)
                          → Maybe (List StateExecFun)
stepLedgerFunntimesList ledger initialAddr lastCallAddr calledAddr funname msg gasreserved  ntimes
                        = stepLedgerFunntimesListAux ledger initialAddr lastCallAddr calledAddr funname msg gasreserved  ntimes
                       (compareLeq (GastoWei param gasreserved) (ledger lastCallAddr .amount))





--clear version of evaluateNonTerminating'
-- the below is the final step and we use it to solve the return cost

evaluateAuxfinal0' : (oldLedger : Ledger)
                          → (currentLedger : Ledger)
                          → (initialAddr : Address)
                          → (lastCallAddr : Address)
                          → (calledAddr : Address)
                          → (cost : ℕ)
                          → (returnvalue : Msg)
                          → (gasLeft : ℕ)
                          → (funNameevalState : FunctionName)
                          → (msgevalState : Msg)
                          → (cp  : OrderingLeq cost gasLeft)
                          → (Ledger × MsgOrErrorWithGas)
evaluateAuxfinal0' oldLedger currentLedger initialAddr lastCallAddr calledAddr cost ms gasLeft funNameevalState msgevalState (leq x)
                               =  (addWeiToLedger currentLedger initialAddr
                                   (GastoWei param (gasLeft - cost))) ,, (theMsg ms , (gasLeft - cost) gas)

evaluateAuxfinal0' oldLedger currentLedger initialAddr lastCallAddr calledAddr cost returnvalue gasLeft funNameevalState msgevalState (greater x)
                               = oldLedger ,, ((err (strErr " Out Of Gass ") ⟨ lastCallAddr >> initialAddr ∙ funNameevalState [ msgevalState ]⟩) , gasLeft gas)
