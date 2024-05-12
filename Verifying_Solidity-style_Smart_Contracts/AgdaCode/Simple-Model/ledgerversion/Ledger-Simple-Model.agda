module Simple-Model.ledgerversion.Ledger-Simple-Model where

open import Data.Nat
open import Agda.Builtin.Nat using (_-_)
open import Data.Unit
open import Data.List
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe  hiding (_>>=_)
open import Data.String hiding (length)

--library for simple model
open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel

-- main library
open import libraries.natCompare




mutual


--contract-commands
  data CCommands : Set where
    transferc  :  Amount → Address → CCommands
    callc      :  Address → FunctionName → Msg → CCommands
    updatec    :  FunctionName → (Msg → SmartContract Msg) → CCommands
    currentAddrLookupc  : CCommands
    callAddrLookupc     : CCommands
    getAmountc          : Address → CCommands


--contract-response
  CResponse : CCommands → Set
  CResponse (transferc amount addr)  =  ⊤
  CResponse (callc addr fname msg)   =  Msg
  CResponse (updatec fname fdef)     =  ⊤
  CResponse currentAddrLookupc       = Address
  CResponse callAddrLookupc          = Address
  CResponse (getAmountc addr)        = Amount



--define smart contract
  data SmartContract (A : Set) : Set where
    return  :  A → SmartContract A
    error   :  ErrorMsg → SmartContract A
    exec    :  (c : CCommands)
            → (CResponse c → SmartContract A)
            → SmartContract A



--define contract
record Contract : Set where
  constructor contract
  field
    amount  :  Amount
    fun     :  FunctionName
            → (Msg → SmartContract Msg)
open Contract public


-- define ledger
Ledger : Set
Ledger = Address  → Contract


--define exeute stack element
record ExecStackEl : Set where
  constructor execStackEl
  field
    lastCallAddress  :  Address
    calledAddress    :  Address
    continuation     :  Msg → SmartContract Msg
open ExecStackEl public


ExecutionStack : Set
ExecutionStack = List ExecStackEl


--define state execution function
record StateExecFun : Set where
  constructor stateEF
  field
    ledger           :  Ledger
    executionStack   :  ExecutionStack
    lastCallAddress  :  Address
    currentAddress   :  Address
    nextstep         :  SmartContract Msg
open StateExecFun public



--define update ledger
updateLedger : Ledger →  Address → FunctionName → (Msg → SmartContract Msg) → Ledger
updateLedger ledger changedAddr changedFname f a .amount
         = ledger a .amount
updateLedger ledger changedAddr changedFname f a .fun fname
         = if (a ≡ᵇ changedAddr) ∧ (fname ≡fun changedFname)
            then f else ledger a .fun fname


-- update ledger amount
updateLedgerAmount : (ledger : Ledger)
         → (currentAddr destinationAddr : Address)
               (amount' : Amount)
         → (correctAmount : amount' ≦r  ledger currentAddr .amount)
         → Ledger
updateLedgerAmount ledger currentAddr destinationAddr amount' correctAmount addr .amount
     = if addr ≡ᵇ currentAddr
     then (if addr ≡ᵇ destinationAddr
           then ledger addr .amount
           else subtract (ledger currentAddr .amount) amount' correctAmount)
     else (if addr ≡ᵇ destinationAddr
     then ledger destinationAddr .amount + amount'
     else ledger addr .amount)
updateLedgerAmount ledger currentAddr newAddr amount' correctAmount addr .fun
     = ledger addr .fun




--define execute transfer aux
executeTransferAux : (oldLedger currentLedger : Ledger)
                  → (executionStack : ExecutionStack)
                  → (callAddr currentAddr : Address)
                  → (amount' : Amount)
                  → (destinationAddr : Address)
                  → (cont : SmartContract Msg)
                  → (cp  : OrderingLeq amount' (currentLedger currentAddr .amount  ))
                  → StateExecFun
executeTransferAux oldLedger currentLedger executionStack callAddr currentAddr amount' destinationAddr cont (leq x) =
          stateEF (updateLedgerAmount currentLedger currentAddr destinationAddr amount' x)
             executionStack callAddr currentAddr cont

executeTransferAux oldLedger currentLedger executionStack callAddr currentAddr amount destinationAddr cont (greater x) =
         stateEF oldLedger executionStack callAddr currentAddr
             (error (strErr "not enough money"))

--define execute transfer
executeTransfer : (oldLedger currentLedger : Ledger)
                  → ExecutionStack
                  → (callAddr currentAddr : Address)
                  → (amount' : Amount)
                  → (destinationAddr : Address)
                  → (cont : SmartContract Msg)
                  → StateExecFun
executeTransfer oldLedger currentLedger exexecutionStack callAddr currentAddr amount' destinationAddr cont
                = executeTransferAux oldLedger currentLedger exexecutionStack callAddr currentAddr amount'
                   destinationAddr cont  (compareLeq amount' (currentLedger currentAddr .amount  ))

--define stepEF
stepEF : Ledger → StateExecFun → StateExecFun
stepEFntimes : Ledger → StateExecFun → ℕ → StateExecFun
stepEF oldLedger (stateEF currentLedger [] callAddr currentAddr (return result))
       = stateEF currentLedger  [] callAddr currentAddr (return result)
stepEF oldLedger (stateEF currentLedger (execSEl ∷ executionStack) callAddr currentAddr (return result))
       = stateEF currentLedger executionStack callAddr  (execSEl .calledAddress) (execSEl .continuation result)
stepEF oldLedger (stateEF currentLedger executionStack callAddr currentAddr (exec currentAddrLookupc cont))
       = stateEF currentLedger executionStack callAddr currentAddr (cont currentAddr)
stepEF oldLedger (stateEF currentLedger executionStack callAddr currentAddr (exec callAddrLookupc cont))
       = stateEF currentLedger executionStack callAddr currentAddr (cont callAddr)
stepEF oldLedger (stateEF currentLedger executionStack callAddr currentAddr
                            (exec (updatec changedFname changedFdef) cont))
       = stateEF (updateLedger currentLedger currentAddr changedFname changedFdef)
                   executionStack callAddr currentAddr (cont tt)
stepEF oldLedger (stateEF currentLedger executionStack oldCalladdr oldCurrentAddr (exec (callc newaddr fname msg) cont))
       = stateEF currentLedger (execStackEl oldCalladdr oldCurrentAddr cont  ∷ executionStack)  oldCurrentAddr newaddr
                   (currentLedger newaddr .fun fname msg)

stepEF oldLedger (stateEF currentLedger executionStack callAddr currentAddr (exec (transferc amount destinationAddr ) cont))
       = executeTransfer oldLedger currentLedger executionStack callAddr currentAddr amount destinationAddr (cont tt)
stepEF oldLedger (stateEF currentLedger executionStack callAddr currentAddr (exec (getAmountc  addrLookedUp) cont))
       = stateEF currentLedger executionStack callAddr currentAddr (cont (currentLedger addrLookedUp .amount))
stepEF oldLedger (stateEF currentLedger executionStack callAddr currentAddr (error errorMsg))
       = stateEF oldLedger executionStack callAddr currentAddr (error errorMsg)



stepEFntimes oldLedger ledgerstateexecfun 0
             = ledgerstateexecfun
stepEFntimes oldLedger ledgerstateexecfun (suc n)
      = stepEF oldLedger (stepEFntimes oldLedger ledgerstateexecfun n)


--define step ledger ntimes
stepLedgerFunntimes : Ledger → Address
        → Address → FunctionName
        → Msg → ℕ → StateExecFun
stepLedgerFunntimes ledger callAddr currentAddr funname msg n
        = stepEFntimes ledger (stateEF ledger [] callAddr currentAddr
        (ledger currentAddr .fun funname msg)) n

--define stepef ledger list
stepLedgerFunntimesList : Ledger → Address
                          →  Address → FunctionName
                          → Msg → ℕ → List StateExecFun
stepLedgerFunntimesList ledger callAddr currentAddr funname msg 0 = []
stepLedgerFunntimesList ledger callAddr currentAddr funname msg (suc n)
        = stepLedgerFunntimes ledger callAddr currentAddr funname msg n ∷
          stepLedgerFunntimesList ledger callAddr currentAddr funname msg n



{-# NON_TERMINATING #-}

evaluateNonTerminatingAux : Ledger → StateExecFun → NatOrError
evaluateNonTerminatingAux oldledger (stateEF currentLedger [] callAddr currentAddr (return (nat n))) = nat n
evaluateNonTerminatingAux oldledger (stateEF currentLedger [] callAddr currentAddr (return otherwise)) = err (strErr "result returned not nat")
evaluateNonTerminatingAux oldledger (stateEF currentLedger s callAddr currentAddr (error msg)) = err msg
evaluateNonTerminatingAux oldledger state = evaluateNonTerminatingAux oldledger (stepEF  oldledger state)

evaluateNonTerminating : Ledger → Address →  Address → FunctionName → Msg → NatOrError
evaluateNonTerminating ledger callAddr currentAddr  funname msg =  evaluateNonTerminatingAux ledger (stateEF ledger [] callAddr currentAddr (ledger currentAddr .fun funname msg))
