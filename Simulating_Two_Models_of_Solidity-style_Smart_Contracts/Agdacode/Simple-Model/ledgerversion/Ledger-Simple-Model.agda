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


-- smart contract-comands:
  data CCommands : Set where
    transferc  :  Amount → Address → CCommands
    callc      :  Address → FunctionName → Msg → CCommands
    updatec    :  FunctionName → (Msg → SmartContract Msg) → CCommands
    currentAddrLookupc  : CCommands
    callAddrLookupc     : CCommands
    getAmountc          : Address → CCommands


-- smart contract response
  CResponse : CCommands → Set
  CResponse (transferc amount addr)  =  ⊤
  CResponse (callc addr fname msg)   =  Msg
  CResponse (updatec fname fdef)     =  ⊤
  CResponse currentAddrLookupc       = Address
  CResponse callAddrLookupc          = Address
  CResponse (getAmountc addr)        = Amount



--SmartContractExec is datatype of what happens when a function is applied to its arguments.
  data SmartContract (A : Set) : Set where
    return  :  A → SmartContract A
    error   :  ErrorMsg → SmartContract A
    exec    :  (c : CCommands) → (CResponse c → SmartContract A)
            → SmartContract A


_>>==_ : {A B : Set} → SmartContract A → (A → SmartContract B) → SmartContract B
return x >>== q = q x
error x >>== q = error x
exec c x >>== q = exec c (λ r → x r >>== q)


_>>_ : {A B : Set} → SmartContract A → SmartContract B → SmartContract B
return x >> q = q
error x >> q = error x
exec c x >> q = exec c (λ r → x r >> q)



-- Definition of simple contract
record Contract : Set where
  constructor contract
  field
    amount  :  Amount
    fun     :  FunctionName → (Msg → SmartContract Msg)
open Contract public



-- ledger
Ledger : Set
Ledger = Address  → Contract


--- theses functions below we use them with do notation
call : Address  → FunctionName → (Msg → SmartContract Msg)
call addr fname msg = exec (callc addr fname msg) return

update : FunctionName → (Msg → SmartContract Msg) → SmartContract ⊤
update fname fdef = exec (updatec fname fdef) return

currentAddrLookup : SmartContract Address
currentAddrLookup = exec currentAddrLookupc return

callAddrLookup : SmartContract Address
callAddrLookup = exec callAddrLookupc return

transfer : Amount → Address → SmartContract ⊤
transfer amount addr =  exec (transferc amount addr) return



-- the definition of execution stack elements
record ExecStackEl : Set where
  constructor execStackEl
  field
    lastCallAddress  :  Address
    calledAddress    :  Address
    continuation     :  Msg → SmartContract Msg
open ExecStackEl public


-- the definition of the execution stack function function
ExecutionStack : Set
ExecutionStack = List ExecStackEl



{- StateExecFun is an intermediate state when we are evaluating a function call
   in a contract
   it consists of
        - the ledger  (which might changed because of updates)
        - executionStack  contains partially evaluated calls to other contracts together with their addresses
        - the current address
        - and the currently partially evaluated function we are evaluating
-}
record StateExecFun : Set where
  constructor stateEF
  field
    ledger           :  Ledger
    executionStack   :  ExecutionStack
    lastCallAddress  :  Address
    currentAddress   :  Address
    nextstep         :  SmartContract Msg
open StateExecFun public



--update ledger
updateLedger : Ledger →  Address → FunctionName → (Msg → SmartContract Msg) → Ledger
updateLedger ledger changedAddr changedFname f a .amount    = ledger a .amount
updateLedger ledger changedAddr changedFname f a .fun fname = if (a ≡ᵇ changedAddr) ∧ (fname ≡fun changedFname)
                                                              then f else ledger a .fun fname


--update ledger amount
updateLedgerAmount : (ledger : Ledger)
                     → (currentAddr destinationAddr : Address) (amount' : Amount)
                     → (correctAmount : amount' ≦r  ledger currentAddr .amount)
                     → Ledger
updateLedgerAmount ledger currentAddr destinationAddr amount' correctAmount addr .amount
     = if addr ≡ᵇ currentAddr
     then subtract (ledger currentAddr .amount) amount' correctAmount
     else (if addr ≡ᵇ destinationAddr
     then ledger destinationAddr .amount + amount'
     else ledger addr .amount)
updateLedgerAmount ledger currentAddr newAddr amount' correctAmount addr .fun
     = ledger addr .fun


-- execute transfer auxiliary
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

-- -- execute transfer
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

-- definition of stepEF
stepEF : Ledger → StateExecFun → StateExecFun
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


-- definition of stepEFntimes
stepEFntimes : Ledger → StateExecFun → ℕ → StateExecFun
stepEFntimes oldLedger ledgerstateexecfun 0
             = ledgerstateexecfun
stepEFntimes oldLedger ledgerstateexecfun (suc n)
      = stepEF oldLedger (stepEFntimes oldLedger ledgerstateexecfun n)


--define stepledgern times
stepLedgerFunntimes : Ledger → Address
                    → Address → FunctionName
                    → Msg → ℕ → StateExecFun
stepLedgerFunntimes ledger callAddr currentAddr funname msg n
        = stepEFntimes ledger (stateEF ledger [] callAddr currentAddr
        (ledger currentAddr .fun funname msg)) n



stepLedgerFunntimesList : Ledger → Address
                          →  Address → FunctionName
                          → Msg → ℕ → List StateExecFun
stepLedgerFunntimesList ledger callAddr currentAddr funname msg 0 = []
stepLedgerFunntimesList ledger callAddr currentAddr funname msg (suc n)
        = stepLedgerFunntimes ledger callAddr currentAddr funname msg n ∷
          stepLedgerFunntimesList ledger callAddr currentAddr funname msg n



record MsgAndLedger : Set where
  constructor msgAndLedger
  field
    theLedger  : Ledger
    msgOrError : MsgOrError

open MsgAndLedger public


{-# NON_TERMINATING #-}
evaluateNonTerminatingAuxWithLedger : Ledger → StateExecFun → MsgAndLedger
evaluateNonTerminatingAuxWithLedger oldledger (stateEF currentLedger [] callAddr currentAddr (return m)) = msgAndLedger currentLedger (theMsg m) 
evaluateNonTerminatingAuxWithLedger oldledger (stateEF currentLedger s callAddr currentAddr (error e)) = msgAndLedger oldledger (err e) 
evaluateNonTerminatingAuxWithLedger oldledger state = evaluateNonTerminatingAuxWithLedger oldledger (stepEF  oldledger state)

evaluateNonTerminatingWithLedger : Ledger → Address →  Address → FunctionName → Msg → MsgAndLedger
evaluateNonTerminatingWithLedger ledger callAddr currentAddr  funname msg
                                        =  evaluateNonTerminatingAuxWithLedger ledger (stateEF ledger [] callAddr currentAddr (ledger currentAddr .fun funname msg))


