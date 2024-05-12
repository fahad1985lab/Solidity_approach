module Simple-Model.example.examplecounter where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe hiding (_>>=_)
open import Data.String hiding (length)


--simple model
open import Simple-Model.ledgerversion.Ledger-Simple-Model

--library
open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel
open import interface.ConsoleLib

--IOledger
open import Simple-Model.IOledger.IOledger-counter



--Example of a simple counter
const : ℕ → (Msg → SmartContract Msg)
const n msg = return (nat n)


-- test our ledger with our example
testLedger : Ledger

-- the example below we used in our paper
testLedger 0 .amount  = 20
testLedger 1 .amount             = 40
testLedger 1 .fun "counter" m   = const 0 (nat 0)
testLedger 1 .fun "increment" m  = exec currentAddrLookupc  λ addr →
                                   exec (callc addr "counter" (nat 0))
                                   λ{(nat n) → exec (updatec "counter" (const (suc n)))
                                             λ _ → return (nat (suc n));
                                  _        → error (strErr "counter returns not a number")}
testLedger 1 .fun "transfer" m  = exec (transferc 10  0) λ _ → return m

testLedger ow .amount           = 0
testLedger ow .fun ow' ow''     = error (strErr "Undefined")


-- To run IO
main  :  ConsoleProg 
main  =  run  (mainBody testLedger 0)
