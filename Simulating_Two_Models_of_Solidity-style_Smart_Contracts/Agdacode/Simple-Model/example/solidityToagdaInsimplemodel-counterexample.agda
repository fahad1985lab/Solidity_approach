module Simple-Model.example.solidityToagdaInsimplemodel-counterexample where

open import Data.Nat  hiding (_<_)
open import Data.List
open import Data.Bool hiding (_<_) --hiding (_<_)
open import Data.Bool.Base   hiding (_<_)
open import Data.Nat.Base hiding (_<_)
open import Data.Maybe hiding (_>>=_)
open import Data.String hiding (length; show; _<_)
open import Data.Nat.Show

--simple model
open import Simple-Model.ledgerversion.Ledger-Simple-Model
open import Simple-Model.IOledger.IOledger-counter
open import interface.ConsoleLib
--library
open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel



--compare
_<_ : ℕ → ℕ → Bool
zero < m = true
suc n < zero = false
suc n < suc m = n < m

--Example of a simple counter

-- constant variable
const : ℕ → (Msg → SmartContract Msg)
const n msg = return (nat n)


-- define uint as in Solidity
Max_Uint : ℕ
Max_Uint = 65535 


-- test our ledger with our example
testLedger : Ledger
testLedger 1 .amount             = 40
testLedger 1 .fun "counter" m    = const 0 (nat 0)
testLedger 1 .fun "increment" m  =
                 exec currentAddrLookupc  λ addr →
                 exec (callc addr "counter" (nat 0))
                 λ{(nat oldcounter) →
                  (if oldcounter < Max_Uint
                   then exec (updatec "counter" (const (suc oldcounter)))
                (λ _ → return (nat (suc oldcounter)))
                   else
                  error (strErr "out of range error"));
                _ → error (strErr "counter returns not a number")}
  
testLedger ow .amount       = 0
testLedger ow .fun ow' ow''
  = error (strErr "Undefined")


-- To run interface
main1  :  ConsoleProg
main1  =  run  (mainBody testLedger 0)
