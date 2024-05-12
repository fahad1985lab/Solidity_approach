open import constantparameters

module Complex-Model.example.reentrancy-attack.reentrancy-attack where
open import Data.List hiding ( _++_; reverse)
open import Data.List.Reverse 
open import Data.Bool.Base hiding (_<_; _≤_)
open import Agda.Builtin.Unit
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Maybe hiding (_>>=_)
open import Data.Nat.Base hiding (_<_)
open import Data.Nat.Show
open import Data.Fin.Base hiding (_+_; _-_; _<_; _≤_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; sym ; cong)
open import Agda.Builtin.Nat using (_-_; _*_; _<_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.String.Base hiding (show)
open import Agda.Builtin.String
open import Data.String.Properties


--our work and libraries
open import libraries.natCompare
open import Complex-Model.ledgerversion.Ledger-Complex-Model-with-reentrancy-attack
open import Complex-Model.ccomand.ccommands-cresponse
open import basicDataStructure
open import interface.ConsoleLib
open import libraries.IOlibrary-new-version
open import Complex-Model.IOledger.IOledgerReentrancyAttack 
open import libraries.Mainlibrary-new-version
open import Complex-Model.ledgerversion.Ledger-Complex-Model-improved-non-terminate


-- convert message or error to natural number
MsgorErrortoN : MsgOrError → ℕ
MsgorErrortoN (theMsg (nat n)) = n
MsgorErrortoN (theMsg (ow)) = 0
MsgorErrortoN (err x) = 0



-- myadd function to comupte two numbers
-- in case if nat will compute two number and return it
-- otherwise will return error
myadd : (amount : ℕ) → (oldValue : MsgOrError) → MsgOrError
myadd amount  (theMsg (nat oldval)) = theMsg (nat (oldval + amount))
myadd amount  (theMsg ow')  = err (strErr " Not a number")
myadd amount  err'  = err'


-- incrementViewFunction function
-- first check these addresses
-- if equal it will call myadd function
-- if not it will return old value
incrementViewFunction : (address : ℕ)  → (amount : ℕ) → (oldFun : Msg → MsgOrError) → Msg → MsgOrError
incrementViewFunction addrChecking amount oldFun (nat addr) =
                 if addrChecking ≡ᵇ addr
                    then  myadd amount (oldFun (nat addr)) 
                    else  (oldFun (nat addr))
incrementViewFunction address amount oldFun msg = oldFun msg





--mysubtract function to subtract two numbers
-- in case if nat will subtract these numbers
-- otherwise it will return error message
mysubtract : (oldValue : MsgOrError) → ℕ → MsgOrError
mysubtract  (theMsg (nat oldval)) m = theMsg (nat (oldval - m))
mysubtract  (theMsg ow') m  = err (strErr " Not a number")
mysubtract  err'  m = err'


--decrementViewFunction function
-- if these number are equal it will call mysubtract
-- otherwise it will return old value
decrementViewFunction : (address : ℕ) → (amount : ℕ) → (oldFun : Msg → MsgOrError) → Msg → MsgOrError
decrementViewFunction addrChecking amount oldFun (nat addr) =
                 if addrChecking ≡ᵇ addr
                 then  mysubtract (oldFun (nat addr)) amount 
                 else  oldFun (nat addr) 
decrementViewFunction address amount oldFun msg = oldFun msg



-- or example
testLedger : Ledger

-- bank contract at address 0
testLedger 0 .amount = 100000
testLedger 0 .fun "deposit" msg  =
          exec callAddrLookupc (λ _ → 1)
          λ lastcallAddr → exec getTransferAmount (λ _ → 1)
          λ transfAmount → exec (getAmountc 0) (λ _ → 1)
          λ amountaddr0 → exec (eventc (("deposit +" ++ show transfAmount ++ " wei"
                          ++ " at address 0 for address " ++ show lastcallAddr 
                          ++ "\n New balance at address 0 is " ++ show amountaddr0 ++ "wei \n")))(λ _ → 1)
          λ  _ → exec (updatec "balance" (λ olFun → incrementViewFunction lastcallAddr transfAmount olFun)(λ oldFun oldcost msg → 1))
          (λ n → 1) λ _ → return (nat 0)
          
testLedger 0 .fun "withdraw" (nat Amount)  =
          exec (getAmountc 0) (λ _ → 1)
          λ getresult → exec (eventc (("Balance at address 0  = "
                          ++ show getresult ++ " wei.\n" ++ " withdraw -" ++ show Amount ++ " wei.")))(λ _ → 1) 
          λ _ → (exec callAddrLookupc (λ _ → 1)
          λ lastcallAddr → exec (callView 0 "balance" (nat lastcallAddr)) (λ _ → 1)
          λ BalanceViewFunction →
            if Amount ≦b MsgorErrortoN BalanceViewFunction
            then (exec (transferc Amount lastcallAddr) (λ _ → 0)
            λ _ → exec (updatec "balance" (λ oldFun → decrementViewFunction lastcallAddr Amount oldFun)(λ oldFun oldcost msg → 1))(λ n → 1)
                  λ x → return (nat 0))
            else error (strErr (" Amount to withdraw is bigger than the balance for the account withdrawing and lastcallAddr = " ++ (show lastcallAddr))) ⟨ 1 >> 1 ∙ "withdraw"  [ nat 0 ]∙ [] ⟩)

testLedger 0 .fun "withdraw" ow  =
         error (strErr (" withdraw function called with msg not being a nat number" ++ (show 0))) ⟨ 1 >> 1 ∙ "withdraw"  [ nat 0 ]∙ [] ⟩

testLedger 0 .viewFunction "balance" msg  = theMsg (nat 0)


-- attack contract at address 1
testLedger 1 .amount = 0
testLedger 1 .fun "fallback" msg =
          exec getTransferAmount (λ _ → 1)
          λ transfAmount → exec callAddrLookupc (λ _ → 1)
          λ lastcallAddr → exec (getAmountc 0) (λ _ → 1)
         (λ balance → if transfAmount ≦b balance 
                       then exec (callc 0 "withdraw" (nat transfAmount) 0)(λ _ → 1) (λ resultofcallc → return (nat 0))
                       else return (nat 0)) 

testLedger 1 .fun "attack" msg   =
          exec callAddrLookupc (λ _ → 0)
          λ lastcallAddr → exec getTransferAmount (λ _ → 0) 
          λ transferAmount →
             if 1 ≦b transferAmount
             then (exec (callc 0 "deposit" (nat 0) transferAmount) (λ _ → 0)
                  λ resultofdeposit → exec (callc 0 "withdraw" (nat transferAmount) 0) (λ _ → 1)
                  λ resultofwithdraw → exec currentAddrLookupc (λ _ → 0)
                  λ curraddr → exec (getAmountc curraddr) (λ _ → 1)
                  λ amountofcurrntaddr →
                  exec (transferc amountofcurrntaddr lastcallAddr)(λ _ → 0)
                   λ _ → exec (getAmountc 0)  (λ _ → 1)
                   λ amountofbankaddr → exec (getAmountc curraddr) (λ _ → 1)
                   λ amountoflastcalladd → exec (getAmountc lastcallAddr) (λ _ → 1)
                   λ amountoflastcalladdr → exec (eventc (("\n" ++ "Current balance at address 0  = " ++ show amountofbankaddr ++ " wei")))
                  (λ _ → 1) λ _ → exec (eventc (( "Current balance at address 1  = " ++ show amountoflastcalladd ++ " wei")))
                  (λ _ → 1) λ _ → exec (eventc (( "Current balance at address 2  = " ++ show amountoflastcalladdr ++ " wei")))
                  (λ _ → 1) λ _ → return (nat 0))
                  else error (strErr " The amount is zero ") ⟨ 1 >> 1 ∙ "attack"  [ msg ]∙ [] ⟩     

-- attaker contract only has amount
testLedger 2 .amount = 26000

-- for other address
testLedger ow .amount  = 0
testLedger ow .fun "fallback" ow''  = return ow''
testLedger ow .fun ow' ow'' = error (strErr "Undefined") ⟨ ow >> ow ∙ ow' [ ow'' ]∙ [] ⟩
testLedger ow .viewFunction ow' ow'' = theMsg (nat 0)
testLedger ow .viewFunctionCost ow' ow''  = 1





--main program IO
main  : ConsoleProg
main  = run (mainBody ⟨ testLedger ledger, 0 initialAddr, 100 gas, 0 amountR⟩)



