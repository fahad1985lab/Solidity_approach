open import constantparameters

module Complex-Model.example.reentrancy-attack.executed-reentrancy-attack  where
open import Data.List
open import Data.Bool.Base 
open import Agda.Builtin.Unit
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Maybe hiding (_>>=_)
open import Data.Nat.Base 
open import Data.Nat.Show
open import Data.Fin.Base hiding (_+_; _-_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; sym ; cong)
open import Agda.Builtin.Nat using (_-_; _*_)
open import Data.String hiding (length; show) renaming (_++_ to _++str_)
open import Data.Unit
open import Data.Empty



--our work
open import Complex-Model.example.reentrancy-attack.reentrancy-attack
open import libraries.natCompare
open import Complex-Model.ledgerversion.Ledger-Complex-Model-with-reentrancy-attack exampleParameters
open import basicDataStructure
open import libraries.Mainlibrary-new-version
open import Complex-Model.ledgerversion.Ledger-Complex-Model-improved-terminate exampleParameters
open import Complex-Model.ccomand.ccommands-cresponse


--------------------------- First test   (deposit 5000 wei)
---- deposit 25000 wei at address 0 for address 2
-- the test case is correct.
--- and same as the other one
-- using function "deposit" with (nat 0) on testLedger

resultAfterdeposit : Ledger ×  MsgOrErrorWithGas
resultAfterdeposit = evaluateTerminatingfinal testLedger 2 2 0 "deposit" (nat 0) 25000 ("deposit function" ∷ []) 250


--- resultReturneddeposit return the result 
resultReturneddeposit : MsgOrErrorWithGas
resultReturneddeposit = proj₂ resultAfterdeposit

{-
theMsg (nat 0) , 231 gas,
("deposit +25000 wei at address 0 for address 2\n New balance at address 0 is 125000wei \n"
 ∷ "deposit function" ∷ [])
-}



-- obtain our ledger to get our amount for each contract
ledgerAfterdeposit : Ledger
ledgerAfterdeposit = proj₁ resultAfterdeposit 



--- check amount after deposit 25000 wei at address 0
checkamountAfterdepositAtadd0 : ℕ
checkamountAfterdepositAtadd0 = ledgerAfterdeposit 0 .amount

{- result amount at address 0 after deposit 5000 wei and before was 10000 wei
125000 
-}


--check amount after deposit 25000 wei at address 0 for address 2
checkamountAfterdepositAtadd2 : ℕ
checkamountAfterdepositAtadd2 = ledgerAfterdeposit 2 .amount
{- result amount at address 2, before was 26000 wei
 981
-}


--check viewfunction after deposit 25000 wei at address 0 for address 2 (nat 2)
checkviewFunctionAfterdeposit : MsgOrError
checkviewFunctionAfterdeposit = ledgerAfterdeposit 0 .viewFunction "balance" (nat 2)
{-
theMsg (nat 25000)

-}


--------------------------- Second test   (withdraw 5000 wei)
---- In first case we depositted 25000 wei at address 0 for address 2
-- Now we need to use withdraw 25000 wei from address 0 and transfer it to address 2
-- using function "withdraw" with (nat 25000) on ledgerAfterdeposit

resultAfterwithdraw : Ledger ×  MsgOrErrorWithGas
resultAfterwithdraw = evaluateTerminatingfinal ledgerAfterdeposit 2 2 0 "withdraw" (nat 25000) 0 ([]) 250


--- resultReturnedwithdraw return the result 
resultReturnedwithdraw : MsgOrErrorWithGas
resultReturnedwithdraw = proj₂ resultAfterwithdraw

{-
theMsg (nat 0) , 227 gas,
("Balance at address 0  = 125000 wei.\n withdraw -25000 wei." ∷ [])
-}


ledgerAfterwithdraw : Ledger
ledgerAfterwithdraw = proj₁ resultAfterwithdraw

--checkamountforAddr0Afterwithdraw to check amount at address 0 after withdraw 25000 wei
checkamountforAddr0Afterwithdraw : ℕ
checkamountforAddr0Afterwithdraw = ledgerAfterwithdraw 0 .amount 
{- result amount at address 0 after withdraw 25000 wei, before was 125000 wei
100000
-}

--checkamountforAddr1Afterwithdraw to check amount at address 2 after withdraw 25000 wei from addr 0
checkamountforAddr1Afterwithdraw : ℕ
checkamountforAddr1Afterwithdraw = ledgerAfterwithdraw 2 .amount 
{- result amount at address 2 after withdraw 25000 wei and transfer money to addr 2, before was  981 wei
25958
-}


--check viewfunction after withdraw 25000 wei from address 0 for address 2 (nat 2)
checkviewFunctionAfterwithdraw : MsgOrError
checkviewFunctionAfterwithdraw = ledgerAfterwithdraw 0 .viewFunction "balance" (nat 2)
{-
theMsg (nat 0)
-}



--------------------------- third test   (attack with 10000)
---- using attack function with amount sent 10000 wei

resultAfterattack : Ledger ×  MsgOrErrorWithGas
resultAfterattack = evaluateTerminatingfinal testLedger 2 2 1 "attack" (nat 0) 25000 ("deposit function" ∷ []) 250







--- resultReturneddeposit return the result 
resultReturnedattack : MsgOrErrorWithGas
resultReturnedattack = proj₂ resultAfterattack
{- result after attack

theMsg (nat 0) , 66 gas,
("Current balance at address 2  = 125750 wei" ∷
 "Current balance at address 1  = 0 wei" ∷
 "\nCurrent balance at address 0  = 0 wei" ∷
 "Balance at address 0  = 25000 wei.\n withdraw -25000 wei." ∷
 "Balance at address 0  = 50000 wei.\n withdraw -25000 wei." ∷
 "Balance at address 0  = 75000 wei.\n withdraw -25000 wei." ∷
 "Balance at address 0  = 100000 wei.\n withdraw -25000 wei." ∷
 "Balance at address 0  = 125000 wei.\n withdraw -25000 wei." ∷
 "deposit +25000 wei at address 0 for address 1\n New balance at address 0 is 125000wei \n"
 ∷ "deposit function" ∷ [])

-}


