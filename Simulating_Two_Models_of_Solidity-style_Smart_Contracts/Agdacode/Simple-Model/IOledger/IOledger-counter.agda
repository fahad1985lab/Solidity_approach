module Simple-Model.IOledger.IOledger-counter where

open import Data.Nat
open import Data.List hiding (_++_)
open import Data.Unit
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe hiding (_>>=_)
open import Data.String hiding (length;show)
open import Data.Nat.Show


open import Simple-Model.ledgerversion.Ledger-Simple-Model
open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel

open import Data.Nat.Show
open import interface.Console hiding (main)
open import interface.Unit
open import interface.NativeIO
open import interface.Base
open import Data.Maybe.Base as Maybe using (Maybe; nothing; _<∣>_; when)
import Data.Maybe.Effectful
open import interface.ConsoleLib



-- string to function name
string2FunctionName : String → Maybe FunctionName
string2FunctionName str =  if str  == "counter"   then just "counter"   else
                          (if str  == "increment" then just "increment" else
                          (if str  == "transfer"  then just "transfer"  else
                          nothing))
                          
-- define a function to convert error message to string
errorMsg2Str : ErrorMsg → String
errorMsg2Str (strErr s)  = s
errorMsg2Str (numErr n)  = show n
errorMsg2Str undefined   = "undefined"

mutual

-- first program to execute a function of a contract
  executeLedger      : ∀{i} → Ledger → (callAddr : Address) → IOConsole i Unit
  executeLedger ledger callAddr .force
      = exec' (putStrLn "Enter the calling address")
        λ _ → IOexec getLine 
        λ line → executeLedgerStep2 ledger callAddr (readMaybe 10 line)

  executeLedgerStep2 : ∀{i} → Ledger → (callAddr : Address) → Maybe ℕ → IOConsole i Unit
  executeLedgerStep2 ledger callAddr nothing .force
                   = exec' (putStrLn "Enter the calling cddress")
                     λ _ → IOexec getLine
                     λ _ →  executeLedger ledger callAddr
  executeLedgerStep2 ledger callAddr (just n) .force
   = exec' (putStrLn "Enter the function name (e.g. counter, increment, transfer)")
     λ _ → IOexec getLine 
     λ line → executeLedgerStep3 ledger callAddr n line

  
  executeLedgerStep3 : ∀{i} → Ledger → (callAddr : Address) → ℕ → FunctionName → IOConsole i Unit
  executeLedgerStep3 ledger callAddr n f .force
   = exec' (putStrLn "Enter the argument of the function as a natural number")
     λ _ → IOexec getLine
     λ line → executeLedgerStep4 ledger callAddr n f (readMaybe 10 line)
     
  
  executeLedgerStep4 : ∀{i} → Ledger → (callAddr : Address) → ℕ → FunctionName → Maybe ℕ → IOConsole i Unit
  executeLedgerStep4 ledger callAddr n f nothing .force
   = exec' (putStrLn "Please enter a natural number")
     λ _ → executeLedgerStep3 ledger callAddr  n f

  executeLedgerStep4 ledger callAddr n f (just m) .force
   = executeLedgerStep5 (evaluateNonTerminatingWithLedger
     ledger callAddr n f (nat m)) callAddr

  
  executeLedgerStep5 : ∀{i} → MsgAndLedger → (callAddr : Address) → IO' consoleI i Unit
  executeLedgerStep5 (msgAndLedger newLedger (theMsg (nat n))) callAddr
    = exec' (putStrLn ("The result of execution is nat " ++ (show n)))
      λ _ → mainBody newLedger callAddr
  executeLedgerStep5 (msgAndLedger newLedger (theMsg (list l))) callAddr
    = exec' (putStrLn "The result of execution is of the form list l ")
      λ _ → mainBody newLedger callAddr
  executeLedgerStep5 (msgAndLedger newLedger (err e)) callAddr
    = exec' (putStrLn "Error")
      λ _ → IOexec (putStrLn (errorMsg2Str e))
      λ _ → mainBody newLedger callAddr



-- Second program to look up the balance of one contract
  executeLedgercheckamount    : ∀{i} → Ledger → (callAddr : Address) → IOConsole i Unit                              
  executeLedgercheckamount ledger callAddr .force
   = exec' (putStrLn "Enter the address of the contract you want to look up the balance")
     λ _ → IOexec getLine 
     λ line → executeLedgercheckamountAux ledger callAddr (readMaybe 10 line)


  executeLedgercheckamountAux : ∀{i} → Ledger  → (callAddr : Address) → Maybe ℕ → IOConsole i Unit
  executeLedgercheckamountAux ledger callAddr nothing .force
   = exec' (putStrLn "Please enter a natural number")
     λ _ → executeLedgercheckamount ledger callAddr
  executeLedgercheckamountAux ledger callAddr (just calledAddr) .force
   = exec' (putStrLn
            ("The available money is " ++ show (ledger calledAddr .amount)
             ++ " wei in address " ++ show calledAddr))
     λ line → mainBody ledger callAddr



--- third program to change the calling address
  executeLedgerChangeCallingAddress : ∀{i} → Ledger → (callAddr : Address) → IOConsole i Unit
  executeLedgerChangeCallingAddress ledger callAddr .force
   = exec' (putStrLn "Enter the new calling address")
     λ _ → IOexec getLine
     λ line → executeLedgerChangeCallingAddressAux ledger callAddr (readMaybe 10 line)


  executeLedgerChangeCallingAddressAux : ∀{i} → Ledger → (callAddr : Address) → Maybe Address → IOConsole i Unit
  executeLedgerChangeCallingAddressAux ledger callAddr (just callingAddr)
      = executeLedger ledger callAddr
  executeLedgerChangeCallingAddressAux ledger callAddr nothing .force
      = exec' (putStrLn "Please enter a number")
      λ _ → executeLedgerChangeCallingAddress ledger callAddr




-- define our interface  
  mainBody : ∀{i} → Ledger → (callAddr : Address) → IOConsole i  Unit
  mainBody ledger callAddr .force
    =  WriteString'
       "Please choose one of the following options:
             1- Execute a function of a contract.
             2- Look up the balance of a contract.
             3- Change the calling address.
             4- Terminate the program." λ _ → 
      (GetLine >>= λ str →
      if str       == "1"  then executeLedger ledger callAddr
      else (if str == "2"  then executeLedgercheckamount ledger callAddr
      else (if str == "3"  then executeLedgerChangeCallingAddress ledger callAddr
      else (if str == "4"  then WriteString "The program will be terminated"
      else WriteStringWithCont "Please enter 1,2,3 or 4"
      λ _ → mainBody ledger callAddr))))

-- The main function is defined in the example files e.g.
-- Agdacode/agda/Simple-Model/IOledger/IOledger-counter.agda

