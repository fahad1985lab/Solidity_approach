
open import constantparameters

module Complex-Model.IOledger.IOledgerReentrancyAttack where


open import Data.Nat
open import Data.List hiding (reverse) renaming (_++_ to _++lstr_)
open import Agda.Builtin.Nat using (_-_; _*_)
open import Data.Unit
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe hiding (_>>=_)
open import Data.String hiding (length;show)
open import Data.Nat.Show
open import interface.Console hiding (main)
open import interface.Unit
open import interface.NativeIO
open import interface.Base
open import Data.Maybe.Base as Maybe using (Maybe; nothing; _<∣>_; when)
open import Data.Maybe.Effectful
open import Data.Product renaming (_,_ to _,,_ )
open import Agda.Builtin.String


-- our work
open import interface.ConsoleLib
open import libraries.natCompare
open import libraries.IOlibrary-new-version
open import libraries.Mainlibrary-new-version
open import basicDataStructure
open import Complex-Model.ledgerversion.Ledger-Complex-Model-with-reentrancy-attack exampleParameters
open import Complex-Model.ledgerversion.Ledger-Complex-Model-improved-non-terminate exampleParameters


msg2ℕ : Msg → ℕ
msg2ℕ (nat n)         = n
msg2ℕ otherwise       = 0



initialfun2Str : MsgOrError → String
initialfun2Str (theMsg (nat n₁)) = "(theMsg " ++ show n₁ ++ ")"
initialfun2Str (theMsg othermsg) = " The message is not a number "
initialfun2Str (err x) = " The message is not a number "


reverse : List String → List String
reverse []       = []
reverse (x ∷ ls) = reverse ls ++lstr (x ∷ []) --{!!}

listsreting2string : List String → String
listsreting2string [] = ""
listsreting2string (x ∷ l)  = x ++ "\n" ++ listsreting2string l




mutual

  executeLedger : ∀{i} → StateIO → IOConsole i Unit
  executeLedger stIO .force =
                             exec' (putStrLn "Enter the called address as a natural number")
                             λ _ → IOexec getLine  λ line →
                            executeLedgerStep1-2 stIO (readMaybe 10 line)



  executeLedgerStep1-2 : ∀{i} → StateIO → Maybe ℕ → IOConsole i Unit
  executeLedgerStep1-2 stIO (just calledAddr) .force =
                                        exec' (putStrLn "Enter the function name")
                                         λ _ → IOexec getLine
                                         λ line → executeLedgerStep1-3 stIO calledAddr line
  executeLedgerStep1-2 stIO nothing .force =
                                          exec' (putStrLn "Please enter an address as a natural number")
                                          λ _ → executeLedger stIO


  executeLedgerStep1-3 : ∀{i} → StateIO → ℕ → FunctionName → IOConsole i Unit
  executeLedgerStep1-3 stIO calledAddr f .force =
                                                exec' (putStrLn "Enter the argument of the function name as a natural number")
                                                λ _ → IOexec getLine  λ line →
                                                executeLedgerStep1-4 stIO calledAddr f (readMaybe 10 line)

  
  executeLedgerStep1-4 : ∀{i} → StateIO → ℕ → FunctionName → Maybe ℕ → IOConsole i Unit
  executeLedgerStep1-4 ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩ calledAddr f (just m) .force
                     = exec' (putStrLn (" The result is as follows:  \n" ++
                       " \n The inital address is " ++ show initialAddr ++
                       " \n The called address is "  ++ show calledAddr ++
                       " \n The amount sent is " ++ show amountR ++ " wei")) λ _ → 
                       executeLedgerFinalStep 
                        (evaluateNonTerminatingfinalstep ledger initialAddr initialAddr calledAddr gas f (nat m)  amountR [])
                        ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩ 

  executeLedgerStep1-4 stIO calledAddr f nothing  .force
                                        = exec' (putStrLn "Enter the argument of the function name as a natural number")
                                        λ _ → executeLedgerStep1-3 stIO  calledAddr f

  executeLedgerFinalStep : ∀{i} →  Maybe (Ledger × MsgOrErrorWithGas) → StateIO  → IO consoleI i Unit 
  executeLedgerFinalStep (just (newledger ,, (theMsg ms , gas₁ gas, listevents)))
                         ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩ .force
                          = exec' (putStrLn (" The argument of the function name is " ++ msg2string (nat amountR)))
                     λ _ → IOexec (putStrLn (" The remaining gas is " ++ (show gas₁) ++ " wei"
                          ++ " and the gas used is " ++ (show (gas - gas₁)) ++ " wei"   
                          ++ " ,  \n The function returned " ++ initialfun2Str (theMsg ms)
                          ++ " , \n The list of events : \n" ++ listsreting2string (reverse listevents))) 
                     λ _ → mainBody (⟨ newledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩)
  executeLedgerFinalStep  (just (newledger ,, (err e ⟨ lastCallAddress >> curraddr ∙ lastfunname [ lastmsg ]∙ event ⟩ , gas₁ gas, listevents)))
                          ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩ .force
                          = exec' (putStrLn "Debug information")
                           λ _ → IOexec (putStrLn (errorMsg2Str (err e ⟨ lastCallAddress >> curraddr ∙ lastfunname [ lastmsg ]∙ listevents ⟩)))
                           λ _ → IOexec (putStrLn ("Address " ++ show lastCallAddress ++
                           " is trying to call the address " ++ show curraddr ++
                           " with Function Name " ++ funname2string lastfunname ++
                           " with Message " ++ msg2string lastmsg
                            ++ " , \n The list of events : \n" ++ listsreting2string (reverse listevents)))
                           λ _ → IOexec (putStrLn ("The remaining gas is " ++ show gas₁ ++ " wei"
                                                    ++ " and the gas used is " ++ (show (gas - gas₁))))
                           λ _ → mainBody (⟨ newledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩)

  executeLedgerFinalStep  (just (newledger ,, (invalidtransaction , gas₁ gas, listevents)))
                         ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩ .force
                          = exec' (putStrLn "Invalid transaction")
                             λ _ → IOexec (putStrLn (errorMsg2Str invalidtransaction))
                             λ _ → IOexec (putStrLn ("The remaining gas is " ++ (show gas₁) ++ " wei"
                               ++ " and the gas used is " ++ (show (gas - gas₁))))                     
                             λ _ → mainBody (⟨ newledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩)
  executeLedgerFinalStep  nothing ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩ .force
                          = exec' (putStrLn "Nothing and the ledger will change to old ledger")
                     λ _ → mainBody (⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩)


--To change calling address
  executeLedger-ChangeCallingAddress : ∀{i} → StateIO → IOConsole i Unit
  executeLedger-ChangeCallingAddress stIO .force
                    = exec' (putStrLn "Enter a new calling address as a natural number")
                      λ _ → IOexec getLine
                      λ line →  executeLedger-ChangeCallingAddressAux stIO (readMaybe 10 line)

  executeLedger-ChangeCallingAddressAux  : ∀{i} → StateIO → Maybe Address → IOConsole i Unit
  executeLedger-ChangeCallingAddressAux ⟨ ledger₁ ledger, initialAddr₁ initialAddr, gas₁ gas, amountR amountR⟩ (just callingAddr)
            = executeLedger ⟨ ledger₁ ledger, callingAddr initialAddr, gas₁ gas, amountR amountR⟩
  executeLedger-ChangeCallingAddressAux stIO nothing .force = exec' (putStrLn "Please enter the calling address as a natural number")
                                        λ _ → executeLedger-ChangeCallingAddress stIO



-- To update the amount sent
  executeLedger-updateAmountReceive : ∀{i} → StateIO → IOConsole i Unit
  executeLedger-updateAmountReceive stIO .force = exec' (putStrLn "Enter the new amount to be sent as a natural number")
                                         λ _ → IOexec getLine  λ line →
                                         executeLedgerStep-updateAmountReceiveAux stIO (readMaybe 10 line)


  executeLedgerStep-updateAmountReceiveAux : ∀{i} → StateIO → Maybe ℕ → IOConsole i Unit  
  executeLedgerStep-updateAmountReceiveAux stIO  nothing .force = exec' (putStrLn "Please enter the amount to be sent as a natural number")
                                                      λ _ → executeLedger-updateAmountReceive stIO

  executeLedgerStep-updateAmountReceiveAux ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩  (just amountrecive) .force
                   = exec' (putStrLn ("The amount to be sent has been updated successfully. \n The new amount to be sent is  " ++ show amountrecive ++ " wei"
                    ++ "\n and the old amount to be sent was " ++ show amountR ++ " wei" ))
                    λ line → mainBody ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountrecive amountR⟩

-- To check the amount recive
  executeLedger-checkAmountReceive : ∀{i} → StateIO → IOConsole i Unit
  executeLedger-checkAmountReceive ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩  .force
                   = exec' (putStrLn (" The amount sent is "  ++ show amountR ++ " wei" ))
                           λ line → mainBody ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩



--- To check the balance for ecah contract
  executeLedger-CheckBalance : ∀{i} → StateIO → IOConsole i Unit
  executeLedger-CheckBalance stIO .force = exec' (putStrLn "Enter the called address as a natural number")
                                           λ _ → IOexec getLine  λ line →
                                            executeLedgerStep-CheckBalanceAux stIO (readMaybe 10 line)

  executeLedgerStep-CheckBalanceAux  : ∀{i} → StateIO → Maybe ℕ → IOConsole i Unit
  executeLedgerStep-CheckBalanceAux stIO nothing .force = exec' (putStrLn "Please enter an address as a natural number")
                                                           λ _ → IOexec getLine
                                                           λ _ → executeLedger-CheckBalance stIO

  executeLedgerStep-CheckBalanceAux ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩ (just calledAddr) .force
                                       = exec' (putStrLn "The information you get is below:  ")
                                       λ line → IOexec (putStrLn ("The available money is " ++ show (ledger calledAddr .amount)
                                         ++ " wei in address " ++ show calledAddr))
                                       (λ line → mainBody (⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩))



-- To update the gas
  executeLedger-updateGas  : ∀{i} → StateIO → IOConsole i Unit
  executeLedger-updateGas stIO .force = exec' (putStrLn "Enter the new gas amount as a natural number")
                                         λ _ → IOexec getLine  λ line →
                                         executeLedgerStep-updateGasAux stIO (readMaybe 10 line)

  executeLedgerStep-updateGasAux  : ∀{i} → StateIO → Maybe ℕ → IOConsole i Unit

  executeLedgerStep-updateGasAux stIO  nothing .force = exec' (putStrLn "Please enter a gas as a natural number")
                                                      λ _ → executeLedger-updateGas stIO

  executeLedgerStep-updateGasAux ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩  (just gass) .force
                   = exec' (putStrLn ("The gas amount has been updated successfully. \n The new gas amount is  " ++ show gass ++ " wei"
                    ++ " and the old gas amount is " ++ show gas ++ " wei" ))
                    λ line → mainBody ⟨ ledger ledger, initialAddr initialAddr, gass gas, amountR amountR⟩



-- To check the gas available
  executeLedger-checkGas : ∀{i} → StateIO → IOConsole i Unit
  executeLedger-checkGas ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩  .force
                   = exec' (putStrLn (" The gas limit is "  ++ show gas ++ " wei" ))
                           λ line → mainBody ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩




----To check the view function
  executeLedger-viewfunction1  : ∀{i}  → StateIO → IOConsole i Unit
  executeLedger-viewfunction1 stIO .force =
                             exec' (putStrLn "Enter the Called Address as a natural number")
                             λ _ → IOexec getLine λ line →
                            executeLedger-viewfunStep1-2 stIO (readMaybe 10 line)


  
  executeLedger-viewfunStep1-2 : ∀{i} → StateIO → Maybe Address → IOConsole i Unit
  executeLedger-viewfunStep1-2 stIO (just calledAddr) .force =
                             exec' (putStrLn "Enter the Function name")
                             λ _ → IOexec getLine λ line →
                             executeLedger-viewfunStep1-3 stIO calledAddr (string2FunctionName line)
  executeLedger-viewfunStep1-2 stIO nothing .force =
                                          exec' (putStrLn "Please enter an address as a natural number")
                                          λ _ → executeLedger-viewfunction1 stIO



  executeLedger-viewfunStep1-3 : ∀{i} → StateIO → (calledAddr : Address) → Maybe FunctionName → IOConsole i Unit
  executeLedger-viewfunStep1-3 stIO calledAddr (just f) .force =
                                                    exec' (putStrLn "Enter the argument of the function name as a natural number")
                                                     λ _ → IOexec getLine λ line →
                                                     executeLedger-viewfunStep1-4 stIO calledAddr f (readMaybe 10 line)
  executeLedger-viewfunStep1-3 stIO calledAddr nothing  .force =
                                                        exec' (putStrLn "Please enter a functionname as string")
                                                        λ _ → executeLedger-viewfunStep1-2 stIO (just calledAddr)


  executeLedger-viewfunStep1-4 : ∀{i} → StateIO → (calledAddr : Address) → FunctionName → Maybe ℕ → IOConsole i Unit
  executeLedger-viewfunStep1-4 ⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩ calledAddr f (just m) .force
                                    = exec' (putStrLn "The information you get is below:  ")
                                    λ _ → IOexec (putStrLn ("The inital address  = " ++ show initialAddr ++
                                    " ,  The called address = "  ++ show calledAddr ++
                                    " The view function returns " ++ initialfun2Str (ledger calledAddr .viewFunction f (nat m)) ++
                                    "\n The view function cost returns " ++ show (ledger calledAddr .viewFunctionCost f (nat m))))
                                    λ _ →  mainBody (⟨ ledger ledger, initialAddr initialAddr, gas gas, amountR amountR⟩)
  executeLedger-viewfunStep1-4 stIO calledAddr f nothing  .force
                                        = exec' (putStrLn "Please enter the argument of the function name as a natural number") λ _ →
                                          executeLedger-viewfunStep1-3 stIO  calledAddr (just f)


-- main menu
  mainBody : ∀{i} → StateIO → IOConsole i Unit
  mainBody stIO .force
    = WriteString'
   ("Please choose one of the following:
      1- Execute a function of a contract.
      2- Execute a function with new calling address.
      3- Update the amount sent in function call.
      4- Check the amount sent in function call.
      5- Look up the amount of a contract.
      6- Update the gas limit.
      7- Check the gas limit.
      8- Evaluate a view function.
      9- Terminate the program.")  λ _ →
     GetLine >>= λ str →
     if         str == "1" then  executeLedger stIO
     else  (if  str == "2" then  executeLedger-ChangeCallingAddress stIO
     else  (if  str == "3" then  executeLedger-updateAmountReceive stIO
     else  (if  str == "4" then  executeLedger-checkAmountReceive stIO
     else  (if  str == "5" then  executeLedger-CheckBalance stIO
     else  (if  str == "6" then  executeLedger-updateGas stIO
     else  (if  str == "7" then  executeLedger-checkGas stIO
     else  (if  str == "8" then  executeLedger-viewfunction1 stIO
     else  (if  str == "9" then  WriteString "The program will be terminated"
     else  WriteStringWithCont  "Please enter a number 1 - 9"
        λ _ →  mainBody stIO ))))))))


-- The main function is defined in the example files e.g.
-- Complex-Model.example/reentrancy-attack/reentrancy-attack.agda
