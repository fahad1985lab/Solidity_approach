--{-# OPTIONS --sized-types --guardedness #-}

module interface.Interface where



open import interface.NativeIO
open import Data.Nat
open import Data.Product
--open import ledger
open import Data.Maybe
open import Agda.Builtin.String




record IOInterfaceMsg  : Set where
  coinductive
  field
    Command   : ℕ × ℕ × Msg → IOInterfaceMsg --Set
    Response  : IOInterfaceMsg





data ConsoleCommand : Set where
  getline   : ConsoleCommand
  putString : String → ConsoleCommand



--ConsoleResponse :  IOInterfaceMsg  → Set

{- (Command x) = {!!}
ConsoleResponse Response    = {!!}
--ConsoleResponse Response    = Maybe Msg
-}


-- open IOInterface public

{-
ConsoleResponse :  IOMsg  → Set
ConsoleResponse (command x) = Msg
ConsoleResponse Response    = Maybe Msg

-}

{-
consoleI : IOMsg
consoleI = {!!}
-}




{-
main : NativeIO Unit
main = nativePutStrLn "Console"
-}



