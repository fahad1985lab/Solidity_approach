{-# OPTIONS --sized-types --guardedness #-}
module interface.Console where

open import Level using () renaming (zero to lzero)
open import Size

open import interface.NativeIO
open import interface.Base



--data type of console command
data ConsoleCommand : Set where
  putStrLn  : String → ConsoleCommand
  getLine   : ConsoleCommand


--function of console command
ConsoleResponse : ConsoleCommand → Set
ConsoleResponse (putStrLn s)  = Unit
ConsoleResponse  getLine      = String


--function of consoleIO
consoleI : IOInterface
consoleI .Command   = ConsoleCommand
consoleI .Response  = ConsoleResponse

IOConsole : Size → Set → Set
IOConsole i = IO consoleI i

--addition to the ooAgda library
IOConsole' : Size → Set → Set
IOConsole' i = IO' consoleI i
--end to addition to the ooAgda library

IOConsole+ : Size → Set → Set
IOConsole+ i = IO+ consoleI i

translateIOConsoleLocal : (c : ConsoleCommand) → NativeIO (ConsoleResponse c)
translateIOConsoleLocal (putStrLn s) = nativePutStrLn s
translateIOConsoleLocal getLine      = nativeGetLine

translateIOConsole : {A : Set} → IOConsole ∞ A → NativeIO A
translateIOConsole = translateIO translateIOConsoleLocal

postulate translateIOConsoleTODO : {A : Set} → (i : Size) → IOConsole i A → NativeIO A


main : NativeIO Unit
main = nativePutStrLn "Console"
