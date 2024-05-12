--@PREFIX@SizedIOBase
{-# OPTIONS --sized-types --guardedness #-}
module interface.ConsoleLib where

open import interface.NativeIO public
open import interface.Console public  hiding (main) renaming (translateIOConsole to run)
open import Size
open import interface.Base
open import Data.List

-- begin modification of ooAgda library  (replacing ∞ by a hidden parameter i)
WriteString : ∀{i} →  (s : String) → IOConsole i Unit
WriteString s = Exec (putStrLn s)

WriteStringWithCont : ∀{i} →  (s : String) → (Unit → IO consoleI i Unit) → IOConsole i Unit
WriteStringWithCont s cont .force = exec' (putStrLn s) cont
-- end modification of ooAgda library

-- addition to the ooAgda library
WriteString' : ∀{i} → (s : String) → (Unit → IO consoleI i Unit) → IOConsole' i Unit
WriteString' s  = exec' (putStrLn s)
--end addition to the ooAgda library



GetLine : IOConsole ∞ String
GetLine = Exec getLine

ConsoleProg : Set
ConsoleProg = NativeIO Unit
