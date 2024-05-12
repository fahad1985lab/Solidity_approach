module libraries.boolLib where

open import Data.Empty
open import Data.Unit
open import Data.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open import libraries.logic
open import libraries.emptyLib

--define aton
atom : Bool → Set
atom true = ⊤
atom false = ⊥


atomLemFalse : (b : Bool) -> b ≡ false -> ¬  (atom b)
atomLemFalse false refl ()

atomLemTrue : (b : Bool) -> b ≡ true -> atom b
atomLemTrue true refl  =  tt


atomToEq : {b : Bool} -> atom b -> b ≡ true
atomToEq {true} p = refl

¬atomToEq : {b : Bool} -> ¬ (atom b) -> b ≡ false
¬atomToEq {false} p = refl
¬atomToEq {true} p = efq (p tt)
