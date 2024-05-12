module libraries.emptyLib  where

open import Data.Empty


empty : {A : Set} → ⊥ → A
empty ()

efq : {A : Set} → ⊥ → A
efq = empty
