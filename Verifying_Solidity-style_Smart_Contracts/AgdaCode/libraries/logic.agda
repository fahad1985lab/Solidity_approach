
module libraries.logic  where

open import Data.Bool hiding (_∧_ ; _∨_)
open import Data.Empty


data _∧_ (A B : Set) : Set where
  and : A -> B -> A ∧ B



data _∨_ (A B : Set) : Set where
  or₁ : A → A ∨ B
  or₂ : B → A ∨ B

¬ : Set → Set
¬ A = A → ⊥


