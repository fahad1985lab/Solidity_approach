module libraries.naturalnumber  where


--open import Data.Nat  hiding (_≤_ ; _<_ )
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Empty
open import Data.Unit


--define natural number
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ


pred : ℕ → ℕ
pred (suc n) = n
pred zero = zero
