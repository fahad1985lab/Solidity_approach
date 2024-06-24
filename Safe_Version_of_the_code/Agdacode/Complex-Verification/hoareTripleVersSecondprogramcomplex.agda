{-# OPTIONS --no-sized-types --safe #-}
open import constantparameters

module Complex-Verification.hoareTripleVersSecondprogramcomplex (param : ConstantParameters) where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_;and)
open import Data.Sum
open import Data.Maybe
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ {-; if_then_else_ -}) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality

--our work
open import Complex-Model.ledgerversion.Ledger-Complex-Model param 
open import Complex-Model.ccomand.ccommands-cresponse  
open import basicDataStructure
open import libraries.natCompare
open import libraries.Mainlibrary
open import libraries.boolLib
open import libraries.hoareTripleLibComplex param 
open import libraries.logic
open import libraries.emptyLib



--second progran
--transfer 10 from address 0 to address 6
transferSec-Prog : RemainingProgram
transferSec-Prog .prog =
   exec (getAmountc 0)
   (λ gasused → 1)
   λ amount →
   if 10 ≦b amount 
   then exec (transferc 10 6)
   (λ gasused → 1)
   (λ _ → return 1 (nat 0))
   else return 1 (nat 0) 
transferSec-Prog .stack          = []
transferSec-Prog .calledAddress  = 0
transferSec-Prog .gasUsed        = 100
transferSec-Prog .funName        = "f"
transferSec-Prog .msg            = nat 0


--define postcondition 
PostTransfer : HLPred
PostTransfer (stateEF led initialAddress callingAddress)
  = (10 ≦r led 6 .amount) ∧
  ((initialAddress ≡ 0) ∧
  (callingAddress ≡ 0))


--define precondition
PreTransfer : HLPred
PreTransfer (stateEF led initialAddress callingAddress)
    = ((10 ≦r led 0 .amount ) ∨
       (10 ≦r led 6 .amount))
     ∧ ((initialAddress ≡ 0)
     ∧ (callingAddress ≡ 0))





-- first direction (forward direction)
proofatom10<=bledger6amount : (led ledger : Ledger)(msg : Msg)(initialAddress callingAddress : ℕ)(x : atom (10 ≦b led 6 .amount))
                     → (x₂     : EFrel led
                        (executeTransferAux led led [] 0 0 0 (return 1 (nat 0)) 100 "f"
                        (nat 0) 10 6 (compareLeq 10 (led 0 .amount)))
                        (stateEF ledger [] initialAddress callingAddress 0
                        (return 1 msg) 100 "f" (nat 0)))
                    → atom (10 ≦b ledger 6 .amount)
proofatom10<=bledger6amount led ledger msg initialAddress callingAddress x x₂  with compareLeq 10 (led 0 .amount)
proofatom10<=bledger6amount led .(updateLedgerAmount led 0 6 10 x₁) msg .0 .0 x (reflex .(stateEF (updateLedgerAmount led 0 6 10 x₁) [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0))) | leq x₁
                            = atomN<=bM+N 10 (led 6 .amount)
proofatom10<=bledger6amount led ledger msg initialAddress callingAddress x (step () x₃) | greater x₁


proofinitialAddress≡0Leq1 : (led1 led2 : Ledger)(msg : Msg)(initialAddress callingAddress : ℕ)(x : atom (10 ≦b led1 6 .amount))
                (x₂ : EFrel led1
         (executeTransferAux led1 led1 [] 0 0 0 (return 1 (nat 0)) 100 "f"
          (nat 0) 10 6 (compareLeq 10 (led1 0 .amount)))
         (stateEF led2 [] initialAddress callingAddress 0
          (return 1 msg) 100 "f" (nat 0)))
                → initialAddress ≡ 0      
proofinitialAddress≡0Leq1 led1 led2 msg initialAddress callingAddress x x₂ with compareLeq 10 (led1 0 .amount)
proofinitialAddress≡0Leq1 led1 .(updateLedgerAmount led1 0 6 10 x₁) msg .0 .0 x (reflex .(stateEF (updateLedgerAmount led1 0 6 10 x₁) [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0))) | leq x₁ = refl
proofinitialAddress≡0Leq1 led1 led2 msg initialAddress callingAddress x (step () x₃) | greater x₁



proofcallingAddress≡0Leq1 : (led1 led2 : Ledger)(msg : Msg)(initialAddress callingAddress : ℕ)(x : atom (10 ≦b led1 6 .amount))
                (x₂ : EFrel led1
         (executeTransferAux led1 led1 [] 0 0 0 (return 1 (nat 0)) 100 "f"
          (nat 0) 10 6 (compareLeq 10 (led1 0 .amount)))
         (stateEF led2 [] initialAddress callingAddress 0
          (return 1 msg) 100 "f" (nat 0)))
                → callingAddress ≡ 0      
proofcallingAddress≡0Leq1 led1 led2 msg initialAddress callingAddress x x₂ with compareLeq 10 (led1 0 .amount)
proofcallingAddress≡0Leq1 led1 .(updateLedgerAmount led1 0 6 10 x₁) msg .0 .0 x (reflex .(stateEF (updateLedgerAmount led1 0 6 10 x₁) [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0))) | leq x₁ = refl
proofcallingAddress≡0Leq1 led1 led2 msg initialAddress callingAddress x (step () x₃) | greater x₁




proofPreTransfer-precondAux1 : (led : Ledger)(s' : HLState)(msg : Msg)(eq1   : (10 ≦b led 0 .amount) ≡ true)
                              (x₂ : EFrel led
                               (stateEF (updateLedgerAmount led 0 6 10 (transfer≡r atom eq1 tt))
                                        [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0))
                               (stateEF (ledger s') [] (initialAddress s') (callingAddress s') 0
                                        (return 1 msg) 100 "f" (nat 0)))
                              → atom (10 ≦b ledger s' 6 .amount)
proofPreTransfer-precondAux1 led (stateEF .(updateLedgerAmount led 0 6 10 (transfer≡r atom eq1 tt)) .0 .0) msg eq1
                                          (reflex .(stateEF (updateLedgerAmount led 0 6 10 (transfer≡r atom eq1 tt)) [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0)))
                                          = atomN<=bM+N 10 (led 6 .amount)


--prove first direction (forward direction) for precondition
proofPreTransfer-precond : < PreTransfer >solprecomplexmodel transferSec-Prog < PostTransfer >
proofPreTransfer-precond (stateEF led .0 .0) s' msg (and (or₁ x) (and refl refl)) (step tt x₂) with 10 ≦b led 0 .amount in eq1
proofPreTransfer-precond (stateEF led _ _) s' msg (and (or₁ tt) (and refl refl)) (step tt (step tt x₂)) | true rewrite compareleq3 10 (led 0 .amount) eq1
                          = and (proofPreTransfer-precondAux1 led s' msg  eq1 x₂) (and (efrelLeminitialAddr' x₂) (efrelLemCallingAddr' x₂)) 
proofPreTransfer-precond (stateEF led .0 .0) s' msg (and (or₂ x) (and refl refl)) (step tt x₂) with 10 ≦b led 0 .amount
proofPreTransfer-precond (stateEF led _ _) (stateEF .led .0 .0) msg (and (or₂ x) (and refl refl)) (step tt (reflex .(stateEF led [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0)))) | false
                          = and x (and refl refl)
proofPreTransfer-precond (stateEF led _ _) (stateEF ledger initialAddress callingAddress) msg (and (or₂ x) (and refl refl)) (step tt (step tt x₂)) | true
                          = and ((proofatom10<=bledger6amount led ledger msg initialAddress callingAddress x x₂))
                           (and (proofinitialAddress≡0Leq1 led ledger msg initialAddress callingAddress x x₂)
                                (proofcallingAddress≡0Leq1 led ledger msg initialAddress callingAddress x x₂))
      



---- second direction (backward direction)
proof⊤OrAtom10<=led6amount : (led1 led2 : Ledger)(msg : Msg)(initialAddress callingAddress : ℕ)
         → (x₂    : EFrel led1
        (executeTransferAux led1 led1 [] initialAddress callingAddress 0
         (return 1 (nat 0)) 100 "f" (nat 0) 10 6
         (compareLeq 10 (led1 0 .amount)))
        (stateEF led2 [] 0 0 0 (return 1 msg) 100 "f" (nat 0)))
        → (⊤ ∨ atom (10 ≦b led1 6 .amount)) ∧
      ((initialAddress ≡ 0) ∧ (callingAddress ≡ 0))
proof⊤OrAtom10<=led6amount led1 led2 msg initialAddress callingAddress x₂ with compareLeq 10 (led1 0 .amount)
proof⊤OrAtom10<=led6amount led1 .(updateLedgerAmount led1 0 6 10 x) msg .0 .0 (reflex .(stateEF (updateLedgerAmount led1 0 6 10 x) [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0))) | leq x
        = and (or₁ tt) (and refl refl)
proof⊤OrAtom10<=led6amount led1 led2 msg initialAddress callingAddress (step () x₂) | greater x



proofinitialAddress≡0 : (led1 led2 : Ledger)(msg : Msg)(initialAddress₁ callingAddress₁ : ℕ)(eq1 : (10 ≦b led2 0 .amount) ≡ false)
                     → (x  : atom (10 ≦b led2 6 .amount))
                     → (x₂    : EFrel led1
                        (stateEF led1 [] initialAddress₁ callingAddress₁ 0
                                 (exec (transferc 10 6) (λ gasused → 1) (λ _ → return 1 (nat 0))) 100 "f" (nat 0))
                        (stateEF led2 [] 0 0 0 (return 1 msg) 100 "f" (nat 0)))
                    → initialAddress₁ ≡ 0
proofinitialAddress≡0 led1 led2 msg initialAddress₁ callingAddress₁  eq1 x (step tt x₂) with compareLeq 10 (led1 0 .amount)
proofinitialAddress≡0 led1 .(updateLedgerAmount led1 0 6 10 x₁) msg .0 .0 eq1 x (step tt (reflex .(stateEF (updateLedgerAmount led1 0 6 10 x₁) [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0)))) | leq x₁
       = refl
proofinitialAddress≡0 led1 led2 msg initialAddress₁ callingAddress₁ eq1 x (step tt (step () x₃)) | greater x₁


proofcallingAddress≡0 : (led1 led2 : Ledger)(msg : Msg)(initialAddress₁ callingAddress₁ : ℕ)(eq1 : (10 ≦b led2 0 .amount) ≡ false)
                     → (x  : atom (10 ≦b led2 6 .amount))
                     → (x₂ : EFrel led1
                           (stateEF led1 [] initialAddress₁ callingAddress₁ 0
                              (exec (transferc 10 6) (λ gasused → 1) (λ _ → return 1 (nat 0))) 100 "f" (nat 0))
                           (stateEF led2 [] 0 0 0 (return 1 msg) 100 "f" (nat 0)))

                    → callingAddress₁ ≡ 0
proofcallingAddress≡0 led1 led2 msg initialAddress₁ callingAddress₁ eq1 x (step tt x₂) with compareLeq 10 (led1 0 .amount)
proofcallingAddress≡0 led1 .(updateLedgerAmount led1 0 6 10 x₁) msg .0 .0 eq1 x (step tt (reflex .(stateEF (updateLedgerAmount led1 0 6 10 x₁) [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0)))) | leq x₁ = refl
proofcallingAddress≡0 led1 led2 msg initialAddress₁ callingAddress₁ eq1 x (step tt (step () x₃)) | greater x₁





--prove second direction (backward direction) for weakest precondition
proofPreTransfer-solweakest : < PreTransfer >solweakestcomplexmodel transferSec-Prog < PostTransfer >
proofPreTransfer-solweakest (stateEF led1 initialAddress₁ callingAddress₁) (stateEF led2 .0 .0) msg (and x (and refl refl)) (step tt x₂) with 10 ≦b led2 0 .amount in eq1
proofPreTransfer-solweakest (stateEF led1 initialAddress₁ callingAddress₁) (stateEF led2 _ _) msg (and x (and refl refl)) (step tt x₂) | false with 10 ≦b led1 0 .amount
proofPreTransfer-solweakest (stateEF led1 .0 .0) (stateEF .led1 _ _) msg (and x (and refl refl)) (step tt (reflex .(stateEF led1 [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0)))) | false | false
      = and (or₂ x) (and refl refl)
proofPreTransfer-solweakest (stateEF led1 initialAddress₁ callingAddress₁) (stateEF led2 _ _) msg (and x (and refl refl)) (step tt (step () x₂)) | false | false
proofPreTransfer-solweakest (stateEF led1 initialAddress₁ callingAddress₁) (stateEF led2 _ _) msg (and x (and refl refl)) (step tt x₂) | false | true
      = and (or₁ tt) (and
                     (proofinitialAddress≡0 led1 led2 msg initialAddress₁ callingAddress₁ eq1 x x₂)
                     (proofcallingAddress≡0 led1 led2 msg initialAddress₁ callingAddress₁ eq1 x x₂))
proofPreTransfer-solweakest (stateEF led1 initialAddress₁ callingAddress₁) (stateEF led2 _ _) msg (and x (and refl refl)) (step tt x₂) | true with 10 ≦b led1 0 .amount
proofPreTransfer-solweakest (stateEF led1 .0 .0) (stateEF .led1 _ _) msg (and x (and refl refl)) (step tt (reflex .(stateEF led1 [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0)))) | true | false
      = and (or₂ x) (and refl refl)
proofPreTransfer-solweakest (stateEF led1 initialAddress₁ callingAddress₁) (stateEF led2 _ _) msg (and x (and refl refl)) (step tt (step tt x₂)) | true | true
      = proof⊤OrAtom10<=led6amount led1 led2 msg initialAddress₁ callingAddress₁ x₂





--prove both directions for hoare tripl
proofTransfer : < PreTransfer >sol transferSec-Prog < PostTransfer >
proofTransfer  .precond  = proofPreTransfer-precond 
proofTransfer  .weakest  = proofPreTransfer-solweakest
