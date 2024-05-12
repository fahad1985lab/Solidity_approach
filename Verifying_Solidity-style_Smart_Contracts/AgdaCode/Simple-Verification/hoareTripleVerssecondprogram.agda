module Simple-Verification.hoareTripleVerssecondprogram where

open import Data.Nat  hiding (_≥_) renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_;and)
open import Data.Sum
open import Data.Maybe
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ {-; if_then_else_-} ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≥_ ; _≤_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality

-- our work
open import Simple-Model.ledgerversion.Ledger-Simple-Model
open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel
open import libraries.natCompare
open import libraries.logic
open import libraries.hoareTripleLibSimple 
open import libraries.emptyLib
open import libraries.boolLib





--- Second program transfer 10 from address 0 to address 6  

--define second program
transferSec-Prog : RemainingProgram
transferSec-Prog .prog =
     exec (getAmountc 0)
     λ amount →
     if 10 ≦b amount 
     then exec (transferc 10 6)
     (λ _ → return (nat 0))
     else return (nat 0)
transferSec-Prog .stack = []
transferSec-Prog .calledAddress = 0


--define postcondition for second program
PostTransfer : HLPred
PostTransfer (stateEF led callingAddress)
 = (led 6 .amount ≡ 10) ∧ (callingAddress ≡ 0) 


--define precondition for second program
PreTransfer : HLPred
PreTransfer (stateEF led callingAddress)
       = (((led 6 .amount ≡ 0) ∧
         (10 ≦r led 0 .amount )) ∨
         ((led 6 .amount ≡ 10) ∧
         (¬ (10 ≦r led 0 .amount ))))
         ∧ (callingAddress ≡ 0)



----- first direction (forward direction)


proofPreTransferaux : (led1 : Ledger)(10≦led1-0amount : 10 ≦r led1 0 .amount)
                       (l : Ledger)(s'   : HLState)
                       (x  : led1 6 .amount ≡ 0)
                       (eq   : updateLedgerAmount led1 0 6 10 10≦led1-0amount ≡ HLState.ledger s')
          → HLState.ledger s' 6 .amount ≡ 10
proofPreTransferaux led1 10≦led1-0amount l s' x eq  rewrite sym eq | x = refl


proofPreTransferaux' : (led1 : Ledger)(10≦led1-0amount : 10 ≦r led1 0 .amount)
                       (l : Ledger)(s'   : HLState)
                       (x  : led1 6 .amount ≡ 0)
                       (eq   : updateLedgerAmount led1 0 6 10 10≦led1-0amount 6 .amount ≡ HLState.ledger s' 6 .amount)
          → HLState.ledger s' 6 .amount ≡ 10
proofPreTransferaux' led1 10≦led1-0amount l s' x eq   rewrite sym eq | x = refl


-- prove first direction (forward direction) for precondition
proofPreTransfer : < PreTransfer >solpresimplemodel transferSec-Prog < PostTransfer >
proofPreTransfer  (stateEF led1 .0) s' msg (and (or₁ (and x x₁)) refl) (step tt x₂) with 10 ≦b led1 0 .amount in eq1 
proofPreTransfer  (stateEF led1 _) s' msg (and (or₁ (and x tt)) refl) (step tt (step tt x₂)) | true  rewrite compareleq3 10 (led1 0 .amount) eq1
  = let
           eq2 : HLState.ledger s' ≡  updateLedgerAmount led1 0 6 10 (transfer≡r atom eq1 tt)
           eq2 = efrelLemLedger' x₂

           eq2b : HLState.ledger s' 6 .amount  ≡  updateLedgerAmount led1 0 6 10 (transfer≡r atom eq1 tt) 6 .amount
           eq2b = cong'  (λ x → x 6 .amount) eq2

           eq3 : updateLedgerAmount led1 0 6 10 (transfer≡r atom eq1 tt) 6 .amount ≡ led1 6 .amount + 10
           eq3 = updateLedgerAmountLem1 led1 0 6 10 (λ {() }) (atomLemTrue (10 ≦b led1 0 .amount) eq1)

           eq4 : HLState.ledger s' 6 .amount ≡ led1 6 .amount + 10
           eq4 = trans≡ eq2b eq3
           
       in and (proofPreTransferaux' led1 (compareleq2 10 (led1 0 .amount) eq1) led1 s' x (sym≡ eq4)) (efrelLemCallingAddr' x₂)
       
proofPreTransfer  (stateEF led1 .0) s' msg (and (or₂ (and x x₃)) refl) (step tt x₂) with 10 ≦b led1 0 .amount
proofPreTransfer  (stateEF led1 _) (stateEF .led1 .0) msg (and (or₂ (and x x₃)) refl) (step tt (reflex .(stateEF led1 [] 0 0 (return (nat 0))))) | false = and x refl
proofPreTransfer  (stateEF led1 _) s' msg (and (or₂ (and x x₃)) refl) (step tt (step tt x₂)) | true with (x₃ tt)
... | ()






--- second direction (backward direction)


proofled1-6-amount+10≡10 : (led1 led2 : Ledger) (msg : Msg) → (callingAddress : ℕ)(x : led2 6 .amount ≡ 10)
                           (eq1  : (10 ≦b led1 0 .amount) ≡ true)
                           (p : EFrel led1 (stateEF (updateLedgerAmount led1 0 6 10 (transfer≡r atom eq1 tt))
                                [] callingAddress 0 (return (nat 0)))
                                (stateEF led2 [] 0 0 (return msg)))
                           → led1 6 .amount + 10 ≡ 10             
proofled1-6-amount+10≡10 led1 .(updateLedgerAmount led1 0 6 10 (transfer≡r atom eq1 tt)) msg .0 x eq1
        (reflex .(stateEF (updateLedgerAmount led1 0 6 10 (transfer≡r atom eq1 tt)) [] 0 0 (return (nat 0))))
        = x



proofPreTransfer-solweakstaux : (led1 led2 : Ledger) (msg : Msg) → (callingAddress : ℕ)(x : led2 6 .amount ≡ 10)
                           (eq1  : (10 ≦b led1 0 .amount) ≡ true)
                           (p    : EFrel led1 (executeTransferAux led1 led1 [] callingAddress 0 10 6
                           (return (nat 0)) (compareLeq 10 (led1 0 .amount)))
                           (stateEF led2 [] 0 0 (return msg)))
                           → (((led1 6 .amount ≡ 0) ∧ ⊤) ∨ ((led1 6 .amount ≡ 10) ∧ (⊤ → ⊥))) ∧ (callingAddress ≡ 0)
proofPreTransfer-solweakstaux  led1 led2 msg callingAddress x eq1 p rewrite (compareleq3 10 (led1 0 .amount) eq1)
      = let
           eq1a : callingAddress ≡ 0 
           eq1a = efrelLemCallingAddr p 

           eq2a : updateLedgerAmount led1 0 6 10 (transfer≡r atom eq1 tt) 6 .amount ≡ 10 
           eq2a = proofled1-6-amount+10≡10  led1 led2 msg callingAddress x eq1 p
                      
           eq3a : led1 6 .amount + 10  ≡ 10
           eq3a = eq2a
           
           eq4a : led1 6 .amount ≡ 0 
           eq4a = 0+lem= (led1 6 .amount) 10 eq3a 
           
       in and (or₁ (and eq4a tt)) eq1a
     

-- second direction
-- prove second direction (backward direction) for weakestprecondition
proofPreTransfer-solweakest : < PreTransfer >solweakestsimplemodel transferSec-Prog < PostTransfer >
proofPreTransfer-solweakest (stateEF led1 callingAddress) (stateEF led2 .0) msg (and x refl) (step tt x₂) with 10 ≦b led1 0 .amount in eq1
proofPreTransfer-solweakest  (stateEF led1 .0) (stateEF .led1 _) msg (and x refl) (step tt (reflex .(stateEF led1 [] 0 0 (return (nat 0))))) | false
                              = and (or₂ (and x (λ x₁ → x₁))) refl
proofPreTransfer-solweakest  (stateEF led1 callingAddress) (stateEF led2 _) msg (and x refl) (step tt (step tt x₂)) | true
                              = proofPreTransfer-solweakstaux  led1 led2 msg callingAddress x eq1 x₂



-- prove both direction precondition and weakestprecondition
proofTransfer : < PreTransfer >sol transferSec-Prog < PostTransfer >
proofTransfer .precond  = proofPreTransfer 
proofTransfer .weakest  = proofPreTransfer-solweakest 

