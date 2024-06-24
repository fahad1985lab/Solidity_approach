{-# OPTIONS --no-sized-types --safe #-}
module Simple-Verification.hoareTripleVersfirstprogram where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_;and)
open import Data.Sum
open import Data.Maybe
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality

open import Simple-Model.ledgerversion.Ledger-Simple-Model
open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel
open import libraries.natCompare
open import libraries.logic
open import libraries.hoareTripleLibSimple
open import libraries.emptyLib
open import libraries.boolLib



-- simple program transfer 10 from address 0 to address 6  
transferProg : RemainingProgram
transferProg .prog =
        exec (transferc 10 6)
        λ _ → return (nat 0)
transferProg .stack = []
transferProg .calledAddress = 0

-- definition of postcondition
PostTransfer : HLPred
PostTransfer (stateEF led callingAddress) =
  (led 6 .amount ≡ 10) ∧ (callingAddress ≡ 0)

-- definition of precondition
PreTransfer : HLPred
PreTransfer (stateEF led callingAddress) =
            (led 6 .amount ≡ 0) ∧
            ((10 ≦r led 0 .amount ) ∧
            (callingAddress ≡ 0))



------ first direction 

proofPreTransferaux1 : (led1 : Ledger)
    (10≦led1-0amount : 10 ≦r led1 0 .amount)
    (s' : HLState)(x  : led1 6 .amount ≡ 0)
    (eq : updateLedgerAmount led1 0 6 10 10≦led1-0amount ≡ HLState.ledger s')
    → HLState.ledger s' 6 .amount ≡ 10
proofPreTransferaux1 led1 10≦led1-0amount s' x eq  rewrite sym eq | x = refl

-- prove first direction for precondition

proofPreTransfer : < PreTransfer >solpresimplemodel transferProg < PostTransfer >
proofPreTransfer (stateEF led1 .0) s' msg (and x (and 10≦led1-0amount refl)) (step tt x₃) rewrite compareleq1 10 (led1 0 .amount) 10≦led1-0amount
  = and (proofPreTransferaux1 led1 10≦led1-0amount s' x (efrelLemLedger x₃)) (efrelLemCallingAddr' x₃)



------ second direction 

proofPreTransfer-solweakestaux : (led1 led2 : Ledger)(msg : Msg)(callingAddress : ℕ)(led2==10 : led2 6 .amount ≡ 10) (leqp : OrderingLeq 10 (led1 0 .amount))
                                 (x₂   : EFrel led1 (executeTransferAux led1 led1 [] callingAddress 0 10 6  (return (nat 0)) leqp)
                                                (stateEF led2 [] 0 0 (return msg)))
                                 → (led1 6 .amount ≡ 0) ∧   ((10 ≦r led1 0 .amount) ∧ (callingAddress ≡ 0))
proofPreTransfer-solweakestaux led1 .(updateLedgerAmount led1 0 6 10 x) msg .0 led2==10 (leq x) (reflex .(stateEF (updateLedgerAmount led1 0 6 10 x) [] 0 0 (return (nat 0))))
  = and (0+lem= (led1 6 .amount) 10 led2==10) (and x refl)
proofPreTransfer-solweakestaux led1 led2 msg callingAddress led2==10 (greater x) (step () x₂)



-- prove second direction for weakestprecondition
proofPreTransfer-solweakest : < PreTransfer >solweakestsimplemodel transferProg < PostTransfer >
proofPreTransfer-solweakest  (stateEF led1 callingAddress) (stateEF led2 .0) msg (and x refl) (step tt x₂)
  = proofPreTransfer-solweakestaux led1 led2 msg callingAddress x (compareLeq 10 (led1 0 .amount)) x₂


-- prove both direction precondition and weakestprecondition
proofTransfer : < PreTransfer >sol transferProg < PostTransfer >
proofTransfer .precond  =  proofPreTransfer 
proofTransfer .weakest  =  proofPreTransfer-solweakest 




