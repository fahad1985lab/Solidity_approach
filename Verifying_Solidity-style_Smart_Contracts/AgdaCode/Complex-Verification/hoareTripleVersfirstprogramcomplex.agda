open import constantparameters

module Complex-Verification.hoareTripleVersfirstprogramcomplex (param : ConstantParameters) where

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

-- our work
open import Complex-Model.ledgerversion.Ledger-Complex-Model param 
open import Complex-Model.ccomand.ccommands-cresponse  
open import basicDataStructure
open import libraries.natCompare
open import libraries.Mainlibrary
open import libraries.boolLib
open import libraries.hoareTripleLibComplex param 
open import libraries.logic
open import libraries.emptyLib


--firsr program
--transfer 10 from address 0 to address 6
transferProg : RemainingProgram
transferProg .prog =
          exec (transferc 10 6)
          (λ gasused → 1)
          λ x → return 1 (nat 0) 
transferProg .stack = []
transferProg .calledAddress = 0
transferProg .gasUsed = 100
transferProg .funName = "f"
transferProg .msg = nat 0




--postcondition 
PostTransfer : HLPred
PostTransfer (stateEF led initialAddress callingAddress)
     = (led 6 .amount ≡ 10) ∧
       ((initialAddress ≡ 0) ∧
       (callingAddress ≡ 0))

--precondition 
PreTransfer : HLPred
PreTransfer (stateEF led initialAddress callingAddress)
    = (led 6 .amount ≡ 0) ∧
      ((10 ≦r led 0 .amount) ∧
      ((initialAddress ≡ 0)  ∧
      (callingAddress ≡ 0)))






--first direction (forward direction)
proofPreTransfer-precondAux : (led : Ledger)(10≦led1-0amount : 10 ≦r led 0 .amount)
                              (s' : HLState)(x : led 6 .amount ≡ 0)
                              (eq : updateLedgerAmount led 0 6 10 10≦led1-0amount ≡ ledger s')
                              → ledger s' 6 .amount ≡ 10
proofPreTransfer-precondAux led 10≦led1-0amount s' x eq rewrite sym eq | x = refl

-- prove first direction (forward direction) for precondition
proofPreTransfer-precond : < PreTransfer >solprecomplexmodel transferProg < PostTransfer >
proofPreTransfer-precond (stateEF led .0 .0) s' msg (and x (and 10≦led1-0amount (and refl refl)))
                (step tt x₃)  rewrite compareleq1 10  (led 0 .amount) 10≦led1-0amount
  = and (proofPreTransfer-precondAux led  10≦led1-0amount s' x (efrelLemLedger x₃)) (and (efrelLeminitialAddr' x₃) (efrelLemCallingAddr' x₃))




--second direction (backward direction)
proofPreTransfer-solweakestAux : (led : Ledger)(s : HLState)(msg : Msg)(x : led 6 .amount ≡ 10)(leqp : OrderingLeq 10 (ledger s 0 .amount))
                               (x₂    : EFrel (s .ledger)
                                        (executeTransferAux (s .ledger) (ledger s) [] (initialAddress s) (callingAddress s) 0 (return 1 (nat 0)) 100
                                         "f" (nat 0) 10 6 leqp)
                                        (stateEF led [] 0 0 0 (return 1 msg) 100 "f" (nat 0)))
                               → (ledger s 6 .amount ≡ 0) ∧
                                  (atom (10 ≦b ledger s 0 .amount) ∧
                                  ((initialAddress s ≡ 0) ∧ (callingAddress s ≡ 0)))
proofPreTransfer-solweakestAux .(updateLedgerAmount led 0 6 10 x₁) (stateEF led .0 .0) msg x (leq x₁)
        (reflex .(stateEF (updateLedgerAmount led 0 6 10 x₁) [] 0 0 0 (return 1 (nat 0)) 100 "f" (nat 0)))
          = and (0+lem= (led 6 .amount) 10 x) (and x₁ (and refl refl))
proofPreTransfer-solweakestAux led s msg x (greater x₁) (step () x₃)


--prove second direction (backward direction) for weakestprecondition
proofPreTransfer-solweakest : < PreTransfer >solweakestcomplexmodel transferProg < PostTransfer >
proofPreTransfer-solweakest s (stateEF led .0 .0) msg (and x (and refl refl)) (step tt x₂)
  = proofPreTransfer-solweakestAux led s msg x (compareLeq 10 (ledger s 0 .amount)) x₂


--prove both direction for hoare triple 
proofTransfer : < PreTransfer >sol transferProg < PostTransfer >
proofTransfer .precond = proofPreTransfer-precond 
proofTransfer .weakest = proofPreTransfer-solweakest






