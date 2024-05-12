module libraries.hoareTripleLibSimple where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_;and)
open import Data.Sum
open import Data.Maybe
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
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




--define stack program
record RemainingProgram : Set where
  constructor remainingProgram
  field
     prog  : SmartContract Msg
     stack : ExecutionStack
     calledAddress   :  Address
open RemainingProgram public



--define end program
endProg : Msg → RemainingProgram
endProg x = remainingProgram (return x) [] 0

--define hoare logic state
record HLState : Set where
  constructor stateEF
  field
    ledger          :  Ledger
    callingAddress  :  Address
open HLState public    


--define combine hoare logic
combineHLprog : RemainingProgram → HLState → StateExecFun
combineHLprog (remainingProgram prg st calledAddr) (stateEF led callingAddr ) = stateEF led st callingAddr calledAddr prg

--define Hoare Logic predicate
HLPred : Set₁
HLPred = HLState → Set


--define not terminate
NotTerminated : StateExecFun → Set
NotTerminated (stateEF led eStack callingAddr calledAddr (return x)) = ⊥
NotTerminated (stateEF led eStack callingAddr calledAddr (error x))  = ⊥
NotTerminated (stateEF led eStack callingAddr calledAddr (exec c x)) = ⊤


--define evalute function relation
data EFrel (l : Ledger) : StateExecFun → StateExecFun → Set where
  reflex : (s : StateExecFun) → EFrel l s s
  step   : {s s'' : StateExecFun} → NotTerminated s → EFrel l (stepEF l s) s'' → EFrel l s  s''


--define solidity precondition simple model
<_>solpresimplemodel_<_> : (φ : HLPred) → (p : RemainingProgram)(ψ : HLPred) → Set
<_>solpresimplemodel_<_> φ p ψ = (s s' : HLState) → (x : Msg) → φ s
     → EFrel (s .ledger)(combineHLprog p s) (combineHLprog (endProg x) s') → ψ s'


--define solidity weakestprecondition simple model
<_>solweakestsimplemodel_<_> : (φ : HLPred) → (p : RemainingProgram) → (ψ : HLPred) → Set
<_>solweakestsimplemodel_<_> φ p ψ = (s s' : HLState) → ( x : Msg) → ψ s'
     → EFrel (s .ledger)(combineHLprog p s) (combineHLprog (endProg x) s') → φ s

--define solidity recored
record <_>sol_<_> (φ : HLPred)(p : RemainingProgram)(ψ : HLPred) : Set where
  field
    precond  : < φ >solpresimplemodel p < ψ >
    weakest  : < φ >solweakestsimplemodel p < ψ >
open <_>sol_<_> public




--- the above functions proves some properties

efrelLemCallingAddr  : {l l1 l2 : Ledger}{callingAddr calledAddr callingAddr' calledAddr' : Address}{msg msg' : Msg}
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr (return msg))
                          (stateEF l2 [] callingAddr' calledAddr' (return msg')))
             → callingAddr ≡ callingAddr'
efrelLemCallingAddr {l} {l1} {.l1} {callingAddr} {calledAddr} {.callingAddr} {.calledAddr} {msg} {.msg} (reflex .(stateEF l1 [] callingAddr calledAddr (return msg))) = refl 

efrelLemCallingAddr'  : {l l1 l2 : Ledger}{callingAddr calledAddr callingAddr' calledAddr' : Address}{msg msg' : Msg}
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr (return msg))
                          (stateEF l2 [] callingAddr' calledAddr' (return msg')))
             → callingAddr' ≡ callingAddr
efrelLemCallingAddr' {l} {l1} {.l1} {callingAddr} {calledAddr} {.callingAddr} {.calledAddr} {msg} {.msg} (reflex .(stateEF l1 [] callingAddr calledAddr (return msg))) = refl



efrelLemCalledAddr  : {l l1 l2 : Ledger}{callingAddr calledAddr callingAddr' calledAddr' : Address}{msg msg' : Msg}
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr (return msg))
                          (stateEF l2 [] callingAddr' calledAddr' (return msg')))
             → calledAddr ≡ calledAddr'
efrelLemCalledAddr {l} {l1} {.l1} {callingAddr} {calledAddr} {.callingAddr} {.calledAddr} {msg} {.msg} (reflex .(stateEF l1 [] callingAddr calledAddr (return msg))) = refl


efrelLemCalledAddr'  : {l l1 l2 : Ledger}{callingAddr calledAddr callingAddr' calledAddr' : Address}{msg msg' : Msg}
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr (return msg))
                          (stateEF l2 [] callingAddr' calledAddr' (return msg')))
             → calledAddr' ≡ calledAddr
efrelLemCalledAddr' {l} {l1} {.l1} {callingAddr} {calledAddr} {.callingAddr} {.calledAddr} {msg} {.msg}  (reflex .(stateEF l1 [] callingAddr calledAddr (return msg))) = refl


efrelLemMsg  : (l l1 l2 : Ledger)(callingAddr calledAddr callingAddr' calledAddr' : Address)(msg msg' : Msg)
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr (return msg))
                          (stateEF l2 [] callingAddr' calledAddr' (return msg')))
             → msg ≡ msg'
efrelLemMsg l l1 .l1 callingAddr calledAddr .callingAddr .calledAddr msg .msg (reflex .(stateEF l1 [] callingAddr calledAddr (return msg))) = refl

efrelLemMsg'  : (l l1 l2 : Ledger)(callingAddr calledAddr callingAddr' calledAddr' : Address)(msg msg' : Msg)
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr (return msg))
                          (stateEF l2 [] callingAddr' calledAddr' (return msg')))
             → msg' ≡ msg
efrelLemMsg' l l1 .l1 callingAddr calledAddr .callingAddr .calledAddr msg .msg (reflex .(stateEF l1 [] callingAddr calledAddr (return msg))) = refl


efrelLemLedger  : {l l1 l2 : Ledger}{callingAddr calledAddr callingAddr' calledAddr' : Address}{msg msg' : Msg}
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr (return msg))
                          (stateEF l2 [] callingAddr' calledAddr' (return msg')))
             → l1 ≡ l2
efrelLemLedger {l} {l1} {.l1} {callingAddr} {calledAddr} {.callingAddr} {.calledAddr} {msg} {.msg} (reflex .(stateEF l1 [] callingAddr calledAddr (return msg))) = refl


efrelLemLedger' : {l l1 l2 : Ledger}{callingAddr calledAddr callingAddr' calledAddr' : Address}{msg msg' : Msg}
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr (return msg))
                          (stateEF l2 [] callingAddr' calledAddr' (return msg')))
             → l2 ≡ l1
efrelLemLedger' {l} {l1} {.l1} {callingAddr} {calledAddr} {.callingAddr} {.calledAddr} {msg} {.msg} (reflex .(stateEF l1 [] callingAddr calledAddr (return msg))) = refl


efrelLemNotErrorReturn  : {l l1 l2 : Ledger}{callingAddr calledAddr callingAddr' calledAddr' : Address}{errorMsg : ErrorMsg} {msg' : Msg}
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr (error errorMsg))
                          (stateEF l2 [] callingAddr' calledAddr' (return msg')))
             → ⊥
efrelLemNotErrorReturn {l} {l1} {l2} {callingAddr} {calledAddr} {callingAddr'} {calledAddr'} {errorMsg} {msg'} (step () x₁)


efrelLemNotErrorReturnr  : {l l1 l2 : Ledger}{callingAddr calledAddr callingAddr' calledAddr' : Address}{msg : Msg}{errorMsg' : ErrorMsg}
             (p : EFrel l (stateEF l1 [] callingAddr calledAddr  (return msg))
                          (stateEF l2 [] callingAddr' calledAddr' (error errorMsg')))
             → ⊥
efrelLemNotErrorReturnr {l} {l1} {l2} {callingAddr} {calledAddr} {callingAddr'} {calledAddr'} {msg} {errorMsg} (step () x₁)




updateLedgerAmountLem1 : (led : Ledger)(calledAddr destinationAddr : Address)(amount' : Amount)
                         (diff : ¬ (destinationAddr ≡ calledAddr))
                         (correctAmount : amount' ≦r  led calledAddr .amount)
                         -> updateLedgerAmount led calledAddr destinationAddr amount' correctAmount destinationAddr  .amount ≡ led destinationAddr .amount + amount'
updateLedgerAmountLem1 led calledAddr destinationAddr diff amount' corrrectAmount rewrite not≡lem1 amount' |  refl≡ᵇ₁ destinationAddr = refl

