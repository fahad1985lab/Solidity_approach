{-# OPTIONS --no-sized-types --safe #-}
open import constantparameters

module libraries.hoareTripleLibComplex (param : ConstantParameters) where

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

open import Complex-Model.ledgerversion.Ledger-Complex-Model param 
open import libraries.natCompare
open import libraries.logic
open import Complex-Model.ccomand.ccommands-cresponse  
open import basicDataStructure
open import libraries.Mainlibrary


-- define stack program
record RemainingProgram : Set where
  constructor remainingProgram
  field
     prog  : SmartContract Msg
     stack : ExecutionStack
     calledAddress   :  Address
     gasUsed         :  ℕ
     funName : FunctionName
     msg   : Msg
open RemainingProgram public

-- define end program
endProg : Msg → RemainingProgram
endProg x = remainingProgram (return 1 x) [] 0 100 "f" (nat 0)




-- define hoare logic state 
record HLState : Set where
  constructor stateEF
  field
    ledger           :  Ledger
    initialAddress  :  Address
    callingAddress  :  Address
open HLState public

-- define combine hoare logic program
combineHLprog : RemainingProgram → HLState → StateExecFun
combineHLprog (remainingProgram prg st calledAddr gasUsed funName msg) (stateEF led initialAddr callingAddr)
  = stateEF led st initialAddr callingAddr calledAddr prg gasUsed funName msg


-- define hoare logic predicate
HLPred : Set₁
HLPred = HLState → Set

--define not terminate 
NotTerminated : StateExecFun → Set
NotTerminated (stateEF led eStack initialAddr callingAddr calledAddr (return x x₁) gasLeft funNameevalState msgevalState)  = ⊥
NotTerminated (stateEF led eStack initialAddr callingAddr calledAddr (error x x₁) gasLeft funNameevalState msgevalState)   = ⊥
NotTerminated (stateEF led eStack initialAddr callingAddr calledAddr (exec c x x₁) gasLeft funNameevalState msgevalState)  = ⊤

-- define evaluate function relation
data EFrel (l : Ledger) : StateExecFun → StateExecFun → Set where
  reflex : (s : StateExecFun) → EFrel l s s
  step   : {s s'' : StateExecFun} → NotTerminated s → EFrel l (stepEF l s ) s'' → EFrel l s  s''


-- define a syntax to prove the precondition
-- solidity precondtion for complex model 
<_>solprecomplexmodel_<_> : (φ : HLPred)(p : RemainingProgram)(ψ : HLPred) → Set
<_>solprecomplexmodel_<_>  φ p ψ = (s s' : HLState) → (x : Msg)
                         → φ s → EFrel (s .ledger) (combineHLprog p s) (combineHLprog (endProg x) s')
                         → ψ s'

-- define a syntax to prove weakest precondition
-- solidity weakest precondtion for complex model 
<_>solweakestcomplexmodel_<_> : (φ : HLPred)(p : RemainingProgram)(ψ : HLPred) → Set
<_>solweakestcomplexmodel_<_>  φ p ψ = (s s' : HLState) → (x : Msg)
                             → ψ s' → EFrel (s .ledger) (combineHLprog p s) (combineHLprog (endProg x) s')
                             → φ s

--define solidity
-- to prove hoare triple for both directions
record <_>sol_<_> (φ : HLPred)(p : RemainingProgram)(ψ : HLPred) : Set where
  field
    precond  :  < φ >solprecomplexmodel p < ψ >
    weakest  :  < φ >solweakestcomplexmodel p < ψ >
open <_>sol_<_> public



--- the above functions prove properties (ledger, msg, initial address and calling address)
efrelLeminitialAddr  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → initialAddress ≡ initialAddress'
efrelLeminitialAddr {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl 



efrelLeminitialAddr'  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → initialAddress' ≡ initialAddress
efrelLeminitialAddr' {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl 


efrelLemCallingAddr  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → callingAddr ≡ callingAddr'
efrelLemCallingAddr {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl 

efrelLemCallingAddr'  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → callingAddr' ≡ callingAddr
efrelLemCallingAddr' {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl 



efrelLemCalledAddr  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → calledAddr ≡ calledAddr'
efrelLemCalledAddr {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl 


efrelLemCalledAddr'  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → calledAddr' ≡ calledAddr
efrelLemCalledAddr' {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl 


efrelLemMsg  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → msg ≡ msg'
efrelLemMsg {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl 

efrelLemMsg'  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → msg' ≡ msg
efrelLemMsg' {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl 


efrelLemLedger  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → l1 ≡ l2
efrelLemLedger {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl


efrelLemLedger' : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}
                  {costgas costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
                  (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas msg) gasUsed funName msg)
                               (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg))
             → l2 ≡ l1
efrelLemLedger' {l} {l1} {.l1} {initialAddress} {callingAddr} {calledAddr} {.(initialAddress)} {.callingAddr}
               {.(calledAddr)} {costgas} {costgas'} {gasUsed} {.(gasUsed)} {funName} {.(funName)} {msg} {.(msg)} (reflex .(stateEF l1 [] initialAddress callingAddr calledAddr
               (return costgas msg) gasUsed funName msg)) = refl



efrelLemNotErrorReturn  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}{errorMsg : ErrorMsg}{debug : DebugInfo}
                          {costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
             (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (error errorMsg debug) gasUsed funName msg)
                          (stateEF l2 [] initialAddress' callingAddr' calledAddr' (return costgas' msg') gasUsed' funName' msg'))
             → ⊥
efrelLemNotErrorReturn {l} {l1} {l2} {initialAddress} {callingAddr} {calledAddr} {initialAddress'} {callingAddr'} {calledAddr'} {errorMsg} {debug} {costgas'}
 {gasUsed} {gasUsed'} {funName} {funName'} {msg} {msg'} (step () p)



efrelLemNotErrorReturnr  : {l l1 l2 : Ledger}{initialAddress callingAddr calledAddr initialAddress' callingAddr' calledAddr' : Address}{errorMsg : ErrorMsg}{debug : DebugInfo}
                          {costgas' : ℕ}{gasUsed gasUsed' :  ℕ}{funName funName' : FunctionName}{msg msg' : Msg}
             (p : EFrel l (stateEF l1 [] initialAddress callingAddr calledAddr (return costgas' msg) gasUsed funName msg)
                          (stateEF l2 [] initialAddress' callingAddr' calledAddr' (error errorMsg debug) gasUsed' funName' msg'))
             → ⊥
efrelLemNotErrorReturnr {l} {l1} {l2} {initialAddress} {callingAddr} {calledAddr} {initialAddress'} {callingAddr'} {calledAddr'} {errorMsg} {debug} {costgas'} {gasUsed}
 {gasUsed'} {funName} {funName'} {msg} {msg'} (step () p)




