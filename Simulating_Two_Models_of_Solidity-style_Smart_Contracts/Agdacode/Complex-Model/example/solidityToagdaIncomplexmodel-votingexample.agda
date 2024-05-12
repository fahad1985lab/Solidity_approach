open import constantparameters

module Complex-Model.example.solidityToagdaIncomplexmodel-votingexample  where
open import Data.List 
open import Data.Bool.Base hiding (_<_)
open import Agda.Builtin.Unit 
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Maybe hiding (_>>=_)
open import Data.Nat.Base hiding (_<_; _>_)
open import Data.Nat.Show
open import Data.Fin.Base hiding (_+_; _-_; _<_; _>_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; sym ; cong)
open import Agda.Builtin.Nat using (_-_; _*_)


--our work
open import  libraries.natCompare
open import Complex-Model.ledgerversion.Ledger-Complex-Model exampleParameters
open import Complex-Model.ccomand.ccommands-cresponse
open import basicDataStructure
open import interface.ConsoleLib
open import libraries.IOlibrary
open import Complex-Model.IOledger.IOledger-votingexample
open import libraries.Mainlibrary
open import libraries.ComplexModelLibrary






--add voter function
addVoterAux : ℕ → (Msg → MsgOrError)
            → Msg → MsgOrError
addVoterAux newaddr oldCheckVoter (nat addr) =
 if    newaddr ≡ᵇ addr
 then  theMsg (nat 1) -- return 1 for true
 else  oldCheckVoter (nat addr)
addVoterAux ow ow' ow'' =
 err (strErr "The argument of checkVoter is not a number")



--delete voter function
deleteVoterAux : ℕ → (Msg → MsgOrError)
               → (Msg → MsgOrError)
deleteVoterAux  newaddr oldCheckVoter (nat addr) =
 if newaddr ≡ᵇ addr
 then theMsg (nat 0) -- return 1 for true
 else oldCheckVoter (nat addr)
deleteVoterAux ow ow' ow'' = err (strErr " You cannot delete voter ")



mysuc : MsgOrError → MsgOrError
mysuc (theMsg (nat n)) = theMsg (nat (suc n))
mysuc (theMsg  ow)= err (strErr " You cannot increment ")
mysuc ow = ow


-- incrementAux for many candidates
incrementcandidates : ℕ → (Msg → MsgOrError) → Msg → MsgOrError
incrementcandidates candidateVotedFor oldVoteResult (nat candidate) =
  if candidateVotedFor ≡ᵇ candidate
  then mysuc (oldVoteResult (nat candidate))
  else oldVoteResult (nat candidate)
incrementcandidates ow ow' ow'' = err (strErr " You cannot delete voter ")


incrementAux : ℕ → SmartContract Msg
incrementAux candidate =
  (exec (updatec "voteResult" (incrementcandidates candidate) λ oldFun oldcost msg → 1)(λ n → 1)) λ x → return 1 (nat candidate)




--define voteaux solidity
voteAux : Address → ℕ → (candidate : ℕ)
         → SmartContract Msg
voteAux addr 0 candidate
  = error (strErr "The voter is not allowed to vote") ⟨ 0 >> 0 ∙ "Voter is not allowed to vote" [ nat 0 ]⟩
voteAux addr (suc _) candidate
  = exec (updatec "checkVoter" (deleteVoterAux addr) λ oldFun oldcost msg → 1)(λ _ → 1) (λ x → (incrementAux candidate))


--- testLedger example
testLedger : Ledger
testLedger 1 .amount = 100
testLedger 1 .viewFunction "checkVoter" msg  =  checkMsgInRangeView Max_Address msg λ voter  → theMsg (nat 0)
testLedger 1 .viewFunction "voteResult" msg  =  checkMsgInRangeView Max_Uint msg λ voter → theMsg (nat 0)
testLedger 1 .viewFunctionCost "checkVoter" msg  = 1
testLedger 1 .viewFunctionCost "voterResult" msg = 1

testLedger 1 .fun "addVoter" msg     = checkMsgInRange Max_Address msg λ user →
                                       exec (callView 1 "checkVoter" (nat user))
                                       (λ _ → 1) λ msgResult → checkMsgOrErrorInRange Max_Bool msgResult 
                                       λ {0 → exec (updatec "checkVoter" (addVoterAux user) λ oldFun oldcost msg → 1)
                                               (λ _ → 1) (λ _ → return 1 (nat 1));
                                         (suc _) → exec (raiseException 1 "Voter already exists")(λ _ → 1)(λ ())}

testLedger 1 .fun "deleteVoter" msg  =  checkMsgInRange Max_Address msg λ user →
                                        exec (callView 1 "checkVoter" (nat user))
                                        (λ _ → 1) λ msgResult → checkMsgOrErrorInRange Max_Bool msgResult 
                                        λ {0 → exec (raiseException 1 "Voter does not exist")(λ _ → 1)(λ ());
                                          (suc _) → exec (updatec "checkVoter" (deleteVoterAux user) λ oldFun oldcost msg → 1)
                                          (λ _ → 1) (λ _ → return 1 (nat 0))}

testLedger 1 .fun "vote" msg = checkMsgInRange Max_Uint msg λ candidate → 
                               exec callAddrLookupc  (λ _ → 1)
                               λ addr → exec (callView 1 "checkVoter" (nat addr)) 
                               (λ _ → 1) λ msgResult → checkMsgOrErrorInRange Max_Bool msgResult
                               λ b → voteAux addr b candidate
                               
-- for purpuse testing we define address 0, 3, and 5  
testLedger 0 .amount   = 100
testLedger 3 .amount   = 100
testLedger 5 .amount   = 100

testLedger ow .amount  = 0
testLedger ow .fun ow' ow'' = error (strErr "Undefined") ⟨ ow >> ow ∙ ow' [ ow'' ]⟩
testLedger ow .viewFunction ow' ow'' = err (strErr "Undefined")
testLedger ow .viewFunctionCost ow' ow'' = 1



--main program IO
main  : ConsoleProg
main  = run (mainBody (⟨ testLedger ledger, 0 initialAddr, 20 gas⟩))


