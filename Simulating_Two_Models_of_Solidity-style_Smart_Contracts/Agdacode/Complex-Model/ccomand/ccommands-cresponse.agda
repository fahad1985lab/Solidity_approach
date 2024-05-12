module Complex-Model.ccomand.ccommands-cresponse where

open import Data.Nat
open import Agda.Builtin.Nat using (_-_)
open import Data.Unit
open import Data.List
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe  hiding (_>>=_)
open import Data.String hiding (length)
open import Data.Empty


-- libraries
open import basicDataStructure
open import libraries.natCompare



mutual

--smart contract commands  
  data CCommands : Set where
    callView   : Address → FunctionName → Msg → CCommands 
    updatec    : FunctionName → ((Msg → MsgOrError)
               → (Msg → MsgOrError)) → ((Msg → MsgOrError)
               → (Msg → ℕ) → Msg → ℕ) → CCommands
    raiseException : ℕ → String → CCommands 
    transferc  : Amount → Address → CCommands
    callc      : Address → FunctionName → Msg → CCommands
    currentAddrLookupc : CCommands
    callAddrLookupc : CCommands
    getAmountc : Address → CCommands

     

--smart contract responses 
  CResponse : CCommands → Set
  CResponse (callView addr fname msg)  = MsgOrError
  CResponse (updatec fname fdef cost)  = ⊤
  CResponse (raiseException _ str)     = ⊥
  CResponse (transferc amount addr)    = ⊤
  CResponse (callc addr fname msg)     = Msg
  CResponse currentAddrLookupc         = Address
  CResponse callAddrLookupc            = Address
  CResponse (getAmountc addr)          = Amount
  


--SmartContractExec is datatype of what happens when a function is applied to its arguments.
--SmartContractExec --> SmartContractExec 
  data SmartContract (A : Set) : Set where
    return  : ℕ → A → SmartContract A
    error   : ErrorMsg → DebugInfo → SmartContract A
    exec    : (c : CCommands) → (CResponse c → ℕ)
            → (CResponse c → SmartContract A) → SmartContract A



_>>=_ : {A B : Set} → SmartContract A → (A → SmartContract B) → SmartContract B
return n x >>= q    = q x
error x z >>= q     = error x z
exec c n x >>= q  = exec c n (λ r → x r >>= q)


_>>_ : {A B : Set} → SmartContract A → SmartContract B → SmartContract B
return n x >> q   = q
error x z >> q    = error x z
exec c n x >> q = exec c n (λ r → x r >> q)

