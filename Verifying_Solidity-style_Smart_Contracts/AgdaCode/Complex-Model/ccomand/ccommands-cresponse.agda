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

--contract-command
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



-- contract-response
  CResponse : CCommands → Set
  CResponse (callView addr fname msg)  = MsgOrError
  CResponse (updatec fname fdef cost)  = ⊤
  CResponse (raiseException _ str)     = ⊥
  CResponse (transferc amount addr)   = ⊤
  CResponse (callc addr fname msg)    = Msg
  CResponse currentAddrLookupc = Address
  CResponse callAddrLookupc = Address
  CResponse (getAmountc addr) = Amount



--SmartContract is datatype of what happens when a function is applied to its arguments.
  data SmartContract (A : Set) : Set where
    return  :  ℕ → A → SmartContract A
    error   :  ErrorMsg → DebugInfo → SmartContract A
    exec    :  (c : CCommands) → (CResponse c → ℕ)
            → (CResponse c → SmartContract A)
            → SmartContract A



