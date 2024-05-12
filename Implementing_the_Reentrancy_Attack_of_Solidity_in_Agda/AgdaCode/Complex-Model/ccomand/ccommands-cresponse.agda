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
-- contract-commands:

  data CCommands : Set where
    callc : Address → FunctionName → Msg → Amount → CCommands
    getTransferAmount : CCommands
    eventc : String → CCommands
    callView   : Address → FunctionName → Msg → CCommands
    updatec    : FunctionName → ((Msg → MsgOrError) → (Msg → MsgOrError))
               → ((Msg → MsgOrError) → (Msg → ℕ) → Msg → ℕ) → CCommands
    transferc  : Amount → Address → CCommands
    transfercWithoutFallBack  : Amount → Address → CCommands    
    callcAssumingTransferc : Address → FunctionName → Msg → Amount → CCommands 
    currentAddrLookupc : CCommands
    callAddrLookupc : CCommands
    getAmountc : Address → CCommands
    

-- contract-response:
  CResponse : CCommands → Set
  CResponse (callc addr fname msg amount) = Msg
  CResponse getTransferAmount = Amount
  CResponse (eventc s) = ⊤
  CResponse (transferc amount addr)   = Msg
  CResponse (transfercWithoutFallBack amount addr) = Msg
  CResponse (callcAssumingTransferc addr fname msg amount)    = Msg
  CResponse currentAddrLookupc = Address
  CResponse callAddrLookupc = Address
  CResponse (getAmountc addr) = Amount
  CResponse (callView addr fname msg)  = MsgOrError
  CResponse (updatec fname fdef cost)  = ⊤



--SmartContract is datatype of what happens when a function is applied to its arguments.
  data SmartContract (A : Set) : Set where
    return  : A → SmartContract A
    error   : ErrorMsg → DebugInfo → SmartContract A
    exec    : (c : CCommands) → (CResponse c → ℕ)
            → (CResponse c → SmartContract A) → SmartContract A



emptymsg : Msg
emptymsg = list []


fallback : String
fallback = "fallback"
