open import constantparameters

module libraries.Mainlibrary where

open import Data.Nat
open import Data.List hiding (_++_)
open import Agda.Builtin.Nat using (_-_; _*_)
open import Data.Unit
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Maybe hiding (_>>=_)
open import Data.String hiding (length;show)
open import Data.Nat.Show
open import Data.Maybe.Base as Maybe using (Maybe; nothing; _<∣>_; when)
open import Data.Maybe.Effectful
open import Data.Product renaming (_,_ to _,,_ )
open import Agda.Builtin.String

--our work
open import basicDataStructure
open import libraries.natCompare
open import Complex-Model.ccomand.ccommands-cresponse


--define contract in complex model
record Contract : Set where
  constructor contract
  field
    amount : Amount
    fun    : FunctionName → (Msg → SmartContract Msg)
    viewFunction : FunctionName → Msg → MsgOrError
    viewFunctionCost : FunctionName → Msg → ℕ
open Contract public

--define ledger
Ledger : Set
Ledger = Address  → Contract



--define execute stack element
record ExecStackEl : Set where
  constructor execStackEl
  field
    lastCallAddress : Address
    calledAddress   : Address
    continuation : (Msg → SmartContract Msg)
    costCont     : Msg → ℕ
    funcNameexecStackEl : FunctionName
    msgexecStackEl      : Msg
open ExecStackEl public


ExecutionStack : Set
ExecutionStack = List ExecStackEl




--define state execution function
record StateExecFun : Set where
  constructor stateEF
  field
    ledger         : Ledger
    executionStack : ExecutionStack
    initialAddr    : Address
    lastCallAddr   : Address
    calledAddr     : Address
    nextstep       : SmartContract Msg
    gasLeft        : ℕ
    funNameevalState : FunctionName
    msgevalState   : Msg
open StateExecFun public

