module Simple-Model.library-simple-model.basicDataStructureWithSimpleModel where

open import Data.Nat
open import Data.String hiding (length)
open import Data.List
open import Data.Bool
open import Agda.Builtin.String



FunctionName : Set
FunctionName = String



_≡fun_ : FunctionName → FunctionName → Bool
_≡fun_ = primStringEquality


--define message (msg)
data Msg : Set where
   nat     :  ℕ          →  Msg
   list    :  List Msg   →  Msg


Time   : Set
Time   =   ℕ


Amount : Set
Amount =  ℕ

--define errormsg
data ErrorMsg : Set where
  strErr     : String → ErrorMsg
  numErr     : ℕ → ErrorMsg
  undefined  : ErrorMsg


Address : Set
Address  =  ℕ


Signature : Set
Signature =  ℕ

PublicKey : Set
PublicKey  =  ℕ


--define natorerror
data NatOrError : Set where
 nat : ℕ → NatOrError
 err : ErrorMsg → NatOrError




data MsgOrError : Set where
 theMsg  : Msg → MsgOrError
 err : ErrorMsg → MsgOrError




