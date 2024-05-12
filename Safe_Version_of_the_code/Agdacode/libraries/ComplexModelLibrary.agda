module libraries.ComplexModelLibrary where


open import Data.Nat  hiding (_>_; _≤_ ; _<_ )
open import Data.Bool hiding (_≤_ ; _<_)
open import basicDataStructure
open import Complex-Model.ccomand.ccommands-cresponse
open import libraries.IOlibrary


--define less
_<_ : ℕ → ℕ → Bool
zero < m = true
suc n < zero = false
suc n < suc m = n < m

--define greater
_>_ : ℕ → ℕ → Bool
zero > m = false
suc n > zero = true
suc n > suc m = n > m

--define equal
_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == suc m = false
suc n == zero  = false
suc n == suc m = n == m

-- define uint16 as in Solidity
Max_Uint : ℕ  
Max_Uint = 65535

--define max boolean with default 1 (true)
Max_Bool : ℕ
Max_Bool = 1

-- define max address as in Solidity
Max_Address : ℕ
Max_Address = 4631683569492647816942839400347516314130799386625622561578303360316525185597



--define check message in range View
checkMsgInRangeView : (bound : ℕ) → Msg
            → (ℕ → MsgOrError) → MsgOrError
checkMsgInRangeView bound (nat n) fn =
 if n < bound
 then (fn n)
 else err (strErr "View function result out of range")
checkMsgInRangeView bound (msg +msg msg₁) fun =
  err (strErr "View function didn't return a number")
checkMsgInRangeView bound (list l) fun =
  err (strErr "View function didn't return a number")


--define check message in range
checkMsgInRange : (bound : ℕ) → Msg
            → (ℕ → SmartContract Msg) → SmartContract Msg
checkMsgInRange bound (nat n) sc =
 if n < Max_Uint
 then (sc n)
 else exec (raiseException 1 "out of range error") (λ _ → 1)(λ ())
checkMsgInRange bound (msg +msg msg₁) sc =
 exec (raiseException 1 "out of range error")(λ _ → 1)(λ ())
checkMsgInRange bound (list l) sc =
 exec (raiseException 1 "out of range error")(λ _ → 1)(λ ())

--define check message or error in range
checkMsgOrErrorInRange : (bound : ℕ) → MsgOrError
             → (ℕ → SmartContract Msg)
             → SmartContract Msg
checkMsgOrErrorInRange bound (theMsg (nat n)) sc =
  if n < Max_Uint
  then (sc n)
  else exec (raiseException 1 "out of range error") (λ _ → 1)(λ ())
checkMsgOrErrorInRange bound (theMsg (_ +msg _)) sc =
  exec (raiseException 1 "out of range error")(λ _ → 1)(λ ())
checkMsgOrErrorInRange bound (theMsg (list _)) sc =
  exec (raiseException 1 "Not a number error")(λ _ → 1)(λ ())
checkMsgOrErrorInRange bound (err x) sc =
  exec (raiseException 1 (error2Str x))(λ _ → 1)(λ ())
