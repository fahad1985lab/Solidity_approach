module libraries.natCompare  where


open import Data.Nat  hiding (_≤_ ; _<_ )
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Empty
open import Data.Unit

open import libraries.boolLib
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)

-- our work
open import libraries.emptyLib
open import libraries.logic




--define less or equal boolean
_≦b_  :  ℕ → ℕ → Bool
zero   ≦b  m       = true
suc n  ≦b  zero    = false
suc n  ≦b  suc m   = n ≦b m



--define equal boolean
_==b_ : ℕ → ℕ → Bool
zero   ==b  zero   =  true
zero   ==b  suc n  =  false
suc n  ==b  zero   =  false
suc n  ==b suc m   =  n ==b m

-- ≦r  is a recursively defined ≦
_≦r_ : ℕ → ℕ → Set
n ≦r m = atom (n ≦b m)


_==r_ : ℕ → ℕ → Set
n ==r m = atom (n ==b m)

_<r_ : ℕ → ℕ → Set
n <r m = suc n ≦r m



<r->¬≦r : (n m :  ℕ) -> n ≦r  m -> ¬ (suc m ≦r n)
<r->¬≦r zero (suc m) p q = q
<r->¬≦r (suc n) (suc m) p q = <r->¬≦r n m p q


_>r_ : ℕ → ℕ → Set
n >r m = m <r n


0≦n : {n : ℕ} → zero ≦r n
0≦n = tt

data OrderingLeq (n m :  ℕ) : Set where
   leq     : n ≦r m → OrderingLeq n m
   greater : m <r  n  → OrderingLeq n m


refl≡ᵇ : (n : ℕ) -> atom (n ≡ᵇ n)
refl≡ᵇ zero  = tt
refl≡ᵇ (suc n)  = refl≡ᵇ n

refl≡ᵇ₁ : (n : ℕ) -> (n ≡ᵇ n) ≡ true
refl≡ᵇ₁ zero = refl
refl≡ᵇ₁ (suc n) = refl≡ᵇ₁ n


cong' : {A B : Set}{a a' : A}(f : A -> B) -> a ≡ a' -> f a  ≡ f a'
cong'  f refl = refl

sucInj : {x y : ℕ} -> suc x ≡ suc y -> x ≡ y
sucInj = cong' pred 


≡ᵇ->≡ : {x y :  ℕ} -> atom (x ≡ᵇ y) -> x ≡ y
≡ᵇ->≡ {zero} {zero} p = refl
≡ᵇ->≡ {suc x} {suc y} p = cong suc (≡ᵇ->≡ p)

≡->≡ᵇ : {x y :  ℕ} -> x ≡ y -> atom (x ≡ᵇ y) 
≡->≡ᵇ {zero} {zero} p = tt
≡->≡ᵇ {suc x} {suc y} p = ≡->≡ᵇ (sucInj p)

not≡lem2 : {x y : ℕ} -> (x ≡ᵇ y) ≡ false -> ¬ (atom (x ≡ᵇ y))
not≡lem2 {x} {y}  = atomLemFalse (x ≡ᵇ y)

not≡lem3 : {x y : ℕ} -> (x ≡ᵇ y) ≡ true -> atom (x ≡ᵇ y)
not≡lem3 {x} {y}  = atomLemTrue (x ≡ᵇ y)   

not≡lem1 : {x y : ℕ} (p : ¬ (x ≡ y)) ->  (x ≡ᵇ y) ≡ false
not≡lem1 {x} {y} p with (x ≡ᵇ y) in eq
... | false = refl
... | true = efq (p (≡ᵇ->≡ (atomLemTrue (x ≡ᵇ y) eq)))

 

liftLeq : {n m : ℕ} → OrderingLeq n m → OrderingLeq (suc n) (suc m)
liftLeq {n} {m} (leq x) = leq x
liftLeq {n} {m} (greater x) = greater x


compareLeq : (n m : ℕ) → OrderingLeq n m
compareLeq zero n = leq tt
compareLeq (suc n) zero = greater tt
compareLeq (suc n) (suc m) = liftLeq (compareLeq n m)

-- a useful lemma
compareleq1 : (x y : ℕ)(xy : x ≦r y) → compareLeq x y ≡ leq xy
compareleq1 zero zero tt = refl
compareleq1 zero (suc y) tt = refl
compareleq1 (suc x) (suc y) xy rewrite compareleq1 x y xy = refl


transfer≡r : {A : Set}(B : A -> Set) {a a' : A} -> a  ≡ a' -> B a' -> B a
transfer≡r {A} B {a} {.a} refl b = b

transfer≡ : {A : Set}(B : A -> Set) {a a' : A} -> a  ≡ a' -> B a -> B a'
transfer≡ {A} B {a} {.a} refl b = b

compareleq2 : (x y : ℕ)(xy : (x ≦b y) ≡ true)  → atom (x ≦b y)
compareleq2 x y xy = transfer≡r  {Bool} (λ x -> atom x) xy tt 

compareleq3 : (x y : ℕ)(xy : (x ≦b y) ≡ true)  → compareLeq x y ≡ leq (compareleq2 x y xy)
compareleq3  x y xy  = compareleq1 x y (compareleq2 x y xy)



data OrderingLess (n m :  ℕ) : Set where
   less     : n <r m → OrderingLess n m
   geq      : m ≦r  n  → OrderingLess n m


liftLess : {n m : ℕ} → OrderingLess n m → OrderingLess (suc n) (suc m)
liftLess {n} {m} (less x) = less x
liftLess {n} {m} (geq x) = geq x


compareLess : (n m : ℕ) → OrderingLess n m
compareLess n zero = geq tt
compareLess zero (suc m) = less tt
compareLess (suc n) (suc m) = liftLess (compareLess n m)



subtract : (n m : ℕ) → m ≦r n → ℕ
subtract n zero nm = n
subtract (suc n) (suc m) nm = subtract n m nm


refl≦r : (n : ℕ) →   n ≦r n
refl≦r 0 = tt
refl≦r (suc n) = refl≦r n

refl==r : (n : ℕ) →   n ==r n
refl==r zero = tt
refl==r (suc n) = refl==r n


lemmaxysuc : (x y : ℕ) → x ≦r y → x ≦r suc y
lemmaxysuc zero y xy = tt
lemmaxysuc (suc x) (suc y) xy = lemmaxysuc x y xy


lemmaxSucY : (x y z : ℕ) → x ≦r suc y → (x ∸ (suc z)) ≦r  y
lemmaxSucY 0 y z xy = tt
lemmaxSucY (suc x) y zero xy = xy
lemmaxSucY (suc x) y (suc z) xy = lemmaxSucY x y z (lemmaxysuc x y xy)

lemma=≦r : (x y z : ℕ) → x ==r y → y ≦r z → x ≦r z
lemma=≦r zero y z x=y y≦rz   = tt
lemma=≦r (suc x) (suc y) (suc z) x=y y≦rz = lemma=≦r x y z x=y y≦rz

{- do it yourself -}
trans<=r : (x y z : ℕ) → x ≦r y → y ≦r z → x ≦r z
trans<=r zero y z xy yz = tt
trans<=r (suc x) (suc y) (suc z) xy yz = trans<=r x y z xy yz

sym== : (x y : ℕ) → x ==r y → y ==r x
sym== zero zero xy = tt
sym== (suc x) (suc y) xy = sym== x y xy


x<=sucx : (x : ℕ) → x ≦r suc x
x<=sucx zero = tt
x<=sucx (suc x) = x<=sucx x

0+lem> : (x y : ℕ) → (suc x + y) >r y
0+lem> zero y = refl≦r y
0+lem> (suc x) y = trans<=r y (x + y) (suc (x + y)) (0+lem> x y) (x<=sucx (x + y))

-- test : (x y : ℕ) → suc (x + y) >r y
-- test = 0+lem>

notsux<=x : (x : ℕ) -> suc x ≦r x -> ⊥
notsux<=x (suc x) p = notsux<=x x p

>impliesNotEq : (x y : ℕ) ->  x >r y  -> x ≡ y -> ⊥
>impliesNotEq (suc x) (suc .x) x>y refl = notsux<=x x x>y

sucx+yNot=y : (x y :  ℕ) ->  suc x + y ≡ y -> ⊥
sucx+yNot=y x y = >impliesNotEq (suc x + y) y (0+lem> x y) 

0+lem= : (x y : ℕ) → x + y ≡ y -> x ≡ 0
0+lem= zero y refl = refl
0+lem= (suc x) y p = efq (sucx+yNot=y x y p) 

trans≡ : {A : Set} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
trans≡  refl refl = refl

sym≡ : {A : Set} {a b  : A} -> a ≡ b -> b ≡ a
sym≡  refl = refl





atomN<=N : ∀ (n : ℕ) → atom (n ≦b n)
atomN<=N zero    = tt
atomN<=N (suc n) = atomN<=N n


proof : ∀ ( n m : ℕ) → atom ((m + suc n) ≦b suc (m + suc n))
proof zero zero    = tt
proof zero (suc m) = proof zero m
proof (suc n) zero    = proof n zero
proof (suc n) (suc m) = proof (suc n) m

trans<=b : (n k : ℕ) → atom (n ≦b k ) → atom (k ≦b suc k) → atom (n ≦b suc k)
trans<=b zero zero tt tt = tt
trans<=b zero (suc k) tt x₁    = tt
trans<=b (suc n) (suc k) x x₁ = trans<=b n k x x₁

atomN<=sucM+sucN : ∀ (n m : ℕ) → atom (n ≦b suc (m + n))
atomN<=sucM+sucN zero m = tt
atomN<=sucM+sucN (suc n) zero = atomN<=sucM+sucN n zero
atomN<=sucM+sucN (suc n) (suc m) = trans<=b n (m + suc n) (atomN<=sucM+sucN (suc n) m) (proof n m) 


atomN<=bM+N : ∀ (n m : ℕ) → atom (n ≦b (m + n))
atomN<=bM+N n zero     = atomN<=N n
atomN<=bM+N n (suc m)  = atomN<=sucM+sucN n m
