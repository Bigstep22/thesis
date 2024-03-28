open import funct.container
module church.inst.list where
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Fin hiding (_+_; _>_; _-_)
open import Data.Empty
open import Data.Unit
open import Function.Base
open import Data.Bool
open import Agda.Builtin.Nat
open import church.defs

open import funct.funext
open import init.initalg

open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning

data ListOp (A : Set) : Set where
  nil : ListOp A
  cons : A → ListOp A

--open import funct.flaws {ℕ ▹ Fin}
F : (A : Set) → Container
F A = ListOp A ▹ λ where
                 nil → ⊥
                 (cons n) → ⊤

List : (A : Set) → Set
List A = μ (F A)
List' : (A B : Set) → Set
List' A B = I⟦ F A ⟧ B

[] : {A : Set} → μ (F A)
[] = in' (nil , λ())


_::_ : {A : Set} → A → List A → List A
_::_ x xs = in' (cons x , λ tt → xs)
infixr 20 _::_


fold' : {A X : Set}(n : X)(c : A → X → X) → List A → X
fold' {A}{X} n c = ⦅ (λ where
                        (nil , _) → n
                        (cons n , g) → c n (g tt) ) ⦆

map1 : {A B : Set}(f : A → B) → List A → List B
map1 f = fold' [] (λ x xs → (f x) :: xs)
m : {A B C : Set}(f : A → B) → List' A C → List' B C
m f (nil , _) = (nil , λ())
m f (cons n , l) = (cons (f n) , l)
mapCh : {A B : Set}(f : A → B) → Church (F A) → Church (F B)
mapCh f (Ch g) = Ch (λ a → g (a ∘ m f))
map2 : {A B : Set}(f : A → B) → List A → List B
map2 f = fromCh ∘ mapCh f ∘ toCh
--                                This last bit doesn't quite fit, new base functor needed?
--                                It should be a nonrecursive implementation....

--map : {A B : Set} (f : A → B) → μ (F A) → μ (F B)
--map f = ⦅ m f ⦆
l1 : μ (F ℕ)
l1 = 5 :: 8 :: []
l2 : μ (F ℕ)
l2 = 3 :: 6 :: []
proof : (map1 (_+_ 2) l2) ≡ l1
proof = refl
--proof2 : {A B : Set} → (f : A → B) → (map1 f ≡ map2 f)
--proof2 f = funext (λ where
--                    (in' (nil , _)) → refl
--                    (in' (cons x , l)) → begin
--                           map1 f (in' (cons x , l))
--                         ≡⟨ refl ⟩
--                           (in' (cons (f x) , (map1 f) ∘ l))
--                         ≡⟨ cong (λ h → in' (cons (f x) , h ∘ l)) {!!} ⟩
--                         -- Close, but no cigar....
--                           (in' (cons (f x) , (map2 f) ∘ l))
--                         ≡⟨ refl ⟩
--                           map2 f (in' (cons x , l))
--                         ∎)



su : List' ℕ ℕ → ℕ
su (nil , _) = 0
su (cons n , f) = n + f tt

sum : μ (F ℕ) → ℕ
sum = ⦅ su ⦆
sumCh : Church (F ℕ) → ℕ
sumCh (Ch g) = g su
sum2 = sumCh ∘ toCh

sumworks : sum (5 :: 6 :: 7 :: []) ≡ 18
sumworks = refl


applyUpTo : {A : Set} → (ℕ → A) → ℕ → μ (F A)
applyUpTo f zero    = []
applyUpTo f (suc n) = f zero :: applyUpTo (f ∘ suc) n

upTo : ℕ → μ (F ℕ)
upTo = applyUpTo id

between1 : ℕ → ℕ → List ℕ
between1 x y = applyUpTo (_+_ x) (suc (y - x))
b' : {B : Set} → (a : List' ℕ B → B) → ℕ → ℕ → B
b' a x zero = a (nil , λ())
b' a x (suc n) = a (cons x , λ tt → (b' a (suc x) n))

b : {B : Set} → (a : List' ℕ B → B) → ℕ → ℕ → B
b a x y = b' a x (suc (y - x))
betweenCh : ℕ → ℕ → Church (F ℕ)
betweenCh x y = Ch (λ a → b a x y)
between2 : ℕ → ℕ → List ℕ
between2 x y = fromCh (betweenCh x y)


check : 2 :: 3 :: 4 :: 5 :: 6 :: [] ≡ between1 2 6
check = refl







count : (ℕ → Bool) → μ (F ℕ) → ℕ
count p = ⦅ (λ where
               (nil , _) → 0
               (cons true , f) → 1 + f tt
               (cons false , f) → f tt) ⦆ ∘ map1 p



even : ℕ → Bool
even 0 = true
even (suc n) = not (even n)
odd : ℕ → Bool
odd = not ∘ even

countworks : count even (5 :: 6 :: 7 :: 8 :: []) ≡ 2
countworks = refl
