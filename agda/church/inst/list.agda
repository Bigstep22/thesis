open import funct.container
module church.inst.list where
open import Data.Product
open import Data.Nat
open import Data.Fin hiding (_+_; _>_)
open import Data.Empty
open import Data.Unit
open import Function.Base
open import Data.Bool

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



[] : {A : Set} → μ (F A)
[] = in' (nil , λ())


_::_ : {A : Set} → A → μ (F A) → μ (F A)
_::_ x xs = in' (cons x , λ tt → xs)
infixr 20 _::_


--map' : {A B : Set}(f : A → B) → μ (F A) → μ (F B)
--map' f (in' (cons x , l)) = (f x) :: map' f (l tt)
--map' f (in' (nil , l)) = []
--
--map'' : {A B : Set}(f : A → B) → μ (F A) → μ (F B)
--map'' f = ⦅ (λ where
--              (nil , _) → []
--              (cons n , g) → in' (cons (f n) , g)) ⦆
--proof' : (map'' (_+_ 2) l2) ≡ l1
--proof' = refl

fold' : {A X : Set}(n : X)(c : A → X → X) → μ (F A) → X
fold' {A}{X} n c = ⦅ (λ where
                        (nil , _) → n
                        (cons n , g) → c n (g tt) ) ⦆
map''' : {A B : Set}(f : A → B) → μ (F A) → μ (F B)
map''' f = fold' [] (λ x xs → (f x) :: xs)
l1 : μ (F ℕ)
l1 = 5 :: 8 :: []
l2 : μ (F ℕ)
l2 = 3 :: 6 :: []
proof : (map''' (_+_ 2) l2) ≡ l1
proof = refl



sum : μ (F ℕ) → ℕ
sum = ⦅ (λ where
            (nil , _) → 0
            (cons n , f) → n + f tt ) ⦆

count : (ℕ → Bool) → μ (F ℕ) → ℕ
count p = ⦅ (λ where
               (nil , _) → 0
               (cons true , f) → 1 + f tt
               (cons false , f) → f tt) ⦆ ∘ map''' p

sumworks : sum (5 :: 6 :: 7 :: []) ≡ 18
sumworks = refl


even : ℕ → Bool
even 0 = true
even (suc n) = not (even n)

countworks : count even (5 :: 6 :: 7 :: 8 :: []) ≡ 2
countworks = refl
