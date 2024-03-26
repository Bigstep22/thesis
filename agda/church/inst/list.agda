open import funct.container
module church.inst.list where
open import Data.Product
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Empty
open import Data.Unit
open import Function.Base
open import Data.Bool

open import init.initalg
open import funct.flaws
open import funct.funext

open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning

data ListOp (A : Set) : Set where
  nil : ListOp A
  cons : A → ListOp A

--F = ℕ ▹ (λ n → Fin n)
F : (X : Set) → Container
F X = (ListOp X) ▹ (λ where
        nil → ⊥
        (cons v) → ⊤)


List : Set → Set
List A = μ {F A} (F A)

[] : List ℕ
[] = in' (nil , λ())

_::_ : ℕ → List ℕ → List ℕ
_::_ x xs = in' (cons x , λ y → xs)
infixr 20 _::_


xs : List ℕ
xs = 5 :: 6 :: 7 :: []


map' : (ℕ → ℕ) → List ℕ → List ℕ
map' f (in' (cons x , xs)) = in' (cons (f x) , λ y → map' f (xs y))
map' f [] = []
l1 : List ℕ
l1 = 5 :: 6 :: 7 :: []
l2 : List ℕ
l2 = 3 :: 4 :: 5 :: []
proof : l1 ≡ (map' (_+_ 2) l2)
proof = refl

proof2 : (g f : ℕ → ℕ) → (map' f) ∘ (map' g) ≡ map' (f ∘ g)
proof2 g f = funext λ x → {!!}

sum : List ℕ → ℕ
--sum (in' (cons x , xs)) = x + {!xs !}
sum = ⦅ (λ x → {!!}) ⦆
--sum [] = 0

proof' : sum l1 ≡ 18
proof' = refl
--λ where
--           zero → 5
--           (suc zero) → 6
--           (suc (suc zero)) → 7


---- This is just fmap... lol
--
--sum : List ℕ → ℕ
--sum (n , l) = ⦅ sum ⦆ (in' ({!!} , λ x → {!!}))
