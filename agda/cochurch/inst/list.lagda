\begin{code}[hide]
{-# OPTIONS --guardedness #-}
module agda.cochurch.inst.list where
open import agda.cochurch.defs renaming (cons to consu)
open import agda.cochurch.proofs
open import Data.Container using (Container; map; _▷_; ⟦_⟧)
open import Level hiding (suc)
open import Data.Empty
open import Data.Unit
open import agda.term.termcoalg
open ν
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Function
open import Data.Nat
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
\end{code}
\begin{code}
open import agda.funct.funext

data ListOp (A : Set) : Set where
  nil : ListOp A
  cons : A → ListOp A

F : (A : Set) → Container 0ℓ 0ℓ
F A = ListOp A ▷ λ { nil → ⊥ ; (cons n) → ⊤ }

List : (A : Set) → Set
List A = ν (F A)
List' : (A B : Set) → Set
List' A B = ⟦ F A ⟧ B

[] : {A : Set} → List A
out ([]) = (nil , λ())

_::_ : {A : Set} → A → List A → List A
out (x :: xs) = (cons x , const xs)
infixr 20 _::_



b' : ℕ × ℕ → List' ℕ (ℕ × ℕ)
b' (x , zero)  = (nil , λ())
b' (x , suc n)  = (cons x , const (suc x , n))

b : ℕ × ℕ → List' ℕ (ℕ × ℕ)
b (x , y) = b' (x , (suc (y - x)))

between1 : ℕ × ℕ → List ℕ
between1 = A⟦ b ⟧
between2 : ℕ × ℕ → List ℕ
between2 = prod b
eqbetween : between1 ≡ between2
eqbetween = refl
--checkbetween : out (2 :: 3 :: 4 :: 5 :: 6 :: []) ≡ out (between2 (2 , 6))
--checkbetween = refl

mapping : {A X : Set} → (f : X → ⊤ ⊎ (A × X)) → (X → List' A X)
mapping f x with f x
mapping f x | (inj₁ tt) = (nil , λ())
mapping f x | (inj₂ (a , x')) = (cons a , const x')
unfold' : {F : Container 0ℓ 0ℓ}{A X : Set}(f : X → ⊤ ⊎ (A × X)) → X → List A
unfold' {A}{X} f = A⟦ mapping f ⟧

m : {A B C : Set}(f : A → B) → List' A C → List' B C
m f (nil , l) = (nil , l)
m f (cons n , l) = (cons (f n) , l)

map1 : {A B : Set}(f : A → B) → List A → List B
map1 f = A⟦ m f ∘ out ⟧
map2 : {A B : Set}(f : A → B) → List A → List B
map2 f = natTrans (m f)
eqmap : {f : ℕ → ℕ} → map1 f ≡ map2 f
eqmap = refl
--checkmap : map1 (_+_ 2) (3 :: 6 :: []) ≡ 5 :: 8 :: []
--checkmap = refl

{-# NON_TERMINATING #-}
su : {S : Set} → (S → List' ℕ S) → S → ℕ
su h s with h s
su h s | (nil , f) = 0
su h s | (cons x , f) = x + su h (f tt)

sum1 : List ℕ → ℕ
sum1 = su out
sum2 : List ℕ → ℕ
sum2 = consu su
eqsum : sum1 ≡ sum2
eqsum = refl
--checksum : sum1 (5 :: 6 :: 7 :: []) ≡ 18
--checksum = refl

eq : {f : ℕ → ℕ} → sum1 ∘ map1 f ∘ between1 ≡ sum2 ∘ map2 f ∘ between2
eq {f} = begin
    su out ∘ A⟦ m f ∘ out ⟧ ∘ A⟦ b ⟧
  ≡⟨ cong (λ g → su out ∘ g) (sym (trans-pres b (m f) (λ _ → funext (λ {(nil , l) → refl ; (cons n , l) → refl})))) ⟩
--    su out ∘ A⟦ m f ∘ out ⟧ ∘ fromCoCh ∘ prodCoCh b
--  ≡⟨ cong (λ g → su out ∘ g ∘ prodCoCh b) {!!} ⟩ -- trans-pres is different from church.... this causes this step to be skipped?
    su out ∘ fromCoCh ∘ natTransCoCh (m f) ∘ prodCoCh b
  ≡⟨ cong (λ g → g ∘ fromCoCh ∘ natTransCoCh (m f) ∘ prodCoCh b) (cons-pres su) ⟩
    consCoCh su ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh (m f) ∘ prodCoCh b
  ≡⟨ cong (λ g → consCoCh su ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh (m f) ∘ g ∘ prodCoCh b) (sym to-from-id) ⟩
    consCoCh su ∘ toCoCh ∘ fromCoCh ∘ natTransCoCh (m f) ∘ toCoCh ∘ fromCoCh ∘ prodCoCh b
  ≡⟨⟩
    consu su ∘ natTrans (m f) ∘ prod b
  ∎
\end{code}
