\paragraph{Example: List fusion}
\begin{code}[hide]
open import Level hiding (zero; suc)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Fin hiding (_+_; _>_; _-_)
open import Data.Empty
open import Data.Unit
open import Function.Base
open import Data.Bool
open import Agda.Builtin.Nat
open import agda.church.defs renaming (cons to consu)
open import agda.church.proofs
open import agda.funct.funext
open import agda.init.initalg
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
\end{code}
\begin{code}
module agda.church.inst.list where
open import Data.Container using (Container; ⟦_⟧; μ; map; _▷_)
open import Data.W renaming (sup to in')

data ListOp (A : Set) : Set where
  nil : ListOp A
  cons : A → ListOp A

F : (A : Set) → Container 0ℓ 0ℓ
F A = ListOp A ▷ λ where nil → ⊥
                         (cons n) → ⊤

List : (A : Set) → Set
List A = μ (F A)
List' : (A B : Set) → Set
List' A B = ⟦ F A ⟧ B



-- Investigation related to filter, the following lines are tangentially related to list
build : {F : Container _ _}{X : Set} → ({Y : Set} → (⟦ F ⟧ Y → Y) → X → Y) → (x : X) → μ F
build g = fromCh ∘ prodCh g
foldr' : {F : Container _ _}{X : Set} → (⟦ F ⟧ X → X) → μ F → X
foldr' c = consCh c ∘ toCh
filter : {A : Set} → (A → Bool) → List A → List A
filter p = fromCh ∘ prodCh (λ f → consCh (λ where
   (nil , l) → f (nil , l)
   (cons a , l) → if (p a) then f (cons a , l) else l tt)) ∘ toCh



[] : {A : Set} → μ (F A)
[] = in' (nil , λ())

_::_ : {A : Set} → A → List A → List A
_::_ x xs = in' (cons x , λ tt → xs)
infixr 20 _::_

fold' : {A X : Set}(n : X)(c : A → X → X) → List A → X
fold' {A}{X} n c = ⦅ (λ where
                        (nil , _) → n
                        (cons n , g) → c n (g tt) ) ⦆




b' : {B : Set} → (a : List' ℕ B → B) → ℕ → ℕ → B
b' a x zero = a (nil , λ())
b' a x (suc n) = a (cons x , λ tt → (b' a (suc x)  n))

b : {B : Set} → (a : List' ℕ B → B) → ℕ × ℕ → B
b a (x , y) = b' a x (suc (y - x))

between1 : ℕ × ℕ → List ℕ
between1 xy = b in' xy
between2 : ℕ × ℕ → List ℕ
between2 = prod b
eqbetween : between1 ≡ between2
eqbetween = refl
checkbetween : 2 :: 3 :: 4 :: 5 :: 6 :: [] ≡ between2 (2 , 6)
checkbetween = refl


m : {A B C : Set}(f : A → B) → List' A C → List' B C
m f (nil , _) = (nil , λ())
m f (cons n , l) = (cons (f n) , l)
map1 : {A B : Set}(f : A → B) → List A → List B
map1 f = ⦅ in' ∘ m f ⦆
map2 : {A B : Set}(f : A → B) → List A → List B
map2 f = natTrans (m f)
eqmap : {f : ℕ → ℕ} → map1 f ≡ map2 f
eqmap = refl
checkmap : (map1 (_+_ 2) (3 :: 6 :: [])) ≡ 5 :: 8 :: []
checkmap = refl


su : List' ℕ ℕ → ℕ
su (nil , _) = 0
su (cons n , f) = n + f tt
sum1 : List ℕ → ℕ
sum1 = ⦅ su ⦆
sum2 : List ℕ → ℕ
sum2 = consu su
eqsum : sum1 ≡ sum2
eqsum = refl
checksum : sum1 (5 :: 6 :: 7 :: []) ≡ 18
checksum = refl



eq : {f : ℕ → ℕ} → sum1 ∘ map1 f ∘ between1 ≡ sum2 ∘ map2 f ∘ between2
eq {f} = begin
    ⦅ su ⦆ ∘ ⦅ in' ∘ m f ⦆ ∘ b in'
  ≡⟨⟩
    ⦅ su ⦆ ∘ ⦅ in' ∘ m f ⦆ ∘ fromCh ∘ prodCh b
  ≡⟨ cong (λ f → ⦅ su ⦆ ∘ f ∘ prodCh b) (sym $ trans-pres (m f)) ⟩
    ⦅ su ⦆ ∘ fromCh ∘ natTransCh (m f) ∘ prodCh b
  ≡⟨ cong (λ g → g ∘ fromCh ∘ natTransCh (m f) ∘ prodCh b) (sym $ cons-pres su) ⟩
    consCh su ∘ toCh ∘ fromCh ∘ natTransCh (m f) ∘ prodCh b
  ≡⟨ cong (λ g → consCh su ∘ g ∘ natTransCh (m f) ∘ prodCh b) to-from-id ⟩
    consCh su ∘ natTransCh (m f) ∘ prodCh b
  ≡⟨ cong (λ g → consCh su ∘ g ∘ natTransCh (m f) ∘ g ∘ prodCh b) (sym to-from-id) ⟩
    consCh su ∘ toCh ∘ fromCh ∘ natTransCh (m f) ∘ toCh ∘ fromCh ∘ prodCh b
  ≡⟨⟩
    consu su ∘ natTrans (m f) ∘ prod b
  ∎



-- Bonus functions
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
\end{code}
