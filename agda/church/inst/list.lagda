\begin{code}
module agda.church.inst.list where
open import Data.Container using (Container; ⟦_⟧; μ; map; _▷_)
open import Data.W renaming (sup to in')
open import Level hiding (zero; suc)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Fin hiding (_+_; _>_; _-_)
open import Data.Empty
open import Data.Unit
open import Function.Base
open import Data.Bool
open import Agda.Builtin.Nat
open import agda.church.defs
open import agda.church.proofs

open import agda.funct.funext
open import agda.init.initalg

open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning

data ListOp (A : Set) : Set where
  nil : ListOp A
  cons : A → ListOp A

F : (A : Set) → Container 0ℓ 0ℓ
F A = ListOp A ▷ λ where
                 nil → ⊥
                 (cons n) → ⊤


List : (A : Set) → Set
List A = μ (F A)
List' : (A B : Set) → Set
List' A B = ⟦ F A ⟧ B

[] : {A : Set} → μ (F A)
[] = in' (nil , λ())


_::_ : {A : Set} → A → List A → List A
_::_ x xs = in' (cons x , λ tt → xs)
infixr 20 _::_


fold' : {A X : Set}(n : X)(c : A → X → X) → List A → X
fold' {A}{X} n c = ⦅ (λ where
                        (nil , _) → n
                        (cons n , g) → c n (g tt) ) ⦆

m : {A B C : Set}(f : A → B) → List' A C → List' B C
m f (nil , _) = (nil , λ())
m f (cons n , l) = (cons (f n) , l)
map1 : {A B : Set}(f : A → B) → List A → List B
map1 f = ⦅ in' ∘ m f ⦆
mapCh : {A B : Set}(f : A → B) → Church (F A) → Church (F B)
mapCh f (Ch g) = Ch (λ a → g (a ∘ m f))
map2 : {A B : Set}(f : A → B) → List A → List B
map2 f = fromCh ∘ mapCh f ∘ toCh
map3 : {A B : Set}(f : A → B) → List A → List B
map3 f = fromCh ∘ transCh (m f) ∘ toCh


l1 : μ (F ℕ)
l1 = 5 :: 8 :: []
l2 : μ (F ℕ)
l2 = 3 :: 6 :: []
proof : (map1 (_+_ 2) l2) ≡ l1
proof = refl


su : List' ℕ ℕ → ℕ
su (nil , _) = 0
su (cons n , f) = n + f tt
sum1 : List ℕ → ℕ
sum1 = ⦅ su ⦆
sumCh : Church (F ℕ) → ℕ
sumCh (Ch g) = g su
sum2 : List ℕ → ℕ
sum2 = sumCh ∘ toCh
sum3 : List ℕ → ℕ
sum3 = consCh su ∘ toCh

sumworks : sum1 (5 :: 6 :: 7 :: []) ≡ 18
sumworks = refl


b' : {B : Set} → (a : List' ℕ B → B) → ℕ → ℕ → B
b' a x zero = a (nil , λ())
b' a x (suc n) = a (cons x , λ tt → (b' a (suc x)  n))

b : {B : Set} → (a : List' ℕ B → B) → ℕ × ℕ → B
b a (x , y) = b' a x (suc (y - x))

between1 : ℕ × ℕ → List ℕ
between1 xy = b in' xy
betweenCh : ℕ × ℕ → Church (F ℕ)
betweenCh xy = Ch (λ a → b a xy)
between2 : ℕ × ℕ → List ℕ
between2 = fromCh ∘ betweenCh
between3 : ℕ × ℕ → List ℕ
between3 = fromCh ∘ prodCh b


check : 2 :: 3 :: 4 :: 5 :: 6 :: [] ≡ between2 (2 , 6)
check = refl

eq1 : {xy : ℕ × ℕ}{f : ℕ → ℕ} → (sum2 ∘ map2 f ∘ between2) ≡ (sumCh ∘ mapCh f ∘ betweenCh)
eq1 {xy}{f} = begin
    sumCh ∘ toCh ∘ fromCh ∘ mapCh f ∘ toCh ∘ fromCh ∘ betweenCh
  ≡⟨ cong (λ g → sumCh ∘ g ∘ mapCh f ∘ g ∘ betweenCh) to-from-id' ⟩
    sumCh ∘ mapCh f ∘ betweenCh
  ∎

eq2 : {xy : ℕ × ℕ}{f : ℕ → ℕ} → (sumCh ∘ mapCh f) (betweenCh xy) ≡ (sum1 ∘ map1 f) (between1 xy)
eq2 {xy}{f} = begin
    (sumCh ∘ mapCh f) (betweenCh xy)
  ≡⟨⟩
    (sumCh (Ch (λ a → b (a ∘ m f) xy)))
  ≡⟨⟩
    b (su ∘ m f) xy
  ≡⟨⟩
    consCh su (Ch (λ a → b (a ∘ m f) xy))
  ≡⟨ cong (consCh su) (sym $ cong-app to-from-id' (Ch (λ a → b (a ∘ m f) xy))) ⟩
    consCh su (toCh (fromCh (Ch (λ a → b (a ∘ m f) xy))))
  ≡⟨ cong-app (cons-pres su) (fromCh (Ch (λ a → b (a ∘ m f) xy))) ⟩
    ⦅ su ⦆ (fromCh (Ch (λ a → b (a ∘ m f) xy)))
  ≡⟨ cong ⦅ su ⦆ (trans-pred (flip b xy) (m f)) ⟩
    ⦅ su ⦆ (⦅ in' ∘ m f ⦆ (fromCh (Ch (λ a → b a xy))))
  ≡⟨ cong (⦅ su ⦆ ∘ ⦅ in' ∘ m f ⦆) (cong-app (prod-pres b) xy) ⟩
    (⦅ su ⦆ ∘ ⦅ in' ∘ m f ⦆) (b in' xy)
  ≡⟨⟩
    (sum1 ∘ map1 f) (between1 xy)
  ∎

-- Proofs for each of the above functions
eqsum : sum1 ≡ sum2
eqsum = refl
eqmap : {f : ℕ → ℕ} → map1 f ≡ map2 f
eqmap = refl
eqbetween : between1 ≡ between2
eqbetween = refl


-- Generalization of the above proofs for any container
-- MOVED TO DEFS.


transfuse : {F G H : Container 0ℓ 0ℓ}(nat1 : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
            (nat2 : {X : Set} → ⟦ G ⟧ X → ⟦ H ⟧ X) →
            transCh nat2 ∘ toCh ∘ fromCh ∘ transCh nat1 ≡ transCh (nat2 ∘ nat1)
transfuse nat1 nat2 = begin
            transCh nat2 ∘ toCh ∘ fromCh ∘ transCh nat1
          ≡⟨ cong (λ f → transCh nat2 ∘ f ∘ transCh nat1) to-from-id' ⟩
            transCh nat2 ∘ transCh nat1
          ≡⟨ funext (λ where (Ch g) → refl) ⟩
            transCh (nat2 ∘ nat1)
          ∎
pipfuse : {F G : Container 0ℓ 0ℓ}{X : Set}{g : {Y : Set} → (⟦ F ⟧ Y → Y) → X → Y}
          {nat : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X}{c : (⟦ G ⟧ X → X)} →
          consCh c ∘ transCh nat ∘ prodCh g ≡ g (c ∘ nat)
pipfuse = refl

-- Using the generalizations, we now get our encoding proofs and shortcut fusion for free :)







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
