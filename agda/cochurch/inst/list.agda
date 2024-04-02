{-# OPTIONS --guardedness #-}
module cochurch.inst.list where
open import cochurch.defs
open import cochurch.proofs
open import Data.Container renaming (⟦_⟧ to I⟦_⟧; refl to C-refl; sym to C-sym)
open import Level hiding (suc)
open import Data.Empty
open import Data.Unit
open import term.termcoalg
open ν
open import Data.Product
open import Function
open import Data.Nat
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import funct.funext

data ListOp (A : Set) : Set where
  nil : ListOp A
  cons : A → ListOp A

F : (A : Set) → Container 0ℓ 0ℓ
F A = ListOp A ▷ λ where
                   nil → ⊥
                   (cons n) → ⊤


List : (A : Set) → Set
List A = ν (F A)
List' : (A B : Set) → Set
List' A B = I⟦ F A ⟧ B

--[] : {A : Set} → ν (F A)
--out ([]) = (nil , λ())
--
--
--_::_ : {A : Set} → A → List A → List A
--out (x :: xs) = (cons x , λ tt → xs)
--infixr 20 _::_


--unfold' : {A X : Set}(n : X)(c : A → X → X) → List A → X
--unfold' {A}{X} n c = ⟦ (λ where
--                          (nil , _) → n
--                          (cons n , g) → c n (g tt) ) ⟧

m : {A B C : Set}(f : A → B) → List' A C → List' B C
m f (nil , _) = (nil , λ())
m f (cons n , l) = (cons (f n) , l)
map1 : {A B : Set}(f : A → B) → List A → List B
map1 f = ⟦ m f ∘ out ⟧
mapCoCh : {A B : Set}(f : A → B) → CoChurch (F A) → CoChurch (F B)
mapCoCh f (CoCh h s) = CoCh (m f ∘ h) s
map2 : {A B : Set}(f : A → B) → List A → List B
map2 f = fromCoCh ∘ mapCoCh f ∘ toCoCh

{-# NON_TERMINATING #-}
su' : {S : Set} → (S → List' ℕ S) → S → ℕ
su' h s with h s
su' h s | (nil , f) = 0
su' h s | (cons x , f) = x + su' h s

sum1 : List ℕ → ℕ
sum1 = su' out
sumCh : CoChurch (F ℕ) → ℕ
sumCh (CoCh h s) = su' h s
sum2 : List ℕ → ℕ
sum2 = sumCh ∘ toCoCh


b' : ℕ × ℕ → List' ℕ (ℕ × ℕ)
b' (x , zero)  = (nil , λ())
b' (x , suc n)  = (cons x , λ tt → (suc x , n))

b : ℕ × ℕ → List' ℕ (ℕ × ℕ)
b (x , y) = b' (x , (suc (y - x)))

between1 : ℕ × ℕ → List ℕ
between1 xy = ⟦ b ⟧ xy
betweenCoCh : (ℕ × ℕ → List' ℕ (ℕ × ℕ)) → (ℕ × ℕ) → CoChurch (F ℕ)
betweenCoCh b = CoCh b
between2 : ℕ × ℕ → List ℕ
between2 = fromCoCh ∘ CoCh b

-- Proofs for each of the above functions
eqsum : sum1 ≡ sum2
eqsum = refl
eqmap : {f : ℕ → ℕ} → map1 f ≡ map2 f
eqmap = refl
eqbetween : between1 ≡ between2
eqbetween = refl


-- Generalization of the above proofs for any container
prodCoCh : {F : Container 0ℓ 0ℓ}{Y : Set} → (g : Y → I⟦ F ⟧ Y) → Y → CoChurch F
prodCoCh g x = CoCh g x
eqprod : {F : Container 0ℓ 0ℓ}{Y : Set}{g : (Y → I⟦ F ⟧ Y)} →
         fromCoCh ∘ prodCoCh g ≡ ⟦ g ⟧
eqprod = refl
--mapCoCh : {A B : Set}(f : A → B) → CoChurch (F A) → CoChurch (F B)
--mapCoCh f (CoCh h s) = CoCh (m f ∘ h) s
transCoCh : {F G : Container 0ℓ 0ℓ}(nat : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X) → CoChurch F → CoChurch G
transCoCh n (CoCh h s) = CoCh (n ∘ h) s
eqtrans : {F G : Container 0ℓ 0ℓ}{nat : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X} →
          fromCoCh ∘ transCoCh nat ∘ toCoCh ≡ ⟦ nat ∘ out ⟧
eqtrans = refl
consCoCh : {F : Container 0ℓ 0ℓ}{Y : Set} → (c : {S : Set} → (S → I⟦ F ⟧ S) → S → Y) → CoChurch F → Y
consCoCh c (CoCh h s) = c h s
eqcons : {F : Container 0ℓ 0ℓ}{X : Set}{c : {S : Set} → (S → I⟦ F ⟧ S) → S → X} →
         consCoCh c ∘ toCoCh ≡ c out
eqcons = refl


transfuse : {F G H : Container 0ℓ 0ℓ}(nat1 : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X) →
            (nat2 : {X : Set} → I⟦ G ⟧ X → I⟦ H ⟧ X) →
            transCoCh nat2 ∘ toCoCh ∘ fromCoCh ∘ transCoCh nat1 ≡ transCoCh (nat2 ∘ nat1)
transfuse nat1 nat2 = begin
            transCoCh nat2 ∘ toCoCh ∘ fromCoCh ∘ transCoCh nat1
          ≡⟨ cong (λ f → transCoCh nat2 ∘ f ∘ transCoCh nat1) to-from-id' ⟩
            transCoCh nat2 ∘ transCoCh nat1
          ≡⟨ funext (λ where (CoCh h s) → refl) ⟩
            transCoCh (nat2 ∘ nat1)
          ∎
pipfuse : {F G : Container 0ℓ 0ℓ}{Y : Set}{g : Y → I⟦ F ⟧ Y}
          {nat : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X}{c : {S : Set} → (S → I⟦ G ⟧ S) → S → Y} →
          consCoCh c ∘ transCoCh nat ∘ prodCoCh g ≡ c (nat ∘ g)
pipfuse = refl

---- Using the generalizations, we now get our encoding proofs and shortcut fusion for free :)
between3 : ℕ × ℕ → List ℕ
between3 = fromCoCh ∘ prodCoCh b
map3 : {A B : Set}(f : A → B) → List A → List B
map3 f = fromCoCh ∘ transCoCh (m f) ∘ toCoCh
sum3 : List ℕ → ℕ
sum3 = consCoCh su' ∘ toCoCh
