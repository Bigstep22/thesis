\begin{code}
{-# OPTIONS --guardedness #-}
open import Data.Container using (Container; map; ⟦_⟧)
open import Level
module agda.cochurch.proofs where
open import Function.Base using (id; _∘_; flip; _$_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import Data.Product using (_,_)
open import agda.term.termcoalg
open ν
open import agda.term.terminal
open import agda.term.cofusion
open import agda.funct.funext
open import agda.cochurch.defs

-- PAGE 52 - Proof 1
from-to-id : {F : Container 0ℓ 0ℓ} → fromCoCh ∘ toCoCh ≡ id
from-to-id {F} = funext (λ (x : ν F) → begin
    fromCoCh (toCoCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCoCh (CoCh out x)
  ≡⟨⟩ -- Definition of fromCh
    A⟦ out ⟧ x
  ≡⟨ reflection x ⟩
    x
  ≡⟨⟩
    id x
  ∎)

-- PAGE 52 - Proof 2
postulate free : {F : Container 0ℓ 0ℓ}
                                 {C D : Set}{Y : Set₁}{c : C → ⟦ F ⟧ C}{d : D → ⟦ F ⟧ D}
                                 (h : C → D)(f : {X : Set} → (X → ⟦ F ⟧ X) → X → Y) →
                                 map h ∘ c ≡ d ∘ h → f c ≡ f d ∘ h
                                 -- TODO: Do D and Y need to be the same thing? This may be a cop-out...
unfold-invariance : {F : Container 0ℓ 0ℓ}{Y : Set}
                    (c : Y → ⟦ F ⟧ Y) →
                    CoCh c ≡ (CoCh out) ∘ A⟦ c ⟧
unfold-invariance c = free A⟦ c ⟧ CoCh refl

to-from-id : {F : Container 0ℓ 0ℓ} → toCoCh ∘ fromCoCh {F} ≡ id
to-from-id = funext λ where
  (CoCh c x) → (begin
      toCoCh (fromCoCh (CoCh c x))
    ≡⟨⟩ -- definition of fromCh
      toCoCh (A⟦ c ⟧ x)
    ≡⟨⟩ -- definition of toCh
      CoCh out (A⟦ c ⟧ x)
    ≡⟨⟩ -- composition
      (CoCh out ∘ A⟦ c ⟧) x
    ≡⟨ cong (λ f → f x) (sym $ unfold-invariance c) ⟩
      CoCh c x
    ∎)

-- PAGE 52 - Proof 3
-- New function constitutes an implementation for the produces function being replaced
prod-pres : {F : Container 0ℓ 0ℓ}{X : Set} (c : X → ⟦ F ⟧ X) (x : X) →
            fromCoCh ((λ s → CoCh c s) x) ≡ A⟦ c ⟧ x
prod-pres c x = begin
    fromCoCh ((λ s → CoCh c s) x)
  ≡⟨⟩ -- function application
    fromCoCh (CoCh c x)
  ≡⟨⟩ -- definition of toCh
    A⟦ c ⟧ x
  ∎

-- PAGE 52 - Proof 4
-- New function constitutes an implementation for the produces function being replaced
unCoCh : {F : Container 0ℓ 0ℓ}(f : {Y : Set} → (Y → ⟦ F ⟧ Y) → Y → ν F) (c : CoChurch F) → ν F
unCoCh f (CoCh c s) = f c s
cons-pres : {F : Container 0ℓ 0ℓ}{X : Set} → (f : {Y : Set} → (Y → ⟦ F ⟧ Y) → Y → ν F) → (x : ν F) →
            unCoCh f (toCoCh x) ≡ f out x
cons-pres f x = begin
    unCoCh f (toCoCh x)
  ≡⟨⟩ -- definition of toCoCh
    unCoCh f (CoCh out x)
  ≡⟨⟩ -- function application
    f out x
  ∎

-- PAGE 52 - Proof 5
-- New function constitutes an implementation for the transformation function being replaced
--(nat f)
record nat {F G : Container 0ℓ 0ℓ}(f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X): Set₁ where
  field
    coherence : {A B : Set}(h : A → B) → map h ∘ f ≡ f ∘ map h
open nat ⦃ ... ⦄

valid-hom : {F G : Container 0ℓ 0ℓ}{X : Set}(h : X → ⟦ F ⟧ X)(f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X)⦃ _ : nat f ⦄ →
            map A⟦ h ⟧ ∘ f ∘ h ≡ f ∘ out ∘ A⟦ h ⟧
valid-hom h f = begin
    (map A⟦ h ⟧ ∘ f) ∘ h
  ≡⟨ cong (_∘ h) (coherence A⟦ h ⟧) ⟩
    (f ∘ map A⟦ h ⟧) ∘ h
  ≡⟨⟩
    f ∘ out ∘ A⟦ h ⟧
  ∎

chTrans : {F G : Container 0ℓ 0ℓ}(f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) → CoChurch F → CoChurch G
chTrans f (CoCh c s) = CoCh (f ∘ c) s
trans-pres : {F G : Container 0ℓ 0ℓ}{X : Set} (h : X → ⟦ F ⟧ X) (f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X)(x : X)⦃ _ : nat f ⦄ →
             fromCoCh (chTrans f (CoCh h x)) ≡ (A⟦ f ∘ out ⟧ ∘ A⟦ h ⟧) x
trans-pres h f x = begin
    fromCoCh (chTrans f (CoCh h x))
  ≡⟨⟩ -- Function application
    fromCoCh (CoCh (f ∘ h) x)
  ≡⟨⟩ -- Definition of fromCh
    A⟦ f ∘ h ⟧ x
  ≡⟨ flip cong-app x $ fusion A⟦ h ⟧ (sym (valid-hom h f)) ⟩
    (A⟦ f ∘ out ⟧ ∘ A⟦ h ⟧) x
  ∎
\end{code}
