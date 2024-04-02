{-# OPTIONS --guardedness #-}
open import Data.Container renaming (⟦_⟧ to I⟦_⟧; refl to C-refl; sym to C-sym)
open import Level
module cochurch.proofs where
open import Function.Base using (id; _∘_; flip; _$_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import Data.Product
open import term.termcoalg
open ν
open import term.terminal
open import term.cofusion
open import funct.flaws
open import funct.funext
open import cochurch.defs

-- PAGE 52 - Proof 1
from-to-id : {F : Container 0ℓ 0ℓ} → fromCoCh ∘ toCoCh ≡ id
from-to-id {F} = funext (λ (x : ν F) → begin
    fromCoCh (toCoCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCoCh (CoCh out x)
  ≡⟨⟩ -- Definition of fromCh
    ⟦ out ⟧ x
  ≡⟨ reflection x ⟩
    x
  ≡⟨⟩
    id x
  ∎)

-- PAGE 52 - Proof 2
postulate freetheorem-terminal : {ℓ : Level}{F : Container 0ℓ 0ℓ}
                                 {C D : Set}{Y : Set ℓ}{c : C → I⟦ F ⟧ C}{d : D → I⟦ F ⟧ D}(h : C → D)
                                 (f : {X : Set} → (X → I⟦ F ⟧ X) → X → Y) →
                                 ((fmap h ∘ c) ≡ d ∘ h) → f c ≡ f d ∘ h
                                 -- TODO: Do D and Y need to be the same thing? This may be a cop-out...
to-from-id : {F : Container 0ℓ 0ℓ}{X : Set}(c : X → I⟦ F ⟧ X)(x : X) →
             toCoCh (fromCoCh (CoCh c x)) ≡ CoCh c x
to-from-id c x = begin
    toCoCh (fromCoCh (CoCh c x))
  ≡⟨⟩ -- definition of fromCh
    toCoCh (⟦ c ⟧ x)
  ≡⟨⟩ -- definition of toCh
    CoCh out (⟦ c ⟧ x)
  ≡⟨⟩ -- composition
    (CoCh out ∘ ⟦ c ⟧) x
  ≡⟨ flip cong-app x ∘ sym $ freetheorem-terminal ⟦ c ⟧ CoCh refl ⟩ -- I made some use of this: https://www-ps.informatik.uni-kiel.de/~sad/FreeTheorems/cgi-bin/free-theorems-webui.cgi
    CoCh c x
  ∎

to-from-id' : {F : Container 0ℓ 0ℓ} → toCoCh ∘ fromCoCh ≡ id
to-from-id' {F} = funext (λ where (CoCh c x) → to-from-id {F} c x)

-- PAGE 52 - Proof 3
-- New function constitutes an implementation for the produces function being replaced
prod-pres : {F : Container 0ℓ 0ℓ}{X : Set} (c : X → I⟦ F ⟧ X) (x : X) →
            fromCoCh ((λ s → CoCh c s) x) ≡ ⟦ c ⟧ x
prod-pres c x = begin
    fromCoCh ((λ s → CoCh c s) x)
  ≡⟨⟩ -- function application
    fromCoCh (CoCh c x)
  ≡⟨⟩ -- definition of toCh
    ⟦ c ⟧ x
  ∎

-- PAGE 52 - Proof 4
-- New function constitutes an implementation for the produces function being replaced
unCoCh : {F : Container 0ℓ 0ℓ}(f : {Y : Set} → (Y → I⟦ F ⟧ Y) → Y → ν F) (c : CoChurch F) → ν F
unCoCh f (CoCh c s) = f c s
cons-pres : {F : Container 0ℓ 0ℓ}{X : Set} → (f : {Y : Set} → (Y → I⟦ F ⟧ Y) → Y → ν F) → (x : ν F) →
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
record nat {F G : Container 0ℓ 0ℓ}(f : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X): Set₁ where
  field
    coherence : {A B : Set}(h : A → B) → fmap {G} h ∘ f ≡ f ∘ fmap {F} h
open nat ⦃ ... ⦄


valid-hom : {F G : Container 0ℓ 0ℓ}{X : Set}(h : X → I⟦ F ⟧ X)(f : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X)⦃ _ : nat f ⦄ →
            fmap ⟦ h ⟧ ∘ f ∘ h ≡ f ∘ out ∘ ⟦ h ⟧
valid-hom h f = begin
    (fmap ⟦ h ⟧ ∘ f) ∘ h
  ≡⟨ cong (_∘ h) (coherence ⟦ h ⟧) ⟩
    (f ∘ fmap ⟦ h ⟧) ∘ h
  ≡⟨⟩
    f ∘ out ∘ ⟦ h ⟧
  ∎
--【_】 : {X : Set} → (X → ⟦ F ⟧ X) → X → ν F
--out (【 c 】 x) = (λ (op , ar) -> op , 【 c 】 ∘ ar) (c x)
-- This will require some work w.r.t. natural transformations, time for some more definitions!

chTrans : {F G : Container 0ℓ 0ℓ}(f : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X) → CoChurch F → CoChurch G
chTrans f (CoCh c s) = CoCh (f ∘ c) s
trans-pred : {F G : Container 0ℓ 0ℓ}{X : Set} (h : X → I⟦ F ⟧ X) (f : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X)(x : X)⦃ _ : nat f ⦄ →
             fromCoCh (chTrans f (CoCh h x)) ≡ (⟦ f ∘ out ⟧ ∘ ⟦ h ⟧) x
trans-pred h f x = begin
    fromCoCh (chTrans f (CoCh h x))
  ≡⟨⟩ -- Function application
    fromCoCh (CoCh (f ∘ h) x)
  ≡⟨⟩ -- Definition of fromCh
    ⟦ f ∘ h ⟧ x
  ≡⟨ flip cong-app x $ fusion ⟦ h ⟧ (sym (valid-hom h f)) ⟩
    (⟦ f ∘ out ⟧ ∘ ⟦ h ⟧) x
  ∎
