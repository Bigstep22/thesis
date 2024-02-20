{-# OPTIONS --guardedness #-}
open import cat.container
module cochurch.proofs {F : Container} where
open import Function.Base using (id; _∘_; flip; _$_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import Data.Product
open import cat.terminal
open ν
open import cat.free
open import cat.flaws
open import cat.funext
open import cochurch.defs

-- PAGE 52 - Proof 1
from-to-id : fromCoCh ∘ toCoCh ≡ id
from-to-id = funext (λ (x : ν F) → begin
    fromCoCh (toCoCh x)
  ≡⟨⟩ -- Definition of toCh
     fromCoCh (CoCh out x)
  ≡⟨⟩ -- Definition of fromCh
    【 out 】 x
  ≡⟨ reflection x ⟩
    x
  ≡⟨⟩
    id x
  ∎)

-- PAGE 52 - Proof 2
to-from-id : {X : Set}(c : X → ⟦ F ⟧ X)(x : X) →
             toCoCh (fromCoCh (CoCh c x)) ≡ CoCh c x
to-from-id c x = begin
    toCoCh (fromCoCh (CoCh c x))
  ≡⟨⟩ -- definition of fromCh
    toCoCh (【 c 】 x)
  ≡⟨⟩ -- definition of toCh
    CoCh out (【 c 】 x)
  ≡⟨⟩ -- composition
    (CoCh out ∘ 【 c 】) x
  ≡⟨ flip cong-app x ∘ sym $ freetheorem-terminal 【 c 】 CoCh refl ⟩ -- I made some use of this: https://www-ps.informatik.uni-kiel.de/~sad/FreeTheorems/cgi-bin/free-theorems-webui.cgi
    CoCh c x
  ∎

-- PAGE 52 - Proof 3
-- New function constitutes an implementation for the produces function being replaced
prod-pres : {X : Set} (c : X → ⟦ F ⟧ X) (x : X) →
            fromCoCh ((λ s → CoCh c s) x) ≡ 【 c 】 x
prod-pres c x = begin
    fromCoCh ((λ s → CoCh c s) x)
  ≡⟨⟩ -- function application
    fromCoCh (CoCh c x)
  ≡⟨⟩ -- definition of toCh
    【 c 】 x
  ∎

-- PAGE 52 - Proof 4
-- New function constitutes an implementation for the produces function being replaced
unCoCh : (f : {Y : Set} → (Y → ⟦ F ⟧ Y) → Y → ν {F} F) (c : CoChurch {F} F) → ν {F} F
unCoCh f (CoCh c s) = f c s
cons-pres : {X : Set} → (f : {Y : Set} → (Y → ⟦ F ⟧ Y) → Y → ν F) → (x : ν F) →
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
postulate coherence : {G : Container}{A B : Set}(h : A → B)
                      (f : {X : Set} → ⟦ F ⟧ X → ⟦ G ⟧ X) →
                      fmap h ∘ f ≡ f ∘ fmap h

valid-hom : {X : Set}(h : X → ⟦ F ⟧ X)(f : {Y : Set} → Y → Y) →
            fmap 【 h 】 ∘ f ∘ h ≡ f ∘ out ∘ 【 h 】
valid-hom h f = begin
    (fmap 【 h 】 ∘ f) ∘ h
  ≡⟨ cong (_∘ h) (coherence 【 h 】 f) ⟩
    (f ∘ fmap 【 h 】) ∘ h
  ≡⟨⟩
    f ∘ out ∘ 【 h 】
  ∎
--【_】 : {X : Set} → (X → ⟦ F ⟧ X) → X → ν F
--out (【 c 】 x) = (λ (op , ar) -> op , 【 c 】 ∘ ar) (c x)
-- This will require some work w.r.t. natural transformations, time for some more definitions!

chTrans : ∀ (f : {Y : Set} → Y → Y) → CoChurch {F} F → CoChurch {F} F
chTrans f (CoCh c s) = CoCh (f ∘ c) s
trans-pred :  {X : Set} (h : X → ⟦ F ⟧ X) (f : {Y : Set} → Y → Y)  (x : X) →
             fromCoCh (chTrans f (CoCh h x)) ≡ (【 f ∘ out 】 ∘ 【 h 】) x
trans-pred h f x = begin
    fromCoCh (chTrans f (CoCh h x))
  ≡⟨⟩ -- Function application
    fromCoCh (CoCh (f ∘ h) x)
  ≡⟨⟩ -- Definition of fromCh
    【 f ∘ h 】 x
  ≡⟨ flip cong-app x $ fusion 【 h 】 (f ∘ h) (f ∘ out) (valid-hom h f) ⟩
    (【 f ∘ out 】 ∘ 【 h 】) x
  ∎
