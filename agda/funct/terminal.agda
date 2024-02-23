{-# OPTIONS --guardedness #-}
open import funct.container
module funct.terminal {F : Container } where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import funct.flaws
open import funct.funext
open import Function
open import Data.Product


-- An initial algebra
record ν (F : Container) : Set where
  coinductive
  field
    out : ⟦ F ⟧ (ν F)
open ν
-- an anamorphism
【_】 : {X : Set} → (X → ⟦ F ⟧ X) → X → ν F
out (【 c 】 x) = (λ (op , ar) -> op , 【 c 】 ∘ ar) (c x)
--fmap : {X Y : Set} → (Y → X) → ⟦ F ⟧ Y → ⟦ F ⟧ X
--fmap ca (op , ar) = op , ca ∘ ar

universal-propₗ : {C : Set}(c : C → ⟦ F ⟧ C)(h : C → ν F) →
                 h ≡ 【 c 】 → out ∘ h ≡ fmap h ∘ c
universal-propₗ c h eq = begin
    out ∘ h
  ≡⟨ cong (_∘_ out) eq ⟩
    out ∘ 【 c 】
  ≡⟨⟩
    fmap 【 c 】 ∘ c
  ≡⟨ cong (_∘ c) (cong fmap (sym eq)) ⟩
    fmap h ∘ c
  ∎
--universal-propᵣ : {C : Set}(c : C → ⟦ F ⟧ C)(h : C → ν F) →
--                            out ∘ h ≡ fmap h ∘ c → h ≡ 【 c 】
--universal-propᵣ c h eq = {!!}

comp-law : {C : Set}(c : C → ⟦ F ⟧ C) → out ∘ 【 c 】 ≡ fmap 【 c 】 ∘ c
comp-law c = refl

--{-# ETA ν #-} -- Seems to cause a hang (or major slowdown) in compilation
              -- in combination with reflection,
              -- have a chat with Casper
postulate νExt : {x y : ν F} → (out x ≡ out y) → x ≡ y
--νExt refl = refl

{-# NON_TERMINATING #-}
reflection : (x : ν F) → 【 out 】 x ≡ x
reflection x = νExt (begin
    out (【 out 】 x)
  ≡⟨ cong-app (comp-law out) x ⟩
    fmap 【 out 】 (out x) -- (λ (op , ar) -> op , 【 out 】 ∘ ar) (out x)
  ≡⟨ cong (flip fmap (out x)) $ funext reflection ⟩
    -- cong (λ f -> f (out x)) $ funext (λ (op , ar) → cong (λ x -> op , x) (funext (reflection ∘ ar)))
    fmap id (out x)
  ≡⟨ cong-app  fmap-id (out x) ⟩
    out x
  ∎)


postulate fusion : {C D : Set}(h : C → D)(c : C → ⟦ F ⟧ C)(d : D → ⟦ F ⟧ D) →
                   (fmap h ∘ c ≡ d ∘ h) → 【 c 】 ≡ 【 d 】 ∘ h
