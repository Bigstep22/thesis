{-# OPTIONS --guardedness #-}
open import Data.Container renaming (⟦_⟧ to I⟦_⟧; refl to C-refl; sym to C-sym; map to fmap)
open import Level
module term.terminal {F : Container 0ℓ 0ℓ} where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import funct.funext
open import term.termcoalg
open ν
open import Function
open import Data.Product



universal-propₗ : {C : Set}(c : C → I⟦ F ⟧ C)(h : C → ν F) →
                 h ≡ ⟦ c ⟧ → out ∘ h ≡ fmap h ∘ c
universal-propₗ c h eq = begin
    out ∘ h
  ≡⟨ cong (_∘_ out) eq ⟩
    out ∘ ⟦ c ⟧
  ≡⟨⟩
    fmap ⟦ c ⟧ ∘ c
  ≡⟨ cong (_∘ c) (cong fmap (sym eq)) ⟩
    fmap h ∘ c
  ∎
--universal-propᵣ : {C : Set}(c : C → ⟦ F ⟧ C)(h : C → ν F) →
--                            out ∘ h ≡ fmap h ∘ c → h ≡ 【 c 】
--universal-propᵣ c h eq = {!!}

comp-law : {C : Set}(c : C → I⟦ F ⟧ C) → out ∘ ⟦ c ⟧ ≡ fmap ⟦ c ⟧ ∘ c
comp-law c = refl


{-# NON_TERMINATING #-}
reflection : (x : ν F) → ⟦ out ⟧ x ≡ x
reflection x = out-injective (begin
    out (⟦ out ⟧ x)
  ≡⟨⟩
    fmap ⟦ out ⟧ (out x) -- (λ (op , ar) -> op , 【 out 】 ∘ ar) (out x)
  ≡⟨⟩
    op , ⟦ out ⟧ ∘ ar
  ≡⟨ cong (λ f → op , f) (funext $ reflection ∘ ar) ⟩
    -- cong (λ f -> f (out x)) $ funext (λ (op , ar) → cong (λ x -> op , x) (funext (reflection ∘ ar)))
    op , id ∘ ar
  ≡⟨⟩
    fmap id (out x)
  ≡⟨⟩
    out x
  ∎)
  where op = Σ.proj₁ (out x)
        ar = Σ.proj₂ (out x)
