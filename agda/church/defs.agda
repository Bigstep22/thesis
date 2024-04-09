module agda.church.defs where
open import Data.Container using (Container; μ; ⟦_⟧)
open import Data.W using () renaming (sup to in')
open import Level using (0ℓ)
open import agda.init.initalg

data Church (F : Container 0ℓ 0ℓ) : Set₁ where
  Ch : ({X : Set} → (⟦ F ⟧ X → X) → X) → Church F
toCh : {F : Container 0ℓ 0ℓ} → μ F → Church F
toCh {F} x = Ch (λ {X : Set} → λ (a : ⟦ F ⟧ X → X) → ⦅ a ⦆ x)
fromCh : {F : Container 0ℓ 0ℓ} → Church F → μ F
fromCh (Ch g) = g in'
