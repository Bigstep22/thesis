open import funct.container
module church.defs where
open import init.initalg

data Church (F : Container) : Set₁ where
  Ch : ({X : Set} → (I⟦ F ⟧ X → X) → X) → Church F
toCh : {F : Container} → μ F → Church F
toCh {F} x = Ch (λ {X : Set} → λ (a : I⟦ F ⟧ X → X) → ⦅ a ⦆ x)
fromCh : {F : Container} → Church F → μ F
fromCh (Ch g) = g in'
