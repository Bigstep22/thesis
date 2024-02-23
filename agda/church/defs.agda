open import funct.container
module church.defs {F : Container} where
open import funct.initial

data Church (F : Container) : Set₁ where
  Ch : ({X : Set} → (⟦ F ⟧ X → X) → X) → Church F
toCh : μ F → Church F
toCh x = Ch (λ {X : Set} → λ (a : ⟦ F ⟧ X → X) → ⦅ a ⦆ x)
fromCh : Church F → μ {F} F
fromCh (Ch g) = g in'
