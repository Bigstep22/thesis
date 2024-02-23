open import Data.Product

module funct.container where

record Container : Set₁ where
  constructor _▹_
  field
    Op : Set
    Ar : Op → Set

⟦_⟧ : Container → Set → Set
⟦ op ▹ ar ⟧ A = Σ[ x ∈ op ] (ar x → A)
