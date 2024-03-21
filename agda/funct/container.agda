open import Data.Product
open import Level
module funct.container where

record Container {ℓ : Level} : Set (suc ℓ) where
  constructor _▹_
  field
    Op : Set ℓ
    Ar : Op → Set ℓ

I⟦_⟧ : {ℓ : Level} → Container {ℓ} → Set ℓ → Set ℓ
I⟦ op ▹ ar ⟧ A = Σ[ x ∈ op ] (ar x → A)
