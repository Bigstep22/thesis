open import Data.Product
open import Level renaming (suc to lsuc; zero to lzero)
open import Agda.Builtin.Equality

module funct.container where


record Container {ℓ : Level} : Set (lsuc ℓ) where
  constructor _▹_
  field
    Op : Set ℓ
    Ar : Op → Set ℓ

I⟦_⟧ : {ℓ : Level} → Container {ℓ} → Set ℓ → Set ℓ
I⟦ op ▹ ar ⟧ A = Σ[ x ∈ op ] (ar x → A)
