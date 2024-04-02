{-# OPTIONS --guardedness #-}
module cochurch.defs where
open import term.termcoalg
open ν
open import Data.Product
open import Data.Container renaming (⟦_⟧ to I⟦_⟧)
open import Level


data CoChurch (F : Container 0ℓ 0ℓ) : Set₁ where
  CoCh : {X : Set} → (X → I⟦ F ⟧ X) → X → CoChurch F
toCoCh : {F : Container 0ℓ 0ℓ} → ν F → CoChurch F
toCoCh x = CoCh out x
fromCoCh : {F : Container 0ℓ 0ℓ} → CoChurch F → ν F
fromCoCh (CoCh h x) = ⟦ h ⟧ x


data CoChurch' (F : Container 0ℓ 0ℓ) : Set₁ where
  cochurch : (∃ λ S → (S → I⟦ F ⟧ S) × S) → CoChurch' F
