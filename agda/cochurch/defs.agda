{-# OPTIONS --guardedness #-}
open import funct.container
module cochurch.defs where
open import term.termcoalg
open ν
open import Data.Product


data CoChurch (F : Container) : Set₁ where
  CoCh : {X : Set} → (X → I⟦ F ⟧ X) → X → CoChurch F
toCoCh : {F : Container} → ν F → CoChurch F
toCoCh x = CoCh out x
fromCoCh : {F : Container} → CoChurch F → ν F
fromCoCh (CoCh h x) = ⟦ h ⟧ x


data CoChurch' (F : Container) : Set₁ where
  cochurch : (∃ λ S → (S → I⟦ F ⟧ S) × S) → CoChurch' F
