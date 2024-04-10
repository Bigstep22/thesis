\begin{code}
{-# OPTIONS --guardedness #-}
open import agda.term.termcoalg
open ν
open import Data.Product
open import Level
open import Function
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
module agda.cochurch.defs where
open import Data.Container using (Container) renaming (⟦_⟧ to I⟦_⟧)

data CoChurch (F : Container 0ℓ 0ℓ) : Set₁ where
  CoCh : {X : Set} → (X → I⟦ F ⟧ X) → X → CoChurch F
toCoCh : {F : Container 0ℓ 0ℓ} → ν F → CoChurch F
toCoCh x = CoCh out x
fromCoCh : {F : Container 0ℓ 0ℓ} → CoChurch F → ν F
fromCoCh (CoCh h x) = ⟦ h ⟧ x


prodCoCh : {F : Container 0ℓ 0ℓ}{Y : Set} → (g : Y → I⟦ F ⟧ Y) → Y → CoChurch F
prodCoCh g x = CoCh g x
eqprod : {F : Container 0ℓ 0ℓ}{Y : Set}{g : (Y → I⟦ F ⟧ Y)} →
         fromCoCh ∘ prodCoCh g ≡ ⟦ g ⟧
eqprod = refl
transCoCh : {F G : Container 0ℓ 0ℓ}(nat : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X) → CoChurch F → CoChurch G
transCoCh n (CoCh h s) = CoCh (n ∘ h) s
eqtrans : {F G : Container 0ℓ 0ℓ}{nat : {X : Set} → I⟦ F ⟧ X → I⟦ G ⟧ X} →
          fromCoCh ∘ transCoCh nat ∘ toCoCh ≡ ⟦ nat ∘ out ⟧
eqtrans = refl
consCoCh : {F : Container 0ℓ 0ℓ}{Y : Set} → (c : {S : Set} → (S → I⟦ F ⟧ S) → S → Y) → CoChurch F → Y
consCoCh c (CoCh h s) = c h s
eqcons : {F : Container 0ℓ 0ℓ}{X : Set}{c : {S : Set} → (S → I⟦ F ⟧ S) → S → X} →
         consCoCh c ∘ toCoCh ≡ c out
eqcons = refl


data CoChurch' (F : Container 0ℓ 0ℓ) : Set₁ where
  cochurch : (∃ λ S → (S → I⟦ F ⟧ S) × S) → CoChurch' F
\end{code}
