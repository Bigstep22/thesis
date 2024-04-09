\begin{code}
{-# OPTIONS --guardedness #-}
open import Data.Container using (Container; map) renaming (⟦_⟧ to I⟦_⟧)
open import Level
module agda.term.terminal {F : Container 0ℓ 0ℓ} where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import agda.funct.funext
open import agda.term.termcoalg
open ν
open import Function
open import Data.Product using (_,_; Σ)



universal-propₗ : {C : Set}(c : C → I⟦ F ⟧ C)(h : C → ν F) →
                 h ≡ ⟦ c ⟧ → out ∘ h ≡ map h ∘ c
universal-propₗ c h eq = begin
    out ∘ h
  ≡⟨ cong (_∘_ out) eq ⟩
    out ∘ ⟦ c ⟧
  ≡⟨⟩
    map ⟦ c ⟧ ∘ c
  ≡⟨ cong (_∘ c) (cong map (sym eq)) ⟩
    map h ∘ c
  ∎
--universal-propᵣ : {C : Set}(c : C → ⟦ F ⟧ C)(h : C → ν F) →
--                            out ∘ h ≡ map h ∘ c → h ≡ ⟦ c ⟧
--universal-propᵣ c h eq = {!!}

comp-law : {C : Set}(c : C → I⟦ F ⟧ C) → out ∘ ⟦ c ⟧ ≡ map ⟦ c ⟧ ∘ c
comp-law c = refl


{-# NON_TERMINATING #-}
reflection : (x : ν F) → ⟦ out ⟧ x ≡ x
reflection x = out-injective (begin
    out (⟦ out ⟧ x)
  ≡⟨⟩
    map ⟦ out ⟧ (out x)
  ≡⟨⟩
    op , ⟦ out ⟧ ∘ ar
  ≡⟨ cong (λ f → op , f) (funext $ reflection ∘ ar) ⟩
    op , id ∘ ar
  ≡⟨⟩
    map id (out x)
  ≡⟨⟩
    out x
  ∎)
  where op = Σ.proj₁ (out x)
        ar = Σ.proj₂ (out x)
\end{code}
