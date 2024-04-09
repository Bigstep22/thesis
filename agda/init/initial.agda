open import Data.Container renaming (refl to C-refl; sym to C-sym; map to fmap)
open import Data.W renaming (sup to in')
open import Level
module agda.init.initial {F : Container 0ℓ 0ℓ}  where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import agda.funct.funext
open import Data.Product
open import Function.Base
open import agda.init.initalg

universal-propₗ : {X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
                  h ≡ ⦅ a ⦆ → h ∘ in' ≡ a ∘ fmap h
universal-propₗ a h eq = begin
    h ∘ in'
  ≡⟨ cong (_∘ in') eq ⟩
    ⦅ a ⦆ ∘ in'
  ≡⟨⟩
    a ∘ fmap ⦅ a ⦆
  ≡⟨ cong (λ x → a ∘ fmap x) (sym eq) ⟩
    a ∘ fmap h
  ∎

--universal-propᵣ : {X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
--                            h ∘ in' ≡ a ∘ fmap h → ⦅ a ⦆ ≡ h
--universal-propᵣ a h eq = {!!}

comp-law : {A : Set}(a : ⟦ F ⟧ A → A) → ⦅ a ⦆ ∘ in' ≡ a ∘ fmap ⦅ a ⦆
comp-law a = refl

reflection : (y : μ F) → ⦅ in' ⦆ y ≡ y
reflection (in' (op , ar)) = begin
     ⦅ in' ⦆ (in' (op , ar))
   ≡⟨⟩
     in' (op , ⦅ in' ⦆ ∘ ar)
   ≡⟨ cong (λ x -> in' (op , x)) (funext (reflection ∘ ar)) ⟩
     in' (op , ar)
   ∎

reflection-law : ⦅ in' ⦆ ≡ id
reflection-law = funext reflection


