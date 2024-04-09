\begin{code}
open import Data.Container using (Container; ⟦_⟧; μ; map)
open import Data.W using () renaming (sup to in')
open import Level
module agda.init.initial {F : Container 0ℓ 0ℓ}  where
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import agda.funct.funext
open import Data.Product using (_,_)
open import Function.Base
open import agda.init.initalg

universal-propₗ : {X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
                  h ≡ ⦅ a ⦆ → h ∘ in' ≡ a ∘ map h
universal-propₗ a h eq = begin
    h ∘ in'
  ≡⟨ cong (_∘ in') eq ⟩
    ⦅ a ⦆ ∘ in'
  ≡⟨⟩
    a ∘ map ⦅ a ⦆
  ≡⟨ cong (λ x → a ∘ map x) (sym eq) ⟩
    a ∘ map h
  ∎

--universal-propᵣ : {X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
--                            h ∘ in' ≡ a ∘ map h → ⦅ a ⦆ ≡ h
--universal-propᵣ a h eq = {!!}

comp-law : {A : Set}(a : ⟦ F ⟧ A → A) → ⦅ a ⦆ ∘ in' ≡ a ∘ map ⦅ a ⦆
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


\end{code}
