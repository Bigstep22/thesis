\paragraph{Universal properties of catamorphisms}
\begin{code}[hide]
open import Data.Container using (Container; ⟦_⟧; μ; map)
open import Level
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import agda.funct.funext
open import Data.Product using (_,_)
open import Function.Base
open import agda.init.initalg
\end{code}
This module proves some properties of catamorphisms.
\begin{code}
module agda.init.initial where
open import Data.W using () renaming (sup to in')
\end{code}
The forward direction of the \textit{universal property of folds} \citep{Harper2011}:
\begin{code}
universal-prop : {F : Container 0ℓ 0ℓ}{X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
                  h ≡ ⦅ a ⦆ → h ∘ in' ≡ a ∘ map h
universal-prop a h eq rewrite eq = refl
\end{code}
\begin{code}[hide]
--universal-propᵣ : {X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
--                            h ∘ in' ≡ a ∘ map h → ⦅ a ⦆ ≡ h
--universal-propᵣ a h eq = {!!}
\end{code}
The \textit{computation law} \citep{Harper2011} (this is exactly how $\catam{\_}$ is defined in the first place):
\begin{code}
comp-law : {F : Container 0ℓ 0ℓ}{A : Set}(a : ⟦ F ⟧ A → A) → ⦅ a ⦆ ∘ in' ≡ a ∘ map ⦅ a ⦆
comp-law a = refl
\end{code}
The \textit{reflection law} \citep{Harper2011}:
\begin{code}
reflection : {F : Container 0ℓ 0ℓ}(y : μ F) → ⦅ in' ⦆ y ≡ y
reflection (in' (op , ar)) = begin
     ⦅ in' ⦆ (in' (op , ar))
   ≡⟨⟩ -- Dfn of ⦅_⦆
     in' (op , ⦅ in' ⦆ ∘ ar)
   ≡⟨ cong (λ x -> in' (op , x)) (funext (reflection ∘ ar)) ⟩
     in' (op , ar)
   ∎

reflection-law : {F : Container 0ℓ 0ℓ} → ⦅ in' ⦆ ≡ id
reflection-law {F} = funext (reflection {F})
\end{code}
