\paragraph{Universal properties of catamorphisms}
This module proves some properties of catamorphisms.
\begin{code}
module agda.init.initial where
\end{code}
\begin{code}[hide]
open import agda.funct.funext
open import agda.init.initalg
open import Data.Product hiding (map)
\end{code}
The forward direction of the \textit{universal property of folds} \citep{Harper2011}:
\begin{code}
universal-prop : {F : Container 0ℓ 0ℓ}{X : Set}{a : ⟦ F ⟧ X → X}{h : μ F → X} →
                  h ≡ ⦅ a ⦆ → h ∘ in' ≡ a ∘ map h
universal-prop refl = refl
\end{code}
\begin{code}[hide]
universal-propᵣ' : {F : Container _ _}{X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
                            h ∘ in' ≡ a ∘ map h → (x : μ F) → h x ≡ ⦅ a ⦆ x
universal-propᵣ' {F}{X} a h eq (in' (i , f)) = begin
      (h ∘ in') (i , f)
    ≡⟨ cong-app eq (i , f) ⟩
      (a ∘ map h) (i , f)
    ≡⟨⟩
      a (i , h ∘ f)
    ≡⟨ cong (λ g → a (i , g)) (funext $ universal-propᵣ' a h eq ∘ f) ⟩
      a (i , ⦅ a ⦆ ∘ f)
    ≡⟨⟩
      (a ∘ map ⦅ a ⦆) (i , f)
    ≡⟨⟩
      (⦅ a ⦆ ∘ in') (i , f)
    ∎
universal-propᵣ : {F : Container _ _}{X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X)(x : (μ F)) →
                    h ∘ in' ≡ a ∘ map h → h x ≡ ⦅ a ⦆ x
universal-propᵣ {F}{X} a h x eq rewrite eq = universal-propᵣ' a h eq x
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
   ≡⟨ cong (λ x → in' (op , x)) (funext (reflection ∘ ar)) ⟩
     in' (op , ar)
   ∎

reflection-law : {F : Container 0ℓ 0ℓ} → ⦅ in' ⦆ ≡ id
reflection-law {F} = funext (reflection {F})
\end{code}
