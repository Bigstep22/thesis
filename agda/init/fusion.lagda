\subsubsection{Initial F-Algebra fusion}
\begin{code}[hide]
module agda.init.fusion where
open import Categories.Functor.Algebra
open import Categories.Object.Initial
open IsInitial
open import agda.funct.funext
open import agda.init.initial
open import agda.funct.endo
open import Categories.Category renaming (Category to Cat)
\end{code}
This section proves the fusion property (see \autoref{sec:fusion_prop}).
From it, it extracts the `fusion law' as it was described by \cite{Harper2011}; which uses non-categorical type definitions.
The categorical fusion property:
\begin{code}
fusionprop : {F : Container 0ℓ 0ℓ}{A B μ : Set}{ϕ : ⟦ F ⟧ A → A}{ψ : ⟦ F ⟧ B → B}
             {init : ⟦ F ⟧ μ → μ}(i : IsInitial C[ F ]Alg (to-Algebra init)) →
             (f : C[ F ]Alg [ to-Algebra ϕ , to-Algebra ψ ]) →
             C[ F ]Alg [ i .! ≈ C[ F ]Alg [ f ∘ i .! ] ]
fusionprop {F} i f = i .!-unique (C[ F ]Alg [ f ∘ i .! ])
\end{code}
The `fusion law':
\begin{code}
fusion : {F : Container 0ℓ 0ℓ}{A B : Set}{a : ⟦ F ⟧ A → A}{b : ⟦ F ⟧ B → B}
         (h : A → B) → h ∘ a ≡ b ∘ map h →  ⦅ b ⦆ ≡ h ∘ ⦅ a ⦆
fusion h p = funext λ x → fusionprop initial-in (
               record { f = h ; commutes = λ {y} → cong-app p y }
             ) {x}
\end{code}
