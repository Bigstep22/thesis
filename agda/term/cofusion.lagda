\subsubsection{Terminal F-Coalgebra fusion}
This section proves the categorical fusion property.
From it, it extracts the `fusion law' as it was described by \cite{Harper2011}; which uses non-categorical type definitions.
The categorical fusion property:
\begin{code}[hide]
{-# OPTIONS --guardedness #-}
module agda.term.cofusion  where
open import agda.term.terminal
open import agda.funct.endo
open import Categories.Category renaming (Category to Cat)
open import Categories.Functor.Coalgebra
open import Categories.Object.Terminal
open IsTerminal
\end{code}
\begin{code}
fusionprop : {F : Container 0ℓ 0ℓ}{C D ν : Set}
             {ϕ : C → ⟦ F ⟧ C}{ψ : D → ⟦ F ⟧ D}{term : ν → ⟦ F ⟧ ν}
             (i : IsTerminal C[ F ]CoAlg (to-Coalgebra term))
             (f : C[ F ]CoAlg [ to-Coalgebra ψ , to-Coalgebra ϕ ]) →
             C[ F ]CoAlg [ i .! ≈ C[ F ]CoAlg [ i .! ∘ f ] ]
fusionprop {F} i f = i .!-unique (C[ F ]CoAlg [ i .! ∘ f ])
\end{code}
The `fusion law':
\begin{code}
fusion : {F : Container 0ℓ 0ℓ}{C D : Set}
         {c : C → ⟦ F ⟧ C}{d : D → ⟦ F ⟧ D}(h : C → D) →
         ({x : C} → (d ∘ h) x ≡ (map h ∘ c) x) →
         (x : C) → A⟦ c ⟧ x ≡ (A⟦ d ⟧ ∘ h) x
fusion h comm x = fusionprop terminal-out (
                    record {f = h ; commutes = comm}
                  ) {x}
\end{code}
