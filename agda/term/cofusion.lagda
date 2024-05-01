\paragraph{Terminal F-Coalgebra fusion}
This module proves the categorical fusion property.
From it, it extracts a `fusion law' as it was defined by \cite{Harper2011}; which is easier to work with.
This shows that the fusion law does follow from the fusion property.
\begin{code}
{-# OPTIONS --guardedness #-}
module agda.term.cofusion  where
\end{code}
\begin{code}[hide]
open import Data.Container using (Container; map; ⟦_⟧)
open import Categories.Category renaming (Category to Cat)
open import Level
open import Function.Base
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import agda.funct.funext
open import agda.term.termcoalg
open import agda.funct.endo
open import Categories.Functor.Coalgebra
open import Categories.Object.Terminal
open IsTerminal
\end{code}
The categorical fusion property:
\begin{code}
fusionprop : {F : Container 0ℓ 0ℓ}{C D ν : Set}{ϕ : C → ⟦ F ⟧ C}{ψ : D → ⟦ F ⟧ D}{term : ν → ⟦ F ⟧ ν}
             (i : IsTerminal C[ F ]CoAlg (to-Coalgebra term))(f : F CoAlghom[ ψ , ϕ ]) →
             C[ F ]CoAlg [ i .! ≈ C[ F ]CoAlg [ i .! ∘ f ] ]
fusionprop {F} i f = i .!-unique (C[ F ]CoAlg [ i .! ∘ f ])
\end{code}
The `fusion law':
\begin{code}
fusion : {F : Container 0ℓ 0ℓ}{C D : Set}{c : C → ⟦ F ⟧ C}{d : D → ⟦ F ⟧ D}(h : C → D) →
                   d ∘ h ≡ map h ∘ c → A⟦ c ⟧ ≡ A⟦ d ⟧ ∘ h
fusion h p = funext λ x → fusionprop terminal-out (record { f = h ; commutes = λ {y} → cong-app p y }) {x}
\end{code}
