\paragraph{Universal property of anamorphisms}
This module proves some property of anamorphisms.
\begin{code}
{-# OPTIONS --guardedness #-}
module agda.term.terminal  where
open import Data.Container using (Container; map) renaming (⟦_⟧ to I⟦_⟧)
\end{code}
\begin{code}[hide]
open import Level
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import agda.funct.funext
open import agda.term.termcoalg
open ν
open import Function
open import Data.Product using (_,_; Σ)
\end{code}
The forward direction of the \textit{universal property of unfolds} \cite{Harper2011}:
\begin{code}
universal-propₗ : {F : Container 0ℓ 0ℓ}{C : Set}(c : C → I⟦ F ⟧ C)(h : C → ν F) →
                 h ≡ A⟦ c ⟧ → out ∘ h ≡ map h ∘ c
universal-propₗ c h eq = begin
    out ∘ h
  ≡⟨ cong (_∘_ out) eq ⟩
    out ∘ A⟦ c ⟧
  ≡⟨⟩
    map A⟦ c ⟧ ∘ c
  ≡⟨ cong (_∘ c) (cong map (sym eq)) ⟩
    map h ∘ c
  ∎
\end{code}
\begin{code}[hide]
--universal-propᵣ : {C : Set}(c : C → ⟦ F ⟧ C)(h : C → ν F) →
--                            out ∘ h ≡ map h ∘ c → h ≡ ⟦ c ⟧
--universal-propᵣ c h eq = {!!}
\end{code}
The \textit{computation law} \cite{Harper2011}:
\begin{code}
comp-law : {F : Container 0ℓ 0ℓ}{C : Set}(c : C → I⟦ F ⟧ C) → out ∘ A⟦ c ⟧ ≡ map A⟦ c ⟧ ∘ c
comp-law c = refl
\end{code}
The \textit{reflection law} \cite{Harper2011}:
SOMETHING ABOUT TERMINATION.
\begin{code}
{-# NON_TERMINATING #-}
reflection : {F : Container 0ℓ 0ℓ}(x : ν F) → A⟦ out ⟧ x ≡ x
reflection x = out-injective (begin
    out (A⟦ out ⟧ x)
  ≡⟨⟩
    map A⟦ out ⟧ (out x)
  ≡⟨⟩
    op , A⟦ out ⟧ ∘ ar
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
