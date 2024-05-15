\paragraph{Terminal coalgebras and anamorphisms}
This module defines a datatype and shows it to be initial; and a function and shows it to be an anamorphism in the category of F-Coalgebras.
Specifically, it is shown that \tt{($\nu$, out)} is terminal.
\begin{code}
{-# OPTIONS --guardedness #-}
module agda.term.terminal where
open import Agda.Builtin.Sigma public
open import Level using (0ℓ; Level) renaming (suc to lsuc) public
open import Data.Container using (Container; ⟦_⟧; map; _▷_) public
open Container
open import Function using (_∘_; _$_; id; const) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; cong-app; subst; trans) public
open Eq.≡-Reasoning public
\end{code}
\begin{code}[hide]
open import Categories.Category renaming (Category to Cat)
open import Categories.Functor.Coalgebra
open import Categories.Category.Construction.F-Coalgebras
open F-Coalgebra-Morphism
open F-Coalgebra
open import Categories.Object.Terminal
open import agda.funct.funext
open import agda.funct.endo
open import Codata.Guarded.M using (head; tail) renaming (M to ν; unfold to A⟦_⟧) public
open import Data.Product.Properties
\end{code}
A shorthand for the Category of F-Coalgebras:
\begin{code}
C[_]CoAlg : (F : Container 0ℓ 0ℓ) → Cat (lsuc 0ℓ) 0ℓ 0ℓ
C[ F ]CoAlg = F-Coalgebras F[ F ]
\end{code}
A candidate terminal datatype and anamorphism function are defined, they will be proved to be so later on this module:
\begin{code}
--A⟦_⟧ : {F : Container 0ℓ 0ℓ}{X : Set} → (X → ⟦ F ⟧ X) → X → ν F
--out (A⟦ c ⟧ x) = let (op , ar) = c x in
--                     (op , A⟦ c ⟧ ∘ ar)
\end{code}
\begin{code}[hide]

--{-# ETA ν #-} -- Seems to cause a hang (or major slowdown) in compilation
              -- in combination with reflection,
              -- have a chat with Casper
out : {F : Container 0ℓ 0ℓ} → ν F → ⟦ F ⟧ (ν F)
out nu = head nu , tail nu
record _≣_ {F : Container _ _}(a b : ν F) : Set where
    coinductive; field
      outfst : head a ≡ head b
      outsnd : (x : Position F (head a)) →
               tail a x ≣ tail b (subst (Container.Position F) outfst x)
open _≣_ public
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Substitutive)
module _ {F : Container 0ℓ 0ℓ} where
  refl' : Reflexive (_≣_ {F})
  outfst (refl') = refl
  outsnd (refl') x = refl'

  sym' : Symmetric (_≣_ {F})
  outfst (sym' eq) = sym (outfst eq)
  outsnd (sym' eq) x with sym (outfst eq)
  outsnd (sym' eq) x | eq2 = sym' {!!}

  trans' : Transitive (_≣_ {F})
  outfst (trans' ij jk) = trans (outfst ij) (outfst jk)
  outsnd (trans' ij jk) x = trans' (outsnd ij x) {!!}
\end{code}
It is shown that any $\anam{\_}$ is a valid F-Coalgebra homomorphism from \tt{out} to any other object \tt{a};
i.e. the forward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of existence:
\begin{code}
univ-to : {F : Container 0ℓ 0ℓ}{C : Set}(h : C → ν F)
          {c : C → ⟦ F ⟧ C} → h ≡ A⟦ c ⟧ → out ∘ h ≡ map h ∘ c
univ-to _ refl = refl
\end{code}
It is shown that any other valid F-Coalgebra homomorphism from \tt{out} to \tt{a} is equal to the $\anam{\_}$ defined;
i.e. the backward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of uniqueness.
This uses \tt{out} injectivity.
Currently, Agda's termination checker does not seem to notice that the proof in question terminates:
\begin{code}
univ-from : {F : Container _ _}{C : Set}(h : C → ν F){c : C → ⟦ F ⟧ C} →
                            out ∘ h ≡ map h ∘ c → (x : C) → h x ≣ A⟦ c ⟧ x
outfst (univ-from h eq x) = ,-injectiveˡ (cong-app eq x)
outsnd (univ-from {F} h {c} eq x) y = univ-from (const $ tail (h x) y)
    (funext λ z → begin
      (out ∘ const (tail (h x) y)) z
      ≡⟨ refl ⟩
      const (out (tail (h x) y)) z
      ≡⟨ ? ⟩
      ((_, (const $ tail (h x) y)) ∘ fst ∘ c) z
      ≡⟨ refl ⟩
      (λ x₁ → fst (c x₁) , (λ x₂ → tail (h x) y)) z
      ≡⟨ refl ⟩
      (map (const (tail (h x) y)) ∘ c) z
    ∎)
    (snd (c x) (subst (Position F) (outfst (univ-from h eq x)) y))
--  out-injective (begin
--      (out ∘ h) x
--    ≡⟨ cong (λ f → f x) eq ⟩
--      map h (op , ar)
--    ≡⟨⟩
--      (op , h ∘ ar)
--    ≡⟨ cong (λ f → op , f) (funext $ univ-from h eq ∘ ar) ⟩ -- induction
--      (op , A⟦ c ⟧ ∘ ar)
--    ≡⟨⟩ -- Definition of ⟦_⟧
--      (out ∘ A⟦ c ⟧) x
--    ∎)
\end{code}
The two previous proofs, constituting a proof of existence and uniqueness, are combined to show that \tt{($\nu$ F, out)} is terminal:
\begin{code}
--terminal-out : {F : Container 0ℓ 0ℓ} → IsTerminal C[ F ]CoAlg (to-Coalgebra out)
--terminal-out = record { ! = λ {A} → record {
--                                    f = A⟦ α A ⟧
--                                    ; commutes = λ {x} → cong-app (univ-to A⟦ α A ⟧ {α A} refl) x }
--                      ; !-unique = λ {A} fhom {x} → sym (univ-from (f fhom) {α A} (funext (λ y → commutes fhom {y})) x) }
\end{code}
The \textit{computation law} \cite{Harper2011}:
\begin{code}
computation-law : {F : Container 0ℓ 0ℓ}{C : Set}(c : C → ⟦ F ⟧ C) → out ∘ A⟦ c ⟧ ≡ map A⟦ c ⟧ ∘ c
computation-law c = refl
\end{code}
The \textit{reflection law} \cite{Harper2011}:
SOMETHING ABOUT TERMINATION.
\begin{code}
reflection : {F : Container 0ℓ 0ℓ}(x : ν F) → A⟦ out ⟧ x ≣ x
outfst (reflection x) = refl
outsnd (reflection x) y = reflection (snd (out x) y)
\end{code}
