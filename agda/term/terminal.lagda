\paragraph{Terminal coalgebras and anamorphisms}
This module defines a datatype and shows it to be initial; and a function and shows it to be an anamorphism in the category of F-Coalgebras.
Specifically, it is shown that \tt{($\nu$, out)} is terminal.
\begin{code}
{-# OPTIONS --guardedness #-}
module agda.term.terminal where
open import Agda.Builtin.Sigma public
open import Level using (0ℓ; Level) renaming (suc to lsuc) public
open import Data.Container using (Container; ⟦_⟧; map; _▷_) public
open import Function using (_∘_; _$_; id; const) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; cong-app; subst) public
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
\end{code}
A shorthand for the Category of F-Coalgebras:
\begin{code}
C[_]CoAlg : (F : Container 0ℓ 0ℓ) → Cat (lsuc 0ℓ) 0ℓ 0ℓ
C[ F ]CoAlg = F-Coalgebras F[ F ]
\end{code}
A shorthand for an F-Coalgebra homomorphism:
\begin{code}
_CoAlghom[_,_] : {X Y : Set}(F : Container 0ℓ 0ℓ)(x : X → ⟦ F ⟧ X)(Y : Y → ⟦ F ⟧ Y) → Set
F CoAlghom[ x , y ] = C[ F ]CoAlg [ to-Coalgebra x , to-Coalgebra y ]
\end{code}
A candidate terminal datatype and anamorphism function are defined, they will be proved to be so later on this module:
\begin{code}
record ν (F : Container 0ℓ 0ℓ) : Set where
  coinductive
  field out : ⟦ F ⟧ (ν F)
open ν public

--record _≈_ {F : Container _ _}(a b : ν F) : Set where
--    coinductive
--    field
--      outfst : fst (out a) ≡ fst (out b)
--      outsnd : ∀ (x) → snd (out a) x ≈ snd (out b) (subst (Container.Position F) outfst x)
--open _≈_

--≈-cong : ∀ {F G : Container _ _}{A B : Set}(f : ν F → ν G) {x y : ν F} → x ≈ y → f x ≈ f y
--≈-cong f x = record { outfst = {!x .outfst!} ; outsnd = {!!} }

A⟦_⟧ : {F : Container 0ℓ 0ℓ}{X : Set} → (X → ⟦ F ⟧ X) → X → ν F
out (A⟦ c ⟧ x) = let (op , ar) = c x in
                     (op , A⟦ c ⟧ ∘ ar)
\end{code}
\begin{code}[hide]
--{-# ETA ν #-} -- Seems to cause a hang (or major slowdown) in compilation
              -- in combination with reflection,
              -- have a chat with Casper
\end{code}
It is shown that any $\anam{\_}$ is a valid F-Coalgebra homomorphism from \tt{out} to any other object \tt{a};
i.e. the forward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of existence:
\begin{code}
univ-to : {F : Container 0ℓ 0ℓ}{C : Set}{c : C → ⟦ F ⟧ C}{h : C → ν F} →
                 h ≡ A⟦ c ⟧ → out ∘ h ≡ map h ∘ c
univ-to refl = refl
\end{code}
Injectivity of the \tt{out} constructor is postulated, I have not found a way to prove this, yet.
\begin{code}
postulate out-injective : {F : Container 0ℓ 0ℓ}{x y : ν F} → out x ≡ out y → x ≡ y
--out-injective eq = funext ?
\end{code}
It is shown that any other valid F-Coalgebra homomorphism from \tt{out} to \tt{a} is equal to the $\anam{\_}$ defined;
i.e. the backward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of uniqueness.
This uses \tt{out} injectivity.
Currently, Agda's termination checker does not seem to notice that the proof in question terminates:
\begin{code}
{-# NON_TERMINATING #-}
univ-from : {F : Container _ _}{C : Set}(c : C → ⟦ F ⟧ C)(h : C → ν F) →
                            out ∘ h ≡ map h ∘ c → (x : C) → h x ≡ A⟦ c ⟧ x
univ-from c h eq x = let (op , ar) = c x in
  out-injective (begin
        (out ∘ h) x
    ≡⟨ cong (λ f → f x) eq ⟩
        (map (h) ∘ c) x
    ≡⟨⟩ -- Definition of composition
        map h (c x)
    ≡⟨⟩
        (op , h ∘ ar)
    ≡⟨ cong (λ f → op , f) (funext $ univ-from c h eq ∘ ar) ⟩ -- induction
        (op , A⟦ c ⟧ ∘ ar)
    ≡⟨⟩
        map A⟦ c ⟧ (c x)
    ≡⟨⟩ -- Definition of ⟦_⟧
        (out ∘ A⟦ c ⟧) x
    ∎)
\end{code}
The two previous proofs, constituting a proof of existence and uniqueness, are combined to show that \tt{($\nu$ F, out)} is terminal:
\begin{code}
terminal-out : {F : Container 0ℓ 0ℓ} → IsTerminal C[ F ]CoAlg (to-Coalgebra out)
terminal-out = record { ! = λ {A} →
                                  record { f = A⟦ α A ⟧ ; commutes = λ {x} → cong-app (univ-to {_}{_}{α A} refl) x }
                      ; !-unique = λ {A} fhom {x} → sym (univ-from (α A) (f fhom) (funext (λ y → commutes fhom {y})) x) }
\end{code}
The \textit{computation law} \cite{Harper2011}:
\begin{code}
comp-law : {F : Container 0ℓ 0ℓ}{C : Set}(c : C → ⟦ F ⟧ C) → out ∘ A⟦ c ⟧ ≡ map A⟦ c ⟧ ∘ c
comp-law c = refl
\end{code}
The \textit{reflection law} \cite{Harper2011}:
SOMETHING ABOUT TERMINATION.
\begin{code}
{-# NON_TERMINATING #-}
reflection : {F : Container 0ℓ 0ℓ}(x : ν F) → A⟦ out ⟧ x ≡ x
reflection x = let (op , ar) = out x in
  out-injective (begin
    out (A⟦ out ⟧ x)
  ≡⟨⟩
    op , A⟦ out ⟧ ∘ ar
  ≡⟨ cong (λ f → op , f) (funext $ reflection ∘ ar) ⟩
    out x
  ∎)
\end{code}
