\paragraph{Terminal coalgebras and anamorphisms: bisimulation}
This module defines a datatype and shows it to be initial; and a function and shows it to be an anamorphism in the category of F-Coalgebras.
Specifically, it is shown that \tt{($\nu$, out)} is terminal.
\begin{code}
{-# OPTIONS --guardedness --with-K --allow-unsolved-metas #-}
module agda.cochurch.terminalbisim where
open import Codata.Guarded.M using (head; tail) renaming (M to ν) public
\end{code}
\begin{code}[hide]
open import Agda.Builtin.Sigma public
open import Level using (0ℓ; Level) renaming (suc to lsuc) public
open import Data.Container using (Container; ⟦_⟧;  _▷_) public
open Container
open import Function using (_∘_; _$_; id; const; flip) public
import Relation.Binary.PropositionalEquality.Core as Eq --using (_≡_; refl; sym; cong; cong-app; subst; trans) public
open import Relation.Binary.PropositionalEquality.Properties
open import agda.funct.funext
open import Data.Product hiding (map)
open import Data.Product.Properties
\end{code}
A candidate terminal datatype and anamorphism function are defined, they will be proved to be so later on this module:
\begin{code}
A⟦_⟧ : {F : Container 0ℓ 0ℓ}{X : Set} → (X → ⟦ F ⟧ X) → X → ν F
head (A⟦ c ⟧ x) = proj₁ (c x)
tail (A⟦ c ⟧ x) = A⟦ c ⟧ ∘ snd (c x)
\end{code}
\begin{code}[hide]
map : {F : Container 0ℓ 0ℓ}{X Y : Set}(h : X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
map {F} h (op , ar) = (op , h ∘ ar)

out : {F : Container 0ℓ 0ℓ} → ν F → ⟦ F ⟧ (ν F)
out = < head , tail >
open import Relation.Binary.Core

open Eq using (_≡_; cong; subst)
module _ {F : Container _ _} where
  record _≣_ (a b : ν F) : Set where
    coinductive; field
      outfst : head a ≡ head b
      outsnd : {x : Position F (head a)} →
               tail a x ≣ tail b (subst (Position F) outfst x)
  open _≣_
  open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Substitutive)

  refl : Reflexive _≣_
  outfst (refl) = Eq.refl
  outsnd (refl) = refl

  tailcong : (y : ν F){x z : Position F (head y)}
             (x≡z : x ≡ z) → tail y x ≣ tail y z
  outfst (tailcong y Eq.refl) = Eq.refl
  outsnd (tailcong y Eq.refl) = refl

  trans : Transitive _≣_
  outfst (trans ij jk) = Eq.trans (outfst ij) (outfst jk)
  outsnd (trans {_}{j}{k} ij jk) {x} =
    trans (outsnd ij) $
      subst
        (λ f → _ ≣ tail k f)
        (subst-subst (outfst ij))
        (outsnd jk)

  sym : Symmetric _≣_
  outfst (sym eq) = Eq.sym (outfst eq)
  outsnd (sym {x}{y} eq) {z} =
    sym $ subst
      (λ f → tail x (subst (Position F) (Eq.sym (outfst eq)) z) ≣ tail y f)
      (subst-subst-sym (outfst eq))
      (outsnd eq)
  -- Rewrite this above line like the one in trans'
open _≣_ public
invnueq : {F : Container 0ℓ 0ℓ}{a b : ν F}(_ : a ≡ b) → a ≣ b
invnueq Eq.refl = refl
postulate nueq : {F : Container 0ℓ 0ℓ}{a b : ν F}(eq : a ≣ b) → a ≡ b
--nueq' : {F : Container 0ℓ 0ℓ}{a b : ν F}
--        (eq : head a ≡ head b)(eq' : ∀{x} →
--        tail a x ≣ tail b (subst (Position F) eq x)) → a ≡ b
--nueq' outfst outsnd = {!!}
\end{code}
It is shown that any A$\anam{\_}$ is a valid F-Coalgebra homomorphism from \tt{out} to any other object \tt{a};
i.e. the forward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of existence:
\begin{code}
univ-to : {F : Container 0ℓ 0ℓ}{C : Set}(h : C → ν F)
          {c : C → ⟦ F ⟧ C}(eq : ∀ {x} → h x ≣ A⟦ c ⟧ x)(x : C) →
          head (h x) ≡ proj₁ (c x)
univ-to _ eq _ = outfst eq
univ-to' : {F : Container 0ℓ 0ℓ}{C : Set}{h : C → ν F}
           {c : C → ⟦ F ⟧ C}(eq : ∀ {x} → h x ≣ A⟦ c ⟧ x) → ∀(x : C){y} →
           tail (h x) y ≣ (h ∘ snd (c x) ∘ subst (Position F) (univ-to h eq x)) y
univ-to' {F}{_}{_}{c} eq x {y} = trans (outsnd eq {y}) (sym $ eq)

conv : {F : Container _ _}{C : Set}(h : C → ν F){c : C → ⟦ F ⟧ C} →
       (eq : ∀{x} → out (h x) ≡ map h (c x)) → {x : C} → head (h x) ≡ proj₁ (c x)
conv h eq = ,-injectiveˡ eq
conv' : {F : Container _ _}{C : Set}(h : C → ν F){c : C → ⟦ F ⟧ C} →
       (eq : ∀{x} → out (h x) ≡ map h (c x)) →
       ∀{x}{y} → tail (h x) y ≣ h (snd (c x) (subst (Position F) (,-injectiveˡ eq) y))
outfst (conv' {F} h {c} eq {x} {y}) = {!!}
outsnd (conv' {F} h {c} eq {x} {y}) {z} = {!!}
\end{code}
It is shown that any other valid F-Coalgebra homomorphism from \tt{out} to \tt{a} is equal to the A$\anam{\_}$ defined;
i.e. the backward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of uniqueness.
This uses \tt{out} injectivity.
Currently, Agda's termination checker does not seem to notice that the proof in question terminates:
\begin{code}
univ-from : {F : Container _ _}{C : Set}(h : C → ν F)(c : C → ⟦ F ⟧ C) →
            (eq1 : ∀{x} → head (h x) ≡ proj₁ (c x)) →
            (eq2 : ∀{x y} → tail (h x) y ≣ h (snd (c x) (subst (Position F) eq1 y))) →
            {x : C} → h x ≣ A⟦ c ⟧ x
outfst (univ-from h c eq1 _) = eq1
outsnd (univ-from {F} h c eq1 eq2 {x}) {y} = trans eq2 $ univ-from h c eq1 eq2
  where open ≡-Reasoning
\end{code}
The two previous proofs, constituting a proof of existence and uniqueness, together show terminality of \tt{($\nu$ F, out)}.
The \textit{computation law} \cite{Harper2011}:
\begin{code}
computation-law : {F : Container 0ℓ 0ℓ}{C : Set}{c : C → ⟦ F ⟧ C} →
                  out ∘ A⟦ c ⟧ ≡ map A⟦ c ⟧ ∘ c
computation-law = Eq.refl
\end{code}
The \textit{reflection law} \cite{Harper2011}:
\begin{code}
reflection' : {F : Container 0ℓ 0ℓ}{x : ν F} → A⟦ out ⟧ x ≣ x
outfst (reflection') = Eq.refl
outsnd (reflection') {y} = reflection'
reflection : {F : Container 0ℓ 0ℓ}{x : ν F} → A⟦ out ⟧ x ≡ x
reflection = nueq reflection'
\end{code}
