\paragraph{Terminal coalgebras and anamorphisms}
This module defines a datatype and shows it to be initial; and a function and shows it to be an anamorphism in the category of F-Coalgebras.
Specifically, it is shown that \tt{($\nu$, out)} is terminal.
\begin{code}
{-# OPTIONS --guardedness --with-K #-}
module agda.term.terminal where
open import Agda.Builtin.Sigma public
open import Level using (0ℓ; Level) renaming (suc to lsuc) public
open import Data.Container using (Container; ⟦_⟧;  _▷_) public
open Container
open import Function using (_∘_; _$_; id; const; flip) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; cong-app; subst; trans) public
open import Relation.Binary.PropositionalEquality.Properties
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
open import Codata.Guarded.M using (head; tail) renaming (M to ν) public
open import Data.Product hiding (map)
open import Data.Product.Properties
\end{code}
A shorthand for the Category of F-Coalgebras:
\begin{code}
C[_]CoAlg : (F : Container 0ℓ 0ℓ) → Cat (lsuc 0ℓ) 0ℓ 0ℓ
C[ F ]CoAlg = F-Coalgebras F[ F ]
\end{code}
A candidate terminal datatype and anamorphism function are defined, they will be proved to be so later on this module:
\begin{code}
A⟦_⟧ : {F : Container 0ℓ 0ℓ}{X : Set} → (X → ⟦ F ⟧ X) → X → ν F
head (A⟦ c ⟧ x) = fst (c x)
tail (A⟦_⟧ {F} c x) = A⟦ c ⟧ ∘ snd (c x)
\end{code}
\begin{code}[hide]
map : {F : Container 0ℓ 0ℓ}{X Y : Set}(h : X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
map {F} h (op , ar) = (op , h ∘ ar)

out : {F : Container 0ℓ 0ℓ} → ν F → ⟦ F ⟧ (ν F)
out nu = head nu , tail nu
record _≣_ {F : Container _ _}(a b : ν F) : Set where
    coinductive; field
      outfst : head a ≡ head b
      outsnd : {x : Position F (head a)} →
               tail a x ≣ tail b (subst (Position F) outfst x)
open _≣_ public
postulate nueq : {F : Container 0ℓ 0ℓ}{a b : ν F}(eq : a ≣ b) → a ≡ b
module _ {F : Container 0ℓ 0ℓ} where
  open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Substitutive)
  refl' : Reflexive (_≣_ {F})
  outfst (refl') = refl
  outsnd (refl') = refl'

--  postulate subst' : {ℓ : Level} →  Substitutive (_≣_ {F}) ℓ
--  subst' P eq p = {!!}


  postulate sym' : Symmetric (_≣_ {F})
--  outfst (sym' eq) = sym (outfst eq)
--  outsnd (sym' eq) {x} = sym' (outsnd eq {subst (Position F) (sym (outfst eq)) x})


  postulate trans' : Transitive (_≣_ {F})
--  outfst (trans' ij jk) = trans (outfst ij) (outfst jk)
--  outsnd (trans' {i}{j}{k} ij jk) = trans' (outsnd ij) (trans' (outsnd jk) {!!})
\end{code}
It is shown that any $\anam{\_}$ is a valid F-Coalgebra homomorphism from \tt{out} to any other object \tt{a};
i.e. the forward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of existence:
\begin{code}
univ-to : {F : Container 0ℓ 0ℓ}{C : Set}{h : C → ν F}
          {c : C → ⟦ F ⟧ C}(eq : h ≡ A⟦ c ⟧)(x : C) →
          head (h x) ≡ fst (c x)
univ-to refl _ = refl
univ-to' : {F : Container 0ℓ 0ℓ}{C : Set}{h : C → ν F}
           {c : C → ⟦ F ⟧ C}(eq : h ≡ A⟦ c ⟧) →
           tail ∘ h ≡ λ x → h ∘ snd (c x) ∘ subst (Position F) (univ-to eq x)
univ-to' refl = refl
conv : {F : Container _ _}{C : Set}(h : C → ν F){c : C → ⟦ F ⟧ C} →
       (eq : ∀{x} → out (h x) ≡ map h (c x)) → (x : C) → head (h x) ≡ fst (c x)
conv h eq x = ,-injectiveˡ eq
conv' : {F : Container _ _}{C : Set}(h : C → ν F){c : C → ⟦ F ⟧ C} →
       (eq : ∀{x} → out (h x) ≡ map h (c x)) → ∀(x : C)(y) → tail (h x) y ≣ h (snd (c x) (subst (Position F) (,-injectiveˡ eq) y))
outfst (conv' {F} h {c} eq x y) = {!!}
outsnd (conv' {F} h {c} eq x y) {z} = {!!}
\end{code}
It is shown that any other valid F-Coalgebra homomorphism from \tt{out} to \tt{a} is equal to the $\anam{\_}$ defined;
i.e. the backward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of uniqueness.
This uses \tt{out} injectivity.
Currently, Agda's termination checker does not seem to notice that the proof in question terminates:
\begin{code}
univ-from : {F : Container _ _}{C : Set}(h : C → ν F){c : C → ⟦ F ⟧ C} →
            (eq1 : ∀ {x} → head (h x) ≡ fst (c x)) →
            (eq2 : ∀{x}{y} → tail (h x) y ≣ h (snd (c x) (subst (Position F) eq1 y))) →
            (x : C) → h x ≣ A⟦ c ⟧ x
outfst (univ-from h {c} eq1 eq2 x) = eq1
outsnd (univ-from {F} h {c} eq1 eq2 x) {y} = trans' eq2 $
                         univ-from h eq1 eq2 (snd (c x) (subst (Position F) eq1 y))
--    (const $ tail (h x) y)
--    (λ {x₁} → {!!} )
--    {!!}
--    (snd (c x) (subst (Position F) eq1 y))
--    (λ {x₁} → begin
--        head (tail (h x) (subst (Position F) (sym eq1) y))
--        ≡⟨ cong head eq2 ⟩
--        head (h (snd (c x) (subst (Position F) eq1 (subst (Position F) (sym eq1) y))))
--        ≡⟨ sym $ subst-subst-sym (eq1) ⟩
--        head (h (snd (c x) y))
--        ≡⟨ cong (head ∘ h) {!refl!} ⟩
--        head (h x₁)
--        ≡⟨ eq1 ⟩
--        fst (c x₁)
--        ∎)
--    (λ {x₁}{y₁} → begin
--      tail (tail (h x) (subst (Position F) (sym eq1) y)) y₁
--      ≡⟨ {!!} ⟩
--      tail (h (snd (c x) (subst (Position F) eq1 (subst (Position F) (sym eq1) y))))
--           (subst (Position F ∘ head) eq2 y₁)
--      ≡⟨ eq2 ⟩
--      h (snd (c (snd (c x) (subst (Position F) eq1 (subst (Position F) (sym eq1) y))))
--        (subst (Position F) eq1 (subst (Position F ∘ head) eq2 y₁)))
--      ≡⟨ cong (λ f → h (snd (c (snd (c x) (subst (Position F) eq1 (subst (Position F) (sym eq1) y)))) (subst (Position F) eq1 f))) (sym $ subst-∘ eq2) ⟩
--      h (snd (c (snd (c x) (subst (Position F) eq1 (subst (Position F) (sym eq1) y))))
--        (subst (Position F) eq1 (subst (Position F ∘ head) eq2 y₁)))
--      ≡⟨ {!!} ⟩
--      h (snd (c x) (subst (Position F) eq1 (subst (Position F) (sym eq1) y)))
--      ≡⟨ cong (h ∘ snd (c x)) (subst-subst-sym eq1) ⟩
--      h (snd (c x) y)
--      ≡⟨ cong (h ∘ snd (c x)) (sym $ subst-subst-sym eq1) ⟩
--      h (snd (c x) (subst (Position F) eq1 (subst (Position F) (sym eq1) y)))
--      ≡⟨ sym eq2 ⟩
--      tail (h x) (subst (Position F) (sym eq1) y)
--      ∎)
--    (snd (c x) y)
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
reflection' : {F : Container 0ℓ 0ℓ}(x : ν F) → A⟦ out ⟧ x ≣ x
outfst (reflection' x) = refl
outsnd (reflection' x) {y} = reflection' (snd (out x) y)
reflection : {F : Container 0ℓ 0ℓ}(x : ν F) → A⟦ out ⟧ x ≡ x
reflection = nueq ∘ reflection'
\end{code}
