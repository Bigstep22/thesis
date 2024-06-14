\subsubsection{Terminal coalgebras and anamorphisms}\label{sec:term}
This section defines a datatype and shows it to be terminal; and a function and shows it to be an anamorphism in the category of F-Coalgebras.
Specifically, it is shown that \tt{($\nu$F, out)} is terminal.
\begin{code}
{-# OPTIONS --guardedness #-}
module agda.cochurch.terminal where
open import Codata.Guarded.M public using (head; tail) renaming (M to ν)
\end{code}
\begin{code}[hide]
open import Agda.Builtin.Sigma public
open import Level using (0ℓ; Level) renaming (suc to lsuc) public
open import Data.Container using (Container; ⟦_⟧; map; _▷_) public
open import Function using (_∘_; _$_; id; const) public
open import Relation.Binary.PropositionalEquality as Eq using
  (_≡_; refl; sym; cong; cong-app; subst) public
open Eq.≡-Reasoning public
open import agda.funct.funext
\end{code}
A candidate anamorphism function is defined, they will be proved to be so later on this module,
Agda's stdlib \tt{unfold} could used but is not for clarity
\begin{code}
A⟦_⟧ : {F : Container 0ℓ 0ℓ}{X : Set} → (X → ⟦ F ⟧ X) → X → ν F
head (A⟦ c ⟧ x) = fst (c x)
tail (A⟦ c ⟧ x) = A⟦ c ⟧ ∘ (snd (c x))
out : {F : Container 0ℓ 0ℓ} → ν F → ⟦ F ⟧ (ν F)
out nu = head nu , tail nu
\end{code}
It is shown that any A$\anam{\_}$ is a valid F-Coalgebra homomorphism from \tt{out} to any other object \tt{a};
i.e. the forward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of existence:
\begin{code}
univ-to : {F : Container 0ℓ 0ℓ}{C : Set}{h : C → ν F}{c : C → ⟦ F ⟧ C} →
                 ({x : C} → h x ≡ A⟦ c ⟧ x) → {x : C} → (out ∘ h) x ≡ (map h ∘ c) x
univ-to {_}{_}{h}{c} eq {x} = let (op , ar) = c x in begin
      out (h x)
    ≡⟨ cong out eq ⟩
      out (A⟦ c ⟧ x)
    ≡⟨⟩
      (op , A⟦ c ⟧ ∘ ar)
    ≡⟨ cong (λ f → op , f) (funext (λ x → sym eq)) ⟩
      (op , h ∘ ar)
    ≡⟨⟩
      map h (c x)
    ∎
\end{code}
Injectivity of the \tt{out} constructor is postulated.
I made a serious attempt to prove the terminality of \tt{M} types in agda through the use of a bisimilation relation,
but at the cutoff moment for the work there was still too much work remaining to warrant continuing it.
Instead, this postulate is used:
\begin{code}
postulate out-injective : {F : Container 0ℓ 0ℓ}{x y : ν F} →
                          out x ≡ out y → x ≡ y
\end{code}
It is shown that any other valid F-Coalgebra homomorphism from \tt{out} to \tt{a} is equal to the A$\anam{\_}$ defined;
i.e. the backward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
This constitutes a proof of uniqueness.
This uses \tt{out} injectivity.
Currently, Agda's termination checker does not seem to notice that the proof in question terminates,
it needs to be rewritten to properly use guardedness:
\begin{code}
{-# NON_TERMINATING #-}
univ-from : {F : Container _ _}{C : Set}(h : C → ν F){c : C → ⟦ F ⟧ C} →
            ({x : C} → (out ∘ h) x ≡ (map h ∘ c) x) → {x : C} →  h x ≡ A⟦ c ⟧ x
univ-from h {c} eq {x} = let (op , ar) = c x in
  out-injective (begin
      (out ∘ h) x
    ≡⟨ eq ⟩
      (op , h ∘ ar)
    ≡⟨ cong (λ f → op , f) (funext $ λ x → univ-from h eq {ar x}) ⟩ -- induction
      (op , A⟦ c ⟧ ∘ ar)
    ≡⟨⟩ -- Definition of ⟦_⟧
      (out ∘ A⟦ c ⟧) x
    ∎)
\end{code}
The two previous proofs, constituting a proof of existence and uniqueness, together prove terminailty of \tt{($\nu$ F, out)}.
The \textit{computation law} \cite{Harper2011}:
\begin{code}
computation-law : {F : Container 0ℓ 0ℓ}{C : Set}(c : C → ⟦ F ⟧ C) →
                  out ∘ A⟦ c ⟧ ≡ map A⟦ c ⟧ ∘ c
computation-law c = refl
\end{code}
The \textit{reflection law} \cite{Harper2011}:
\begin{code}
{-# NON_TERMINATING #-}
reflection : {F : Container 0ℓ 0ℓ}{x : ν F} →
             A⟦ out ⟧ x ≡ x
reflection {_}{x} = let (op , ar) = out x in
  out-injective (begin
    out (A⟦ out ⟧ x)
  ≡⟨⟩
    op , A⟦ out ⟧ ∘ ar
  ≡⟨ cong (λ f → op , f) (funext λ x → reflection {_}{ar x}) ⟩
    out x
  ∎)
\end{code}
The fusion property, which follows from the backwards direction of the \textit{universal property of unfolds}:
\begin{code}
fusion : {F : Container 0ℓ 0ℓ}{C D : Set}{c : C → ⟦ F ⟧ C}{d : D → ⟦ F ⟧ D}(h : C → D) →
         ({x : C} → (d ∘ h) x ≡ (map h ∘ c) x) → (x : C) →  (A⟦ d ⟧ ∘ h) x ≡ A⟦ c ⟧ x
fusion {_}{C}{_}{c}{d} h eq x = univ-from (A⟦ d ⟧ ∘ h) (cong (map A⟦ d ⟧) eq) {x}
\end{code}
