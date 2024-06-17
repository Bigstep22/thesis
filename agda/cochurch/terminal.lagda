\paragraph{Terminal coalgebras and anamorphisms}\label{sec:term}
This section defines a datatype and shows it to be terminal; and a function and shows it to be an anamorphism in the category of F-Coalgebras.
It takes the definition of \tt{M} types and shows that the A$\anam{\_}$ function defined for it is an anamorphism.
This is done by proving that the A$\anam{\_}$ is a unique F-coalgebra homomorphism from any datatype through a proof of existence and uniqueness:
\begin{equation*}
\forall (C,\phi)\in\coalg{F}_0: \exists! \catam{\phi}\in \homm{\tt{CoAlg}(F)}{C,\nu F}, s.t. out \circ A\anam{\phi} = F A\anam{\phi} \circ \phi
\end{equation*}
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
I define a function below which turns out to be a catamorphism.
This fact is proved in this section through a proof of existence \tt{univ-to} and a proof of uniqueness \tt{univ-from}.
The \tt{unfold} function for containers in Agda's stdlib is defined identically and could be imported, omitting this definition.
However, for clarity I'm including the definition here instead of importing it:
\begin{code}
A⟦_⟧ : {F : Container 0ℓ 0ℓ}{X : Set} → (X → ⟦ F ⟧ X) → X → ν F
head (A⟦ c ⟧ x) = fst (c x)
tail (A⟦ c ⟧ x) = A⟦ c ⟧ ∘ (snd (c x))
out : {F : Container 0ℓ 0ℓ} → ν F → ⟦ F ⟧ (ν F)
out nu = head nu , tail nu
\end{code}
We show that any A$\anam{\_}$ is a valid F-CoAlgebra homomorphism from any other object to \tt{out};
i.e. the forward direction of the \textit{universal property of unfolds} \citep{Harper2011}:
\begin{equation*}
h = A\anam{a} \Longrightarrow out \circ h = F h \circ c
\end{equation*}
This constitutes a proof of existence;
there exists a function (in this case called $\anam{\_}$), that is a valid F-Algebra homomorphism:
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
To prove equality between two terminal datatypes a bisimulation relation is needed.
I made an attempt to prove the \tt{univ-from}, \tt{univ-to}, and \tt{reflection} lemmas through the use of a bisimilation relation,
but due to time constraings there was too much work remaining to warrant continuing it.
The final state of this code can be found in \autoref{app:bisim} and is summarized as follows:
\begin{itemize}[noitemsep]
  \item The reflection law was proven (as a bisimilarity)
%   \item The computation law was proven (as a propositional equality)
  \item The termination of the `proof of uniqueness' part of the proof of terminality (also as a bisimilarity)
  \item The plan and execution of restructuring the further code that rests on the above proofs.
  Most likely the use of propositional equalities throughout the following proofs need to be modified to instead use some combination of the bisimilarity and propositional equality in Agda.
\end{itemize}
Instead, we postulate injectivity of the \tt{out} constructor and use propositional equality.
\begin{code}
postulate out-injective : {F : Container 0ℓ 0ℓ}{x y : ν F} →
                          out x ≡ out y → x ≡ y
\end{code}
It is shown that any other valid F-Coalgebra homomorphism from \tt{out} to \tt{a} is equal to the A$\anam{\_}$ defined;
i.e. the backward direction of the \textit{universal property of unfolds} \cite{Harper2011}.
\begin{equation*}
h = A\anam{a} \Longleftarrow out \circ h = F h \circ c
\end{equation*}
This constitutes a proof of uniqueness;
for any function that is a valid F-Algebra homomorphism (in this case called $h$), it is equal to $A\anam{\_}$.
This uses \tt{out} injectivity.
Currently, Agda's termination checker does notice that the proof in question terminates.
The proof needs to be rewritten to properly use guardedness through the use of a bisimilarity:
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
% The \textit{computation law} \cite{Harper2011}:
\begin{code}[hide]
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
