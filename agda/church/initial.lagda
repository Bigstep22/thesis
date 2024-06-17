\paragraph{Universal properties of catamorphisms and initiality}
This section proves the universal property of folds.
It takes the definition of \tt{W} types and shows that the $\catam{\_}$ function defined for it is a catamorphism.
This is done by proving that the fold is a unique F-algebra homomorphism to any datatype through a proof of existence and uniqueness:
\begin{equation*}
\forall (C,\phi)\in\alg{F}_0: \exists! \catam{\phi}\in \homm{\tt{Alg}(F)}{\mu F,C}, s.t. \catam{\phi}\circ in = \phi\circ F\catam{\phi}
\end{equation*}
\begin{code}
module agda.church.initial where
open import Data.W using () renaming (sup to in') public
\end{code}
\begin{code}[hide]
open import Level using (0ℓ; Level) renaming (suc to lsuc) public
open import Function using (_∘_; _$_; id; const) public
open import Data.Product using (_,_) public
open import Data.Container using (Container; μ; ⟦_⟧; map; _▷_) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; cong-app; subst; trans) public
open Eq.≡-Reasoning public
open import agda.funct.funext
\end{code}
I define a function below which turns out to be a catamorphism.
This fact is proved in this section through a proof of existence \tt{univ-to} and a proof of uniqueness \tt{univ-from}.
The \tt{fold} function for containers in Agda's stdlib is defined identically and could be imported, omitting this definition.
However, for clarity I'm including the definition here instead of importing it:
\begin{code}
⦅_⦆ : {F : Container 0ℓ 0ℓ}{X : Set} → (⟦ F ⟧ X → X) → μ F → X
⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)
\end{code}
We show that any $\catam{\_}$ is a valid F-Algebra homomorphism from \tt{in'} to any other object \tt{a}
i.e., the forward direction of the \textit{universal property of folds} \citep{Harper2011}:
\begin{equation*}
h = \catam{a} \Longrightarrow h \circ in = a \circ F h
\end{equation*}
This constitutes a proof of existence;
there exists a function (in this case called $\catam{\_}$), that is a valid F-Algebra homomorphism:
\begin{code}
univ-to : {F : Container 0ℓ 0ℓ}{X : Set}{a : ⟦ F ⟧ X → X}{h : μ F → X} →
                  ({x : μ F} → h x ≡ ⦅ a ⦆ x) → {x : ⟦ F ⟧ (μ F)} → (h ∘ in') x ≡ (a ∘ map h) x
univ-to {_}{_}{a}{h} eq {x@(op , ar)} = begin
      h (in' (op , ar))
    ≡⟨ eq ⟩
      ⦅ a ⦆ (in' (op , ar))
    ≡⟨⟩
      a (op , ⦅ a ⦆ ∘ ar)
    ≡⟨ cong (λ f → a (op , f)) (funext λ _ → sym eq) ⟩
      a (op , h ∘ ar)
    ≡⟨⟩
      a (map h x)
    ∎
\end{code}
We show that any other valid F-Algebra homomorphism from \tt{in'} to \tt{a} is equal to the $\catam{\_}$ function defined;
i.e. the backwards direction of the \textit{universal property of folds} \citep{Harper2011}.
\begin{equation*}
h = \catam{a} \Longleftarrow h \circ in = a \circ F h
\end{equation*}
This constitutes a proof of uniqueness;
for any function that is a valid F-Algebra homomorphism (in this case called $h$), it is equal to $\catam{\_}$:
\begin{code}
univ-from : {F : Container 0ℓ 0ℓ}{X : Set}{a : ⟦ F ⟧ X → X}(h : μ F → X) →
            ({x : ⟦ F ⟧ (μ F)} → (h ∘ in') x ≡ (a ∘ map h) x) → {x : μ F} → h x ≡ ⦅ a ⦆ x
univ-from {_}{_}{a} h eq {in' x@(op , ar)} = begin
      (h ∘ in') x
    ≡⟨ eq ⟩
      a (op , h ∘ ar)
    ≡⟨ cong (λ f → a (op , f)) (funext λ _ → univ-from h eq) ⟩
      a (op , ⦅ a ⦆ ∘ ar)
    ≡⟨⟩
      (⦅ a ⦆ ∘ in') x
    ∎
\end{code}
The two previous proofs, constituting a proof of existence and uniqueness, together prove initiality of \tt{(μ F, in')}.
% The \textit{computation law} \citep{Harper2011}:
\begin{code}[hide]
comp-law : {F : Container 0ℓ 0ℓ}{A : Set}{a : ⟦ F ⟧ A → A}{x : ⟦ F ⟧ (μ F)} →
           (⦅ a ⦆ ∘ in') x ≡ (a ∘ map ⦅ a ⦆) x
comp-law = refl
\end{code}
The \textit{reflection law} \citep{Harper2011}:
\begin{code}
reflection : {F : Container 0ℓ 0ℓ}{y : μ F} →
             ⦅ in' ⦆ y ≡ y
reflection {_}{y@(in' (op , ar))} = begin
     ⦅ in' ⦆ y
   ≡⟨⟩ -- Dfn of ⦅_⦆
     in' (op , ⦅ in' ⦆ ∘ ar)
   ≡⟨ cong (λ f → in' (op , f)) (funext λ _ → reflection) ⟩
     in' (op , ar)
   ≡⟨⟩ -- Dfn of y
     y
   ∎
\end{code}
The fusion property, which follows from the backwards direction of the \textit{universal property of folds}:
\begin{code}
fusion : {F : Container 0ℓ 0ℓ}{A B : Set}{a : ⟦ F ⟧ A → A}{b : ⟦ F ⟧ B → B}{h : A → B} →
         ({x : ⟦ F ⟧ A} → (h ∘ a) x ≡ (b ∘ map h) x) → (x : μ F) → (h ∘ ⦅ a ⦆) x ≡ ⦅ b ⦆ x
fusion {_}{_}{_}{a}{b}{h} eq x = univ-from (h ∘ ⦅ a ⦆) eq {x}
\end{code}
