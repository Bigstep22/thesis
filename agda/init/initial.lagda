\paragraph{Universal properties of catamorphisms and initiality}
This module defines a function and shows it to be a catamorphism in the category of F-Agebras,
by module proving some properties of catamorphisms and is showing that \tt{(μ F, in')} is initial.
\begin{code}
module agda.init.initial where
open import Data.W using () renaming (sup to in'; foldr to ⦅_⦆) public
\end{code}
\begin{code}[hide]
open import Level using (0ℓ; Level) renaming (suc to lsuc) public
open import Function using (_∘_; _$_; id; const) public
open import Data.Product using (_,_) public
open import Data.Container using (Container; μ; ⟦_⟧; map; _▷_) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; cong-app; subst; trans) public
open Eq.≡-Reasoning public
open import Categories.Category renaming (Category to Cat)
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
open import Categories.Object.Initial
open F-Algebra-Morphism
open F-Algebra
open import agda.funct.funext
open import agda.funct.endo
\end{code}
A shorthand for the Category of F-Algebras.
\begin{code}
C[_]Alg : (F : Container 0ℓ 0ℓ) → Cat (lsuc 0ℓ) 0ℓ 0ℓ
C[ F ]Alg = F-Algebras F[ F ]
\end{code}
A shorthand for an F-Algebra homomorphism:
\begin{code}
_Alghom[_,_] : {X Y : Set}(F : Container 0ℓ 0ℓ)(x : ⟦ F ⟧ X → X)(Y : ⟦ F ⟧ Y → Y) → Set
F Alghom[ x , y ] = C[ F ]Alg [ to-Algebra x , to-Algebra y ]
\end{code}
A candidate function is defined, this will be proved to be a catamorphism through the proof of initiality:
\begin{code}
--⦅_⦆ : {F : Container 0ℓ 0ℓ}{X : Set} → (⟦ F ⟧ X → X) → μ F → X
--⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)
--⦅_⦆ = foldr -- from Data.W
\end{code}
It is shown that any $\catam{\_}$ is a valid F-Algebra homomorphism from \tt{in'} to any other object \tt{a};
i.e. the forward direction of the \textit{universal property of folds} \citep{Harper2011}.
This constitutes a proof of existence:
\begin{code}
univ-to : {F : Container 0ℓ 0ℓ}{X : Set}{a : ⟦ F ⟧ X → X}{h : μ F → X} →
                  h ≡ ⦅ a ⦆ → h ∘ in' ≡ a ∘ map h
univ-to refl = refl
\end{code}
It is shown that any other valid F-Algebra homomorphism from \tt{in'} to \tt{a} is equal to the $\catam{\_}$ function defined;
i.e. the backwards direction of the \textit{universal property of folds} \citep{Harper2011}.
This constitutes a proof of uniqueness:
\begin{code}
univ-from : {F : Container 0ℓ 0ℓ}{X : Set}(a : ⟦ F ⟧ X → X)(h : μ F → X) →
                            h ∘ in' ≡ a ∘ map h → (x : μ F) → h x ≡ ⦅ a ⦆ x
univ-from a h eq (in' x@(op , ar)) = begin
      (h ∘ in') x
    ≡⟨ cong-app eq x ⟩
      (a ∘ map h) x
    ≡⟨⟩
      a (op , h ∘ ar)
    ≡⟨ cong (λ f → a (op , f)) (funext $ univ-from a h eq ∘ ar) ⟩
      a (op , ⦅ a ⦆ ∘ ar)
    ≡⟨⟩
      (a ∘ map ⦅ a ⦆) x
    ≡⟨⟩
      (⦅ a ⦆ ∘ in') x
    ∎
\end{code}
\begin{code}
\end{code}
The two previous proofs, constituting a proof of existence and uniqueness, are combined to show that \tt{(μ F, in')} is initial:
\begin{code}
initial-in : {F : Container 0ℓ 0ℓ} → IsInitial C[ F ]Alg (to-Algebra in')
initial-in = record { ! = λ {A} →
                                record {
                                       f = ⦅ α A ⦆
                                       ; commutes = λ {x} → cong-app (univ-to {_}{_}{α A} refl) x  }
                    ; !-unique = λ {A} fhom {x} → sym $ univ-from (α A) (f fhom) (funext (λ y → commutes fhom)) x }
\end{code}
The \textit{computation law} \citep{Harper2011}:
\begin{code}
comp-law : {F : Container 0ℓ 0ℓ}{A : Set}(a : ⟦ F ⟧ A → A) → ⦅ a ⦆ ∘ in' ≡ a ∘ map ⦅ a ⦆
comp-law a = refl
\end{code}
The \textit{reflection law} \citep{Harper2011}:
\begin{code}
reflection : {F : Container 0ℓ 0ℓ}(y : μ F) → ⦅ in' ⦆ y ≡ y
reflection (in' (op , ar)) = begin
     ⦅ in' ⦆ (in' (op , ar))
   ≡⟨⟩ -- Dfn of ⦅_⦆
     in' (op , ⦅ in' ⦆ ∘ ar)
   ≡⟨ cong (λ x → in' (op , x)) (funext (reflection ∘ ar)) ⟩
     in' (op , ar)
   ∎

reflection-law : {F : Container 0ℓ 0ℓ} → ⦅ in' ⦆ ≡ id
reflection-law {F} = funext (reflection {F})
\end{code}
