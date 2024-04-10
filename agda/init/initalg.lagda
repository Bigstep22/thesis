\paragraph{Initial algebras and catamorphisms}
\begin{code}[hide]
open import Data.Product using (_,_)
open import Level using (0ℓ; suc)
open import Categories.Functor.Algebra
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning
open import agda.funct.funext using (funext)
open import Function using (_∘_; _$_)
open import agda.funct.endo
open import Data.Container using (Container; μ; ⟦_⟧; map)
open import Categories.Category.Construction.F-Algebras
open import Categories.Object.Initial --C[ F ]Alg
open F-Algebra-Morphism
open F-Algebra
\end{code}
This module defines a function and shows it to be a catamorphism in the category of F-Agebras.
Specifically, it is shown that \tt{(μ F, in')} is initial.
\begin{code}
module agda.init.initalg where
open import Categories.Category renaming (Category to Cat)
open import Data.W using () renaming (sup to in')
\end{code}
A shorthand for the Category of F-Algebras.
\begin{code}
C[_]Alg : (F : Container 0ℓ 0ℓ) → Cat (suc 0ℓ) 0ℓ 0ℓ
C[ F ]Alg = F-Algebras F[ F ]
\end{code}
A shorthand for an F-Algebra homomorphism:
\begin{code}
_Alghom[_,_] : {X Y : Set}(F : Container 0ℓ 0ℓ)(x : ⟦ F ⟧ X → X)(Y : ⟦ F ⟧ Y → Y) → Set
F Alghom[ x , y ] = C[ F ]Alg [ to-Algebra x , to-Algebra y ]
\end{code}
A candidate function is defined, this will be proved to be a catamorphism through the proof of initiality:
\begin{code}
⦅_⦆ : {F : Container 0ℓ 0ℓ}{X : Set} → (⟦ F ⟧ X → X) → μ F → X
⦅ a ⦆ (in' (op , ar)) = a (op , ⦅ a ⦆ ∘ ar)
\end{code}
It is shown that any $\catam{\_}$ is a valid F-Algebra homomorphism from \tt{in'} to any other object \tt{a}.
This constitutes a proof of existence:
\begin{code}
valid-falghom : {F : Container 0ℓ 0ℓ}{X : Set}(a : ⟦ F ⟧ X → X) → F Alghom[ in' , a ]
valid-falghom {X} a = record { f = ⦅ a ⦆ ; commutes = refl }
\end{code}
It is shown that any other valid F-Algebra homomorphism from \tt{in'} to \tt{a} is equal to the $\catam{\_}$ function defined.
This constitutes a proof of uniqueness:
\begin{code}
isunique : {F : Container 0ℓ 0ℓ}{X : Set}{a : ⟦ F ⟧ X → X}(fhom : F Alghom[ in' , a ])(x : μ F) →
           ⦅ a ⦆ x ≡ fhom .f x
isunique {_}{_}{a} fhom (in' (op , ar)) = begin
        ⦅ a ⦆ (in' (op , ar))
    ≡⟨⟩ -- Dfn of ⦅_⦆
        a (op , ⦅ a ⦆ ∘ ar)
    ≡⟨ cong (λ h → a (op , h)) (funext $ isunique fhom ∘ ar) ⟩ -- induction
        a (op , (fhom .f) ∘ ar)
    ≡⟨⟩ -- Dfn of map
        (a ∘ map (fhom .f)) (op , ar)
    ≡⟨ sym $ fhom .commutes ⟩
        (fhom .f ∘ in') (op , ar)
  ∎
\end{code}
The two previous proofs, constituting a proof of existence and uniqueness, are combined to show that \tt{(μ F, in')} is initial:
\begin{code}
initial-in : {F : Container 0ℓ 0ℓ} → IsInitial C[ F ]Alg (to-Algebra in')
initial-in = record { ! = λ {A} → valid-falghom (A .α)
                    ; !-unique = λ fhom {x} → isunique fhom x }
\end{code}
