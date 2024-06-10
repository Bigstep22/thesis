\paragraph{Endofunctors}
I define an endofunctor across the category of agda sets, where the functors are extensions of containers.
There is a little bit of unwieldyness as \tt{Sets} defines equality through extensionality but using an implicit parameter.
In order to combine it with \tt{funext} a little bit of unpacking and repacking of the definitions needs to be done.
\begin{code}[hide]
open import Data.Container using (Container; ⟦_⟧; map)
open import Level using (0ℓ)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor using (Endofunctor)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import agda.funct.funext using (funext)
open import Function
module agda.funct.endo where
\end{code}
\begin{code}
F[_] : (F : Container 0ℓ 0ℓ) → Endofunctor (Sets 0ℓ)
F[ F ] = record { F₀ = ⟦ F ⟧ ; F₁ = map
                ; identity = refl ; homomorphism = refl
                ; F-resp-≈ = λ p → cong₂ map (funext (λ x → p {x})) refl }
\end{code}
