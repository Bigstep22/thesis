\begin{code}[hide]
module agda.examples.container where
open import Level
open import Data.Product.Base as Prod using (Σ-syntax)
\end{code}
The definition of a container is as follows:
\begin{code}
record Container (s p : Level) : Set (suc (s ⊔ p)) where
  constructor _▷_; field
    Shape    : Set s
    Position : Shape → Set p
\end{code}
A container contains an index set, called \tt{Shape} and also a \tt{Position}, which represent the recursive elements of the container.

Containers can be given a semantics (or extension) in the following manner:
\begin{code}
⟦_⟧ : ∀ {s p ℓ} → Container s p → Set ℓ → Set (s ⊔ p ⊔ ℓ)
⟦ S ▷ P ⟧ X = Σ[ s ∈ S ] (P s → X)
\end{code}
The \tt{X} represents the type of the recursive elements of the container.
