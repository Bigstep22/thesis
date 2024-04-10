\paragraph{Terminal coalgebras and anamorphisms}
This module defines a datatype and shows it to be initial; and a function and shows it to be an anamorphism in the category of F-Coalgebras.
Specifically, it is shown that \tt{($\nu$, out)} is terminal.
\begin{code}
{-# OPTIONS --guardedness #-}
module agda.term.termcoalg where
open import Categories.Category renaming (Category to Cat)
open import Data.Container using (Container; map) renaming (⟦_⟧ to I⟦_⟧)
\end{code}
\begin{code}[hide]
open import Level
open import Function
open import Data.Product using (_,_; Σ)
open import Categories.Functor.Coalgebra
open import Categories.Category.Construction.F-Coalgebras
open F-Coalgebra-Morphism
open F-Coalgebra
open import Categories.Object.Terminal
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning
open import agda.funct.funext
open import agda.funct.endo
\end{code}
A shorthand for the Category of F-Coalgebras:
\begin{code}
C[_]CoAlg : (F : Container 0ℓ 0ℓ) → Cat (suc 0ℓ) 0ℓ 0ℓ
C[ F ]CoAlg = F-Coalgebras F[ F ]
\end{code}
A shorthand for an F-Coalgebra homomorphism:
\begin{code}
_CoAlghom[_,_] : {X Y : Set}(F : Container 0ℓ 0ℓ)(x : X → I⟦ F ⟧ X)(Y : Y → I⟦ F ⟧ Y) → Set
F CoAlghom[ x , y ] = C[ F ]CoAlg [ to-Coalgebra x , to-Coalgebra y ]
\end{code}
A candidate terminal datatype and anamorphism function are defined, they will be proved to be so later on this module:
\begin{code}
record ν (F : Container 0ℓ 0ℓ) : Set where
  coinductive
  field out : I⟦ F ⟧ (ν F)
open ν
⟦_⟧ : {F : Container 0ℓ 0ℓ}{X : Set} → (X → I⟦ F ⟧ X) → X → ν F
out (⟦ c ⟧ x) = (λ (op , ar) → op , ⟦ c ⟧ ∘ ar) (c x)
\end{code}
\begin{code}[hide]
--{-# ETA ν #-} -- Seems to cause a hang (or major slowdown) in compilation
              -- in combination with reflection,
              -- have a chat with Casper
\end{code}
Injectivity of the \tt{out} constructor is postulated, I have not found a way to prove this, yet.
\begin{code}
postulate out-injective : {F : Container 0ℓ 0ℓ}{x y : ν F} → out x ≡ out y → x ≡ y
--out-injective eq = funext ?
\end{code}
It is shown that any $\anam{\_}$ is a valid F-Coalgebra homomorphism from \tt{out} to any other object \tt{a}.
This constitutes a proof of existence:
\begin{code}
valid-fcoalghom : {F : Container 0ℓ 0ℓ}{X : Set}(a : X → I⟦ F ⟧ X) → F CoAlghom[ a , out ]
valid-fcoalghom {X} a = record { f = ⟦ a ⟧ ; commutes = refl }
\end{code}
It is shown that any other valid F-Coalgebra homomorphism from \tt{out} to \tt{a} is equal to the $\anam{\_}$ defined.
This constitutes a proof of uniqueness.
This uses \tt{out} injectivity.
SOMETHING ABOUT TERMINATION CHECKING.
\begin{code}
{-# NON_TERMINATING #-}
isunique : {F : Container 0ℓ 0ℓ}{X : Set}{c : X → I⟦ F ⟧ X}(fhom : F CoAlghom[ c , out ])
           (x : X) → ⟦ c ⟧ x ≡ fhom .f x
isunique {_}{_}{c} fhom x = out-injective (begin
        (out ∘ ⟦ c ⟧) x
    ≡⟨⟩ -- Definition of ⟦_⟧
        map ⟦ c ⟧ (c x)
    ≡⟨⟩
        (λ(op , ar) → (op , ⟦ c ⟧ ∘ ar)) (c x)
    -- Same issue as with the proof of reflection it seems...
    ≡⟨ cong (λ f → op , f) (funext $ isunique fhom ∘ ar) ⟩ -- induction
        (op , fhom .f ∘ ar)
    ≡⟨⟩
        map (fhom .f) (c x)
    ≡⟨⟩ -- Definition of composition
        (map (fhom .f) ∘ c) x
    ≡⟨ sym $ fhom .commutes ⟩
        (out ∘ fhom .f) x
  ∎)
  where op = Σ.proj₁ (c x)
        ar = Σ.proj₂ (c x)
\end{code}
The two previous proofs, constituting a proof of existence and uniqueness, are combined to show that \tt{($\nu$ F, out)}
\begin{code}
terminal-out : {F : Container 0ℓ 0ℓ} → IsTerminal C[ F ]CoAlg (to-Coalgebra out)
terminal-out = record { ! = λ {A} → valid-fcoalghom (A .α)
                      ; !-unique = λ fhom {x} → isunique fhom x }
\end{code}
