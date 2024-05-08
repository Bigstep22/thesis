\paragraph{Terminal coalgebras and anamorphisms}
This module defines a datatype and shows it to be initial; and a function and shows it to be an anamorphism in the category of F-Coalgebras.
Specifically, it is shown that \tt{($\nu$, out)} is terminal.
\begin{code}
{-# OPTIONS --guardedness #-}
module agda.term.termcoalg where
open import Agda.Builtin.Sigma public
open import Level using (0ℓ; Level) renaming (suc to lsuc) public
open import Data.Container using (Container; ⟦_⟧; map; _▷_) public
open import Function using (_∘_; _$_; id; const) public
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; cong-app; subst) public
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
\end{code}
A shorthand for the Category of F-Coalgebras:
\begin{code}
C[_]CoAlg : (F : Container 0ℓ 0ℓ) → Cat (lsuc 0ℓ) 0ℓ 0ℓ
C[ F ]CoAlg = F-Coalgebras F[ F ]
\end{code}
A shorthand for an F-Coalgebra homomorphism:
\begin{code}
_CoAlghom[_,_] : {X Y : Set}(F : Container 0ℓ 0ℓ)(x : X → ⟦ F ⟧ X)(Y : Y → ⟦ F ⟧ Y) → Set
F CoAlghom[ x , y ] = C[ F ]CoAlg [ to-Coalgebra x , to-Coalgebra y ]
\end{code}
A candidate terminal datatype and anamorphism function are defined, they will be proved to be so later on this module:
\begin{code}
record ν (F : Container 0ℓ 0ℓ) : Set where
  coinductive
  field out : ⟦ F ⟧ (ν F)
open ν public

--record _≈_ {F : Container _ _}(a b : ν F) : Set where
--    coinductive
--    field
--      outfst : fst (out a) ≡ fst (out b)
--      outsnd : ∀ (x) → snd (out a) x ≈ snd (out b) (subst (Container.Position F) outfst x)
--open _≈_

--≈-cong : ∀ {F G : Container _ _}{A B : Set}(f : ν F → ν G) {x y : ν F} → x ≈ y → f x ≈ f y
--≈-cong f x = record { outfst = {!x .outfst!} ; outsnd = {!!} }

A⟦_⟧ : {F : Container 0ℓ 0ℓ}{X : Set} → (X → ⟦ F ⟧ X) → X → ν F
out (A⟦ c ⟧ x) = let (op , ar) = c x in
                     (op , A⟦ c ⟧ ∘ ar)
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
valid-fcoalghom : {F : Container 0ℓ 0ℓ}{X : Set}(a : X → ⟦ F ⟧ X) → F CoAlghom[ a , out ]
valid-fcoalghom {X} a = record { f = A⟦ a ⟧ ; commutes = refl }
\end{code}
It is shown that any other valid F-Coalgebra homomorphism from \tt{out} to \tt{a} is equal to the $\anam{\_}$ defined.
This constitutes a proof of uniqueness.
This uses \tt{out} injectivity.
Currently, Agda's termination checker does not seem to notice that the proof in question terminates, a modification
 to $\nu$ might be needed in order ensure proper termination checking for this proof:
\begin{code}
{-# NON_TERMINATING #-}
isunique : {F : Container 0ℓ 0ℓ}{X : Set}{c : X → ⟦ F ⟧ X}(fhom : F CoAlghom[ c , out ]) →
           (x : X) → A⟦ c ⟧ x ≡ fhom .f x
isunique {F}{X}{c} fhom x = let (op , ar) = c x in
  out-injective (begin
        (out ∘ A⟦ c ⟧) x
    ≡⟨⟩ -- Definition of ⟦_⟧
        map A⟦ c ⟧ (c x)
    ≡⟨⟩
        (op , A⟦ c ⟧ ∘ ar)
    ≡⟨ cong (λ f → op , f) (funext $ isunique fhom ∘ ar) ⟩ -- induction
        (op , fhom .f ∘ ar)
    ≡⟨⟩
        map (fhom .f) (c x)
    ≡⟨⟩ -- Definition of composition
        (map (fhom .f) ∘ c) x
    ≡⟨ sym $ fhom .commutes ⟩
        (out ∘ fhom .f) x
  ∎)
\end{code}
The two previous proofs, constituting a proof of existence and uniqueness, are combined to show that \tt{($\nu$ F, out)}
\begin{code}
terminal-out : {F : Container 0ℓ 0ℓ} → IsTerminal C[ F ]CoAlg (to-Coalgebra out)
terminal-out = record { ! = λ {A} → valid-fcoalghom (A .α)
                      ; !-unique = λ fhom {x} → isunique fhom x }
\end{code}
