\begin{code}
{-# OPTIONS --guardedness #-}
module agda.term.termcoalg where
open import Data.Container using (Container; map) renaming (⟦_⟧ to I⟦_⟧)
open import Level
open import Data.Product using (_,_; Σ)
open import Level
open import Categories.Category renaming (Category to Cat)
open import Categories.Functor.Coalgebra
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning
--open import funct.flaws
open import agda.funct.funext
open import Function
open import agda.funct.endo

open import Categories.Category.Construction.F-Coalgebras
C[_]CoAlg : (F : Container 0ℓ 0ℓ) → Cat (suc 0ℓ) 0ℓ 0ℓ
C[ F ]CoAlg = F-Coalgebras F[ F ]

open import Categories.Object.Terminal --C[ F ]CoAlg

_CoAlghom[_,_] : {X Y : Set}(F : Container 0ℓ 0ℓ)(x : X → I⟦ F ⟧ X)(Y : Y → I⟦ F ⟧ Y) → Set
F CoAlghom[ x , y ] = C[ F ]CoAlg [ to-Coalgebra x , to-Coalgebra y ]


record ν (F : Container 0ℓ 0ℓ) : Set where
  coinductive
  field
    out : I⟦ F ⟧ (ν F)
open ν
⟦_⟧ : {F : Container 0ℓ 0ℓ}{X : Set} → (X → I⟦ F ⟧ X) → X → ν F
out (⟦ c ⟧ x) = (λ (op , ar) → op , ⟦ c ⟧ ∘ ar) (c x)
--{-# INJECTIVE out #-}
--{-# INJECTIVE ν #-}

--{-# ETA ν #-} -- Seems to cause a hang (or major slowdown) in compilation
              -- in combination with reflection,
              -- have a chat with Casper
postulate out-injective : {F : Container 0ℓ 0ℓ}{x y : ν F} → out x ≡ out y → x ≡ y
--out-injective eq = funext ?
--out-injective {F}{x}{y} eq = refl
--out-injective : ∀ {C : Container 0ℓ 0ℓ}{s t : Shape C} {f : Position C s → ν C} {g} →
--                 out (s , f) ≡ out (t , g) → s ≡ t
--νExt refl = refl

open F-Coalgebra-Morphism
open F-Coalgebra


valid-fcoalghom : {F : Container 0ℓ 0ℓ}{X : Set}(a : X → I⟦ F ⟧ X) → F CoAlghom[ a , out ]
valid-fcoalghom {X} a .f = ⟦ a ⟧
valid-fcoalghom {X} a .commutes = refl

{-# NON_TERMINATING #-}
isunique : {F : Container 0ℓ 0ℓ}{X : Set}{c : X → I⟦ F ⟧ X}(fhom : F CoAlghom[ c , out ])(x : X) →
           ⟦ c ⟧ x ≡ fhom .f x
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
                       ≡⟨ cong-app (sym $ funext (λ x → fhom .commutes {x}))  x ⟩
                         (out ∘ fhom .f) x
                       ∎)
                       where op = Σ.proj₁ (c x)
                             ar = Σ.proj₂ (c x)


terminal-out : {F : Container 0ℓ 0ℓ} → IsTerminal C[ F ]CoAlg (to-Coalgebra out)
terminal-out = record
             { ! = λ {A} → valid-fcoalghom (A .α)
             ; !-unique = λ fhom {x} → isunique fhom x
             }
\end{code}
