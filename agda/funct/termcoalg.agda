{-# OPTIONS --guardedness #-}
open import funct.container
module funct.termcoalg {F : Container} where
open import Data.Product
open import Level
open import Categories.Category renaming (Category to Cat)
open import Categories.Functor.Coalgebra
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open ≡-Reasoning
open import funct.flaws
open import funct.funext
open import Function
open import funct.endo

open import Categories.Category.Construction.F-Coalgebras
C[_]CoAlg : (F : Container) → Cat (suc 0ℓ) 0ℓ 0ℓ
C[ F ]CoAlg = F-Coalgebras F[ F ]

open import Categories.Object.Terminal C[ F ]CoAlg

_CoAlg[_,_] : {X Y : Set}(F : Container)(x : X → I⟦ F ⟧ X)(Y : Y → I⟦ F ⟧ Y) → Set
F CoAlg[ x , y ] = C[ F ]CoAlg [ to-Coalgebra x , to-Coalgebra y ]


record ν (F : Container) : Set where
  coinductive
  field
    out : I⟦ F ⟧ (ν F)
open ν
⟦_⟧ : {X : Set} → (X → I⟦ F ⟧ X) → X → ν F
out (⟦ c ⟧ x) = (λ (op , ar) → op , ⟦ c ⟧ ∘ ar) (c x)

--{-# ETA ν #-} -- Seems to cause a hang (or major slowdown) in compilation
              -- in combination with reflection,
              -- have a chat with Casper
postulate νExt : {x y : ν F} → (out x ≡ out y) → x ≡ y
--νExt refl = refl

open F-Coalgebra-Morphism
open F-Coalgebra


valid-fcoalghom : {X : Set}(a : X → I⟦ F ⟧ X) → F CoAlg[ a , out ]
valid-fcoalghom {X} a = record { f = ⟦ a ⟧ ; commutes = refl }

{-# NON_TERMINATING #-}
isunique : {X : Set}{c : X → I⟦ F ⟧ X}(fhom : F CoAlg[ c , out ])(x : X) →
           ⟦ c ⟧ x ≡ fhom .f x
isunique {_}{c} fhom x = νExt (begin
                         (out ∘ ⟦ c ⟧) x
                       ≡⟨⟩ -- Definition of ⟦_⟧
                         fmap ⟦ c ⟧ (c x)
                       -- This doesn't terminate becaues I'm doing cong on (flip fmap (c x)), so I'm not recursing on my input....
                       -- Same issue as with the proof of reflection it seems...
                       ≡⟨ cong (flip fmap (c x)) (funext (λ y → isunique fhom y)) ⟩
                         fmap (fhom .f) (c x)
                       ≡⟨⟩ -- Definition of composition
                         (fmap (fhom .f) ∘ c) x
                       ≡⟨ cong-app (sym $ funext (λ x → fhom .commutes {x}))  x ⟩
                         (out ∘ fhom .f) x
                       ∎)


terminal-out : IsTerminal (to-Coalgebra out)
terminal-out = record
             { ! = λ {A} → valid-fcoalghom (A .α)
             ; !-unique = λ fhom {x} → isunique fhom x
             }
