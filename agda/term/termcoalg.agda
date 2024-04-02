{-# OPTIONS --guardedness #-}
module term.termcoalg where
open import Data.Container renaming (⟦_⟧ to I⟦_⟧; refl to C-refl; sym to C-sym)
open import Level
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

--{-# ETA ν #-} -- Seems to cause a hang (or major slowdown) in compilation
              -- in combination with reflection,
              -- have a chat with Casper
postulate νExt : {F : Container 0ℓ 0ℓ}{x y : ν F} → (out x ≡ out y) → x ≡ y
--νExt refl = refl

open F-Coalgebra-Morphism
open F-Coalgebra


valid-fcoalghom : {F : Container 0ℓ 0ℓ}{X : Set}(a : X → I⟦ F ⟧ X) → F CoAlghom[ a , out ]
valid-fcoalghom {X} a .f = ⟦ a ⟧
valid-fcoalghom {X} a .commutes = refl

{-# NON_TERMINATING #-}
isunique : {F : Container 0ℓ 0ℓ}{X : Set}{c : X → I⟦ F ⟧ X}(fhom : F CoAlghom[ c , out ])(x : X) →
           ⟦ c ⟧ x ≡ fhom .f x
isunique {_}{_}{c} fhom x = νExt (begin
                         (out ∘ ⟦ c ⟧) x
                       ≡⟨⟩ -- Definition of ⟦_⟧
                         fmap ⟦ c ⟧ (c x)
                       ≡⟨⟩
                         (λ(op , ar) → (op , ⟦ c ⟧ ∘ ar)) (c x)
                       -- Same issue as with the proof of reflection it seems...
                       ≡⟨ cong (λ f → op , f) (funext $ isunique fhom ∘ ar) ⟩ -- induction
                         (op , fhom .f ∘ ar)
                       ≡⟨⟩
                         fmap (fhom .f) (c x)
                       ≡⟨⟩ -- Definition of composition
                         (fmap (fhom .f) ∘ c) x
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
