module cat.funext where
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning

postulate funext  : {X : Set}{Y : X → Set}{f g : (x : X) → Y x} →
                    (∀ x → f x ≡ g x) → f ≡ g
postulate funexti : {X : Set}{Y : X → Set}{f g : {x : X} → Y x} →
                    (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g
-- See https://stackoverflow.com/a/56423455 as to why funexti(mplicit) is written this way, is this a weakness in the typechecker?
