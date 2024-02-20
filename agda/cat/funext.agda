module cat.funext where
open import Relation.Binary.PropositionalEquality as Eq
open ≡-Reasoning
open import Axiom.Extensionality.Propositional

postulate funext : ∀{a b} → Extensionality a b

funexti : ∀{a b} → ExtensionalityImplicit a b
funexti = implicit-extensionality funext

