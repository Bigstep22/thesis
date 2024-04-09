module agda.funct.funext where
open import Axiom.Extensionality.Propositional
postulate funext : ∀{a b} → Extensionality a b
funexti : ∀{a b} → ExtensionalityImplicit a b
funexti = implicit-extensionality funext
