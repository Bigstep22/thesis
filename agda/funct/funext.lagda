Functional extensionality is postulated using Agda's ExtensionalityImplicit module:
\begin{code}
module agda.funct.funext where
open import Axiom.Extensionality.Propositional
postulate funext : ∀{a b} → Extensionality a b
funexti : ∀{a b} → ExtensionalityImplicit a b
funexti = implicit-extensionality funext
\end{code}
