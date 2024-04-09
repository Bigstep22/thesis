\paragraph{Functional Extensionality}
We postulate functional extensionality.
This is done through Agda's builting Extensionality module:
\begin{code}
module agda.funct.funext where
open import Axiom.Extensionality.Propositional
postulate funext : ∀{a b} → Extensionality a b
funexti : ∀{a b} → ExtensionalityImplicit a b
funexti = implicit-extensionality funext
\end{code}
