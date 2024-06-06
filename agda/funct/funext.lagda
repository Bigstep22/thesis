\paragraph{Functional Extensionality}
We postulate functional extensionality.
This is done through Agda's builtin Extensionality module:
\begin{code}[hide]
module agda.funct.funext where
open import Axiom.Extensionality.Propositional
\end{code}
\begin{code}
postulate funext : ∀{a b} → Extensionality a b
funexti : ∀{a b} → ExtensionalityImplicit a b
funexti = implicit-extensionality funext
\end{code}
