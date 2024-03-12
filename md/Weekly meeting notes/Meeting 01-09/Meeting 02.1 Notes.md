Speedups with fusion:
- Speedup Part of it: it's easier for the compiler to apply optimizations.
	- Compiler can't do much with datastructures.
	- If you use constructures you allocate.
		- By using a function to represent the data, as opposed to constructors, the compiler can do more optimizations, by doing inlining such.
- On general recursion inlining: there is a paper about join-points. It's a form of recursion that can be inlined.
	- Compiling without continuations paper. (Simon Peyton Jones). Section 5

 Containers:
 - Casper might have meant to use the container representation to create proofs across those.

Vocabulary
- Just write down foreign terms, ask!

For next meeting
- [x] Install Agda: Done using Doom emacs!
- [x] Implement fusion of free monad.
- [ ] Write outline and (sort of) intro of thesis to motivate:
- [ ] Time planning (gantt chart)