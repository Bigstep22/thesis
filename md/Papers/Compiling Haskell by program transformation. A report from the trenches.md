Simon Peyton Jones (1996)
[[Compiling_Haskell_by_program_transformation.pdf]]
https://www.doi.org/10.1007/3-540-61055-3_27

# Description
Describes, practically, the challenges implementing program transformations in Haskell
- Haskell, at this point, does most of its program transformations in the 'middle-end' using Core-to-core transformations
# Index
- Section 3: Core language description
- Section 4: inlining and beta reduction
- Section 5: transformation of `case` expressions.
- Section 6: One gloval transformation pass, performing and exploiting stricness analysis.
- Section 7: Other main transformation in GHC
- Section 8: Summary of lessons learned from experience.

# Section 3
## Operational reading
- Includes description of the core language
- Heap containing three things:
	- Data values
	- Function values
	- Thunks
- Two most important intuitions are:
	- Let bindings perform head allocation
	- Case expressions perform evaluation
- `f (sin x) y` gets transformed to `let v = sin x in f v y`, where the let creates a thunked computation of its body (in this case `sin x`), long with the needed context information
## Polymorhism
- Is essentially solved by passing along 'type parameters' to polymorphic functions
- Types are not passed around at runtime.
- A bunch of references are given at the end of the section for further optimizations.

# Section 4: Inlining and beta reduction
- TBD


