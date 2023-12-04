Dates
- I would like to finish my thesis before the summer
- I have (am still doing) a literature survey which means I feel that I'm able to do it within this time frame.
- Planning document: see google sheets

Deliverables First-stage review
- What am I turning in then?
- What is the rubrik for the final thesis grading? I would like it to be able to work backwards from that for my planning.

Topics
- Implementation of fusion for Free monad and Higher-order free monad. (Generalized fold fusion)
	- Enables any functor to become a fusable datatype, which is general in its own way.
	- Is specific only to the Free monad and co., but could be very illustrative as to how to implement this in general for any datatype
- Implementation of `deriving ChFusion`: Implement an easy way of telling the Haskell compiler to generate shortcut Church-encoding fusion code, enabling easy usage of fusion in performance-critical code.
	- Requires investigating the inner-workings of Haskell to efficiently implement this
		- Could be a lot of work, Jaro probably knows something about all this
		- Maybe find out how it is implemented for lists, allows forcing of this same feature for other constructs using pragmas.
	- Is only specific to Haskell, not general theory being generated.

 Haskell fusion
- There seem to be multiple ways to implement inlining (and thereby fusion) in Haskell
	- Using pragmas to forcefully direct the compiler to handle datatypes in certain ways.
	- "GHC is keen to create type-specialised copies of (constraint) polymorphic recursive definitions and to inline the definitions of typeclass methods in the process." (Wu et al., 2015).

Thesis committee members
- Who would be good candidates?
	- Are there good FP people at other universities in Holland?
