Benedikt: One idea is to do a proof of library fusion's paper generally. Where I would implement it in Agda the encodings and then do proofs of their correctness.

Casper: How would you fuse generalized fold?
Left Khan extensions


Find benchmarks that are representative that you want to fuse and implement their Ch/CoCh encodings as a motivator for the research. Is a good case study for the difficulty of doing so.

Start with the Agda implementation and proof
Then once this is done, create a Haskell deriving clause for deriving these encodings.

First-stage review: Implementation of the Agda encoding and having a motivating example in Haskell/Agda for the performance gains. With a small presentation of the current working state and any lessons/hurdles that I've encountered.
Extensions:
- An overview of the theoretic optimizaitons that are needed to make fusion work (pehaps abstractly, perhaps in Haskell).
- Implementation of the `deriving` keyword for the Ch/CoCh encodings

Agda does build in eta and beta reduction, maybe Haskell does more?

Thesis committee:
- Neil, knows formal methods. Sometimes does PL stuff
- Sebastian jumajic, from algorithmics.
- Mathijs de weerdt.
