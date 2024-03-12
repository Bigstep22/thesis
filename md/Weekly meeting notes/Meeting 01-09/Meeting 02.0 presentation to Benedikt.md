Presentation was alright. I hadn't realized Benedikt's lack of experience in Haskell. He said he got the gist of what I was trying to explain. He also confirmed he'd be part of my thesis project.

I could'be motivated the type of the 'handler' better by just using proper effect handlers rather than using Datatypes a la carte's method doing handlers, useful to know for next time when explaining this system. Both have their benefits: the evaluation is easier to understand using typeclass. The type of the evaluation function is more intuitive from the handler point of view.

The question: 'why does the inlining and the pragmas create an increase in performance in Haskell? In an eager language the speedup can be quite significant, but in Haskell less so but still noticeable, why is that?'. Jaro came up with a much more technical explanation that my 'because no intermediate datastructure', I should ask him more about it because I didn't follow it at the time. 
- Look into Haskell's optimizer, why does inlining and the RULES pragma provide a speedup with church encoding over just implementing and pipelining the functions as is done naively?

Be humble, take the opportunity to learn from your surroundings and be a receptive student.