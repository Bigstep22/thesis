This week:
- Implemented Stream cochurch fusion.
	- I seemed to accidentally replicate the work of https://doi.org/10.1145/1291151.1291199
- I went through and hand-compiled an example of church fusion, this time with the proper datastructures
	- I did the same for cochurch (but then stream fusion)
- I did a performance comparison of the different implentations.
	- Normal, classical haskell implementation of the pipeline
	- Church-fused pipeline
	- CoChurch-fused pipeline
	- CoChurch-fused pipeline, with tail recursion
		- CoChurch-fusion seems to lend itself well to generating tail-recursive pipelines
	- Hand-compiled, rewritten pipeline, as one function
	- Hand-compiled, with tail recursion.
	- Haskell lists, with their so-called fusion (doesn't seem to work
- I went to Jesper to ask about looking for a new comittee member, this seems to be fine, so I can go an look now.
- I copied over the category definitions from agda-cats
QQ's for this session:
- Is there a way to get the 'native' haskell fusion to work? Under the hood this is just pragma's, in the same way that I'm using them.
- Any recommendations for integrating my work and agda-cats

For the coming week:
- Write a report on my finding with the optimizations.
- Integrate my proof formalizations and agda-cats.
