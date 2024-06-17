- [ ] WRITE ABSTRACT
- [x] Read feedback from Casper, write todo's
- [x] Read feedback from Jesper, write todo's
- [x] Order new todo's
- [x] Rewrite initial agda file
- [x] Rewrite terminal agda file
- [x] Casper, Chapter 3: My main comments are about writing style. You tend to present your results and insights in a matter-of-fact manner. But the results are often highly non-obvious. There’s room for helping the reader (much) more.
- [ ] Casper, Chapter 3: The analysis of your results in your evaluation section could also be more in-depth. I’ve added some questions in a note in the PDF, for example.
- [ ] Casper, Chapter 4: I think the point that the theorems enable fusion could be made more clearly if you actually prove that the tail-recursive function you show earlier in the paper is equal to the pipeline
- [x] Casper, Chapter 4: Otherwise, mainly writing things.
- [ ] Casper, Chapter 4: I find it a heavy-going chapter with all the definitions, and relatively little explanation.
- [ ] Casper, Chapter4: I found myself trying to remember the diagrams you were formalizing from Chapter 2. I think it might work better if they were in Chapter 4 where you actually use them instead, so they’re fresh in the readers mind, and so that they provide high-level intuition for all the Agda code there.
- [ ] Jesper, Chapter 4.6: Leest momenteel erg als een verslag van wat jij hebt gedaan, maar dit is niet wat het meest interessant is voor de lezer. Over het algemeen verwacht ik van een discussie-sectie meer reflectie over de resultaten die je hebt bewezen, de toepasbaarheid ervan, en eventueel de beperkingen van de tools die je hebt gebruikt. Ik zou je huidige beschrijving van wat je wel of niet hebt gedaan durven inkorten of zelfs weglaten en in plaats daarvan focusen op de "so what": welke boodschap heb je voor de lezer? Wat weten we nu dat we hiervoor niet wisten? Welke conclusies kan je hieruit trekken?
- [x] Jesper 4.6: " (and terminality of M (ν) types)" => Haakjes zijn niet nodig.  
- [x] Jesper 4.6: "I made a serious attempt" => de lezer heeft hier niet echt een boodschap aan.  
- [x] Jesper 4.6: "postulates that the coinductive datatype is injective" => bedoel je de constructor van het type, of het type zelf?  
- [x] Jesper 4.6: "Its use is well-understood" => well-understood *to be consistent*.  
- [x] Jesper 4.6: "is likely not supported" => Wat bedoel je met "likely"? Het is wel of niet supported, "likely" komt hier niet aan te pas.  
- [x] Jesper 4.6: " It is needed for ..." => needed by you or by Agda?  
- [x] Jesper 4.6: Internal parametricity is een veel ouder idee, oorspronkelijk komt het volgens mij van Guilhem Moulin's paper uit 2012 ([https://ieeexplore.ieee.org/document/6280432](https://ieeexplore.ieee.org/document/6280432)).
- [ ] Jesper, Chapter 4: In hoofdstuk 4 is het momenteel voor mij niet duidelijk wat hoofd- en bij-zaak is. Begin een hoofstuk steeds met een statement van wat het doel/probleem is en hoe je dat in grote lijnen gaat bereiken. Het is me verder niet echt duidelijk hoe de resultaten van de verschillende subsecties samenhangen.
- [ ] Jesper, Chapter 4: Verder toon je nu heel veel Agda code met vaak geen of minimale uitleg. Ik zou persoonlijk veel van de minder belangrijke lemma's weglaten en in plaats daarvan focusen op de statements van de belangrijkste resultaten, hoe je deze hebt geformuleerd in Agda, en wat de overwegingen of alternatieven hierbij waren.
- [x] Jesper 4: "This section is the compliment" => the complement  
- [x] Jesper 4: "I made a serious attempt [...] but at the cutoff moment for the work..." => Zeg gewoon "due to time constraints".  
- [x] Jesper 4: "...left as an excercise to the reader" => Ik weet dat dit af en toe gezegd wordt, maar dit lijkt me meer geschikt voor een textbook dan voor een thesis. Als je het niet in de tekst wil zetten is dat ok, maar verwijs dan gewoon naar de juiste plaats in je code.  
- [x] Jesper 4: "church-encoded" => "Church-encoded"  
- [ ] Jesper 4: De "bonus functions" zonder uitleg zou ik eerlijk gezegd weglaten. Over het algemeen is het principe "less is more": beter om met een paar goed gekozen voorbeelden je punt te maken dan om de lezer te overstelpen met zo veel mogelijk voorbeelden.  
- [x] Jesper 4: "The definition of the CoChurch datatypes is defined slightly differently" => waarom is de definitie anders?
- [ ] Jesper, Introduction: De introductie is wat mij betreft oké maar zou nog wat meer context kunnen gebruiken om het toegankelijker te maken: wat is functional programming, waarom zijn we er in geïnteresseerd.- `between` is niet de standaard naam in Haskell, dat is `enumFromTo`. Ik zou eventueel deze naam gebruiken, en iig uitleggen wat de functie doet.  
- [x] Jesper, Introduction: "if repetitive and error-prone" => "*is* repetitive and error-prone"  
- [x] Jesper, Introduction: "Much work already exists" => vage statement, waar gaat dit werk over?  
- [x] Jesper, Introduction: "are replicated and investigated further " => vermijd passive voice.
- [x] Jesper, Conclusion: "And shown the generalizability" => begin zinnen niet met "and".  
- [x] Jesper, Conclusion: "Needing either proper loopification [..]" => Dit is geen volledige zin.  
- [x] Jesper, Conclusion: " It may be possible to generalize the work of Coutts et al. [...]" => De andere items in deze lijst zijn geformuleerd als acties, deze valt wat uit de boot.  
- [ ] Jesper, Conclusion: Ik zou de puntjes voor future work opdelen in (1) extensies van jouw werk, (2) toepassingen van je werk, en (3) verbeteringen aan tools (ihb Agda)











In roughly the following order, tomorrow Tuesday:
- [x] Incorporate Jaro's feedback into the thesis
- [x] Collect data
- [x] Write data collection analysis
	- Ask Jaro about wise dataset
	- Start writing before then!
- [x] Pass another section onto Jaro: Haskell pt. 2
- [x] Pass the thesis onto Nathan for readability
- [x] Incorporate Nathan's feedback
- [x] Revise intro
	- 
- [x] Pass a section onto Casper for review: introduction
- [x] Write out Agda side
	- 
- [x] Pass a section onto Jesper: Agda part
- [x] Give entire paper a pass for grammar, flow, and connectedness

Data collection plan:
Five functions types (with subtypes):
- D1: Unfused
- D4: Hand fused
- D5: GHC List fused
- Church fused
	- D2: Normal fused
	- D7: Tail recursive fused
	- Stream fused
	- Stream, tail-recursive fused
- Cochurch fused
	- D8: Normal fused
	- D3: Tail recursive fused
	- D9: Stream fused
	- D6: Stream, tail recursive fused