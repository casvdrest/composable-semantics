.PHONY: loc

default: 
	agda --verbose=2 src/Everything.agda ; agda --verbose=2 src/ArbitraryCategories/Sets.agda

doc: 
	agda --html --html-dir=docs src/Everything.agda ; agda --html --html-dir=docs src/ArbitraryCategories/Sets.agda
      
loc:
	cloc --force-lang=Agda --by-file --exclude-dir=Fragment,Languages,Canon,Interface,Test --exclude-list-file=src/.donotcount src
	cloc --force-lang=Agda --by-file --list-file=src/.docount src
