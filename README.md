# Intrinsically-Typed Definitional Interpreters à la Carte

Joint work with Casper Bach Poulsen, Arjen Rouvoet, Eelco Visser, Peter Mosses. 

Browse the code interacively [**here**](https://casvdrest.github.io/composable-semantics/Everything.html)

Familiar with Agda? `Everything.agda` imports all definitions.  

## Build instructions

Run `make` in the top level directory of this repository to check `Everything.agda` (which imports all definitions).  
Run `make doc` in the top level directory of this repository to generate HTML documentation in `docs/`. 

## Clickable HTML

To view the code in the interactive and clickable format, open `docs/Everything.html` in your browser after generating the HTML.  

## Troubleshooting

Try 
```
git submodule init
git submodule update --recursive
```
if building fails due to missing dependencies.  

# Dependencies

* [Agda (version >= 2.6.1.3)](https://agda.readthedocs.io/)
* [The Agda standard library](https://github.com/agda/agda-stdlib)
* [The agda-categories library](https://github.com/agda/agda-categories)
