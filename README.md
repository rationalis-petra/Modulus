# The Modulus Programming Language

🚧🔨 **Under Construction**  🪛🚧

Modulus is currently under heavy development. As such, it is rife with bugs,
idiosyncrasies and unimplemented features. However, you can still try it out if
you're interested.

## Overview
Modulus is intended to bring together the development experience of the two
halves of the funcitonal programming world, offering the live-programming
experience of the Lisp family combined with the confidence inspired by the type
systems of the ML family.

### Features
+ **Structures** Tired of class hierarchy headaches? Structs are a mechanism for
  packaging type(s) and associated behaviour. They double as both a basis for a
  module system, and offer a compelling alternative to object systems for
  implementing dynamic behaviour.

+ **Dependent Types** A powerful generalisation of existing type-systems,
  dependent types enable the type-system to express arbitrary properties, like
  "a function which returns only even numbers" or "a function which outputs
  strings containing only the letters a, b and c".

+ **Metaprogramming** Write code which writes code. Modulus has two types of
  macros, which either modify the parser, or rewrite syntax trees.

+ **Powerful Libraries** Modulus has a powerful set of standard libraries which
  implement not just collections, IO and networking, but also powerful parsing
  and data-processing facilities. It also includes a JIT compiler for itself,
  enabling you to write applications which are scriptable in Modulus.

<!-- + The **Interative Enviroment** is not a feature of the language itself, but of -->
<!--   this particular implementation. Break the compile-test-rewrite cycle by -->
<!--   swapping function definitions, watch variable values, and more - all live as -->
<!--   your code is running! -->

## Currently Implemented 
+ Structures
+ Dependent Types
+ Inductive and Coinductive datatypes
+ Implicit arguments




## Installation
There are currently no distributed binaries for modulus, so you must build from
source. The steps to do so are as follows

1. Install the [Haskell Tool Stack](https://docs.haskellstack.org/en/stable/),
   if you don't already have it
2. Clone this repo onto your local file
3. From inside this repository, first run `stack build`, then run either
   `stack install` (to install) or `stack run` (to run without installing).
   
**Note**: If you want to provide command-line arguments to the modulus program
with `stack run`.
   
The inputs modulus accepts are 
+ **Mode** required, `-m` or `--mode`. Can be either `(i)nteractive`, `(s)server`
  or `(c)ompile`. 
+ **File** required, `-f` or `--file`. Can be any valid file-string.
   

   
In order to provide command line args to modulus via stack run, you'll need to
prefix arguments with `--` so `modulus --mode i` becomes `stack run -- --mode
i`.
    
## Documentation
Coming Shortly (ish)


