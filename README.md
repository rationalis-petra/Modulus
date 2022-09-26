# The Modulus Programming Language

🚧🔨 **Under Construction**  🪛🚧

Modulus is a programming language which is currently under heavy development. As
such, it is rife with bugs, idiosyncrasies and unimplemented features. However,
you can still try it out if you're interested.

## Desired Features
+ **Structures** Tired of class hierarchy headaches? mechanism for packaging
  type(s) and associated behaviour. They offer a compelling alternative to
  object systems for implementing dynamic behaviour.

+ **Dependent Types** A powerful generalisation of existing type-systems,
  dependent types enable the type-system to express arbitrary properties, like
  "a function which returns only even numbers" or "a function which outputs
  strings containing only the letters a, b and c".

+ **Metaprogramming** Write code which writes code. You can write
  two types of macros, either modifying the parser, or rewriting syntax trees. 

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
3. From inside this repository, run either
  + `stack build`,
  + `staack install` or
  + `stack run`. In order to provide command line args to the modulus program
    this way, you'll need to prefix `--`. So, to run modulus with the interpret
    (`-i`) flag, you do: `stack run -- -i`. To run modulus in interpreted mode
    on the file "myprog.mls", call `stack run -- -i --file myprog.mls`
    
## Documentation
Currently a WIP, sorry...


