# Modulus

Modulus is a strongly-typed functional programming langauge designed for the
construction of powerful and general abstractions.

+ Modulus is built on top of *Modules*, which enable abstractions by describing
  a type(s) by their *behaviour*, rather than structures. Modules can be used
  for several orthogonal purposes, including information-hiding, polymorphism
  and namespacing.
  
+ Modulus features *algebraic effects* this system lets you define advanced
  control abstractions such as exceptions, state or probabilistic
  programs. These effects are much like Monads, but are more easily composable
  and combinable (no need for transformers and lift!) 

Modulus is a personal project, and currently under heavy development. Expect
things to be unimplemented, and many bugs!

To lean more: 
+ Read the tour below (for functional programmers)
+ For those with less functional experience, I'd recommend starting with a more
  mature language, although I am working on a longer-form Modulus Book :)
  
  
# Whirlwind Tour of Modulus
## Installation
Currently, there are no packages for installing Modulus: to install, you will
need Haskell's [stack](https://docs.haskellstack.org/en/stable/README/)
tool. Then, clone the repository, navigate to it on the command line, and invoke
`stack build`. From here, you can run the binary without installing it via
`stack run`, or use `stack install` for it to be installed to
`.local/bin/modulus`.

The Modulus lanugage heavily encourages the use of unicode characters in
programs, with many standard-library functions and some keywords incorporating
them. It is therefore recommended to install an extension which makes typing
these characters much easier (e.g. Emacs' tex-input-mode or unicode-math
package). 


## Functions and Types
Like Haskell, Modulus is a lanugage of pure terms and functions, which are
distinguished from impure computations by the type-system. To define a function,
use the `defn` keyword. Type-annotations (optional) can be added either to
arguments or the function as a whole. 

```modulus
;; annotation via arguments
(defn add-n [(lst : list int) (n : int)]
  ;; anonymous functions defined via λ
  (map (λ [x] (x + n)) lst))

;; annotate the function
(upper-lower : string → bool → string)
(defn upper-lower [s upper] 
  (if upper 
    (to-upper s)
    (to-lower s)))

```

One major difference is that polymorphism is achieved with *explicit* type
arguments. To demonstrate, imagine the trivial function `app`, which takes a
function `f : a → b` and an argument `x : a` and then calls f with argument
x. This function might look like

```modulus
(defn app [(a : type) (b : type) (f : a → b) (x : a)]
  (f x)) 
```

Then, the expression calling `app` with a function `to-str : int → string` and argument 2 is: 
`app int string to-str 2`. Modulus thus sacrifices the nice compactness of
Hindley-Milner based systems and in return receives the full power of
System-Fω. However, this verbosity can quickly become tiring, so Modulus offers
a compromise: all type arguments which occur *before* any value arguments can be
made implicit, by surrounding them with curly-braces: 

```modulus
(defn app {a b} [(f : a → b) (x : a)]
  (f x))
```

Now, when type-checking, e.g. `app to-str 2`, Modulus will try and infer the
values of the implicit arguments a and b (int and string). As there is the
restriction that the type arguments *must* come before any value arguments, not
all type arguments can be made implicit, but most can. 




## Effects
You may be familiar with Haskell's *Monad* system Modulus can have Monads, but
in most use-cases its' *effect* system will be the first thing you reach
for. The effect system allows you to make use of standard computational effects
like *state*, *exceptions*, *failure* or even define your own custom effects
for, e.g. logging. If a term causes an effect before it is used, it is listed in
angle brankets (⟨⟩) before the type of the term. For example, if you know that a
function `foo` has type `string → ⟨(state bool) (except string)⟩ string`, then you know that the
function: 

1. Takes a string as argument and returns a string
2. Relies on *state* and may raise an *exepction*
  + The type of the exeption that may be raised is string (presumably some kind
    of message).
  + The only value that *state* modifies is a single boolean.

All effects except IO can be defined within the lanugage, so let's look at
making our own: imagine that we want to represent computations which may
try and calculate an undefined value - for example, dividing by zero, or taking
the logarithm of a negative number. First, we have to tell

```modulus
(effect undef
  (undefined [] float))
```

The meaning of this is that a computation can call `undefined` with a single
argument (of unit type) and expect to receive a `float` in return. The value of
this float is unknown by the callee. For example, to implement a division whiich
returns undefined when we divide by zero, we do:

```modulus
(defn udiv [(n : float) (m : float)] 
  (if (m = 0) (undef) (n / m)))
```

This function will be typed: `float → flaot → ⟨undef⟩ float` by Modulus. If you
wish to sequence effects, we use a `seq` clause. As an example, imagine we have
a `vec3` type which has fields `x` `y` and `z` (all floats), and wish to write a
normalization function. In this case, each value must be divided by the
(potentially zero) magnitude. 

```modulus
(defn normalize-vector [(v : vec3)]
  (let m (magnitude v))
  (seq
    ;; To capture values, use a left-arrow
    (x' ← udiv v.x m)
    (y' ← udiv v.y m)
    (z' ← udiv v.z m)

    ;; The value of the final expression is returned by the seq expression
    (vec3 x' y' z')))
```

So far I have simply said that an *undef* may evaluate to *any* float, but how
do we decide which one? The answer is that we use *effect handlers*. You can
think of an effect handler as being kind of like a "try-catch" statement for
effects. Let us consider two ways of handling an undefined value: 
1. Give up: the computation has failed, and we return nothing
2. Substitute in a value 

The handler for the first option might look like

```modulus
;; maybe return nothing
(handle (code-to-handle)
  (undef [_] None)
  (val [v] (Some v)))
```

The code we handle might contain within it an `undef`. The first clause of the
handler tells us that, if this does happen, the entire expression should return
`None`. If no call is made to undef, then the expression will eventaully return
a value, and the `val` calsue will be invoked, and so `Some v` (where v is the
value) will be returned. In this way, we have converted an impure computation
into a pure computation returning a maybe value. 

In the second option, we want to sunstitute in some value (I'll use 0) whenever
an `undef` term appears. This is where we see that effect handlers are subtly
different from exceptions: when we handle an effect, the handler also takes in
an argument which I've called `k`. This is a *continuation* it is a function
which, when called with a particular value (in this case zero) will resume the
computation at the point where the `undef` term was evaluated, except the value
we provide it is substituted in.

```modulus
;; substitute 0
(handle (some-vector-code ())
  (undef [k] (k 0))
  (val [v] v))
```

