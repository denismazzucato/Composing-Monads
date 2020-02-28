# Composing Monads
Research Report on Composing Monads for an University project

## Report
The report is written in Latex and a final version of it has been added to
the repo as *main.pdf*.
This work is based on
[Composing monads*](http://web.cecs.pdx.edu/~mpj/pubs/composing.html)
by Mark P. Jones and Luc Duponcheel.

My works is just a study of the main one, without many differences. 
The main one is the proof that a natural join doesn't exists.
I found out that the proof presented in the original paper is wrong,
so I presented my own version.

## Formalization

One year later, I decided to formalize in
[Lean](https://leanprover.github.io/) this work.
The work can easily be found in the *src* directory.

### dir structure

The work is divided into two main namespace: *category* and *composed*.

The first one includes the basic structure of *functor*, *premonad* and *monad*.
I've decided to built these structures on my own.
Anyway, my environment is totally equivalent to the one inside the Lean standard library
(the proof of this statement can be found in *src/category/conjunction.lean*).

The last one groups all the classes and functions required to compose two generic monads (with all the necessary auxiliary functions).
With this structure you can safely compose monads without losing any monad property.
They are automatically inferred from the two given monads. 

```
src
|- data/maybe
   |- basic.lean
   |- instances.lean
|- category
   |- functor.lean
   |- premonad.lean
   |- monad.lean
   |- lawful.lean
   |- conjunction
   |- natural_join
|- composed
   |- lawful
      |- prod
      |- dorp
      |- swap
   |- basic
   |- prod
   |- dorp
   |- swap
   |- instances
   ```

**data/maybe** is just an instance example of my own monadic environment.

**category/lawful** exposes the lawful classes for functor, premonad and monad.
They slightly differ from the lawful described in the standard library, but as shown in *category/conjunction* they are equivalent. 

**category/conjunction**, this module defines the equivalence between the standard and the custom monadic structure.

**category/natural_join** is the proof that a function with the right sign (MNMNX → MNX) cannot 
be found only with the given monads M and N.

**composed/basic** defines the structure for the composition of functor and premonad only.
**composed/prod**, **composed/dorp** and **composed/swap** define the structure for the monad composition instead.

**composed/instances** prove that the composition of two functors or premonads respect their lawful classes.

**composed/lawful/*** prove that the composition of two monads (plus an auxiliary function) respects it monadic lawful class. 

