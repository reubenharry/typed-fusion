This is an exploratory library for working with symmetry-respecting linear maps, in the vein of TensorKit.

The unique feature of this library is that it is written in Haskell, which has a type system that is much more expressive than Julia, and can encode the relevant mathematical structure at compile time. For example, we can write

```haskell
x :: C 2 ⊗ C 3
x = vec (1,2) ⊗ vec (4,5,6)
```

The top line specifies the type, and should be read as the mathematical statement $x : \mathbb{C}^2 \otimes \mathbb{C}^3$. 

Haskell really checks this. For example, if you write

```haskell
x = vec (1,2) ⊗ vec (4,5)
```

you will get an error like the following in real time:

SCREENSHOT

## Clebsch-Gordan rules and fusion in the types

The real point of this library is to write symmetry respecting linear maps, like:

TODO

As before, the top line is the type, which should be read as the mathematical statement $x : \mathbb{C}^2 \otimes \mathbb{C}^3 \Rightarrow \mathbb{C}^4$, where I use $\Rightarrow$ to refer to an intertwining map, i.e. a linear map that respects the symmetry of the representation.

Like TensorKit, the representation of intertwiners takes advantage of Schur's lemma to massively reduce the amount of storage needed for a large linear map. Unlike TensorKit, everything is checked at compile time, so if you write 

in real time it will show the following:

screenshot

This is underlined because the compiler knows that the Clebsch-Gordan rule for adding two Spin Half representations should yield a Singlet and a Triplet, and that a Triplet lives in a 3-dimensional vector space, not a 2-dimensional vector space.

## Why do this?

Without statically checked types, it is very easy to make mistakes. It's also very easy to lose track of what the shapes of arrays should be. 

This library is an exploration of the idea that tensor network libraries should really be written in languages with expressive types. A more extreme version would be to use Lean, where the types are in principle powerful enough to prove the correctness of the algorithms themselves. Haskell is a nice middle ground, where the types are reasonably expressive, but the compiled code is engineered to be fast.
