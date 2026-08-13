# CoEndoYoneda Equivalence and Purity

See [documentation and Agda code](https://github.com/LucDuponcheelAtGitHub/CoEndoYoneda-and-Purity-in-Agda/blob/main/CoEndoYonedaEquivalenceAndPurity.lagda.md).

This file uses `strict` and contains `postulate`s.

See [documentation and Cubical Agda code](https://github.com/LucDuponcheelAtGitHub/CoEndoYoneda-and-Purity-in-Agda/blob/main/CubicalCoEndoYonedaEquivalenceAndPurity.lagda.md).

This file does not use `strict` and does not contain `postulate`s.

Both files are work in progress.

## In short

I proved a CoEndoYoneda equivalence theorem, that generalizes the well known one for the
category of sets and functions.

This project is an *every disadvantage has an advantage* story.

*First the disadvantage*

It turns out to be hard to find categories satisfying the requirements of the theorem, so
albeit a nice pointfree generalization of the standard pointful equivalance for the category
of sets and functions, one of my initial goals, generalizing to impure functions, functions
with side effects, turns out to be unachievable.

*Now the advantage*

For the category of Kleisli functions, the requirements of the theorem are *equivalent* with 
the idempotency, see [nLab](https://ncatlab.org/nlab/show/idempotent+monad), of the monad of
the Kleisli function.

Informally, idempotency of a monad boils down to
"performing the side effect twice is the same as performing it once".
This suggests that the side effect is not a side effect at all.

This can be proved formally.

In short, what I have defined is a
*categorical classification of purity*
that, for the category of Kleisli functions, is equivalent with the monad involved being side
effect free. 

Considering monads as computations, expressions with side effects, and noting that
computations are pointful, what I have defined is a
*pointfree classification of the pointful concept* which I like to refer to as
*computation (execution) referential transparency*, cfr.
*expression (evaluation) referential transparency*.

