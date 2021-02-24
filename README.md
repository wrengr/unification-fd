unification-fd
==============
[![Hackage version](https://img.shields.io/hackage/v/unification-fd.svg?style=flat)](https://hackage.haskell.org/package/unification-fd)
[![Build Status](https://github.com/wrengr/unification-fd/workflows/CI/badge.svg)](https://github.com/wrengr/unification-fd/actions?query=workflow%3ACI)
[![Upstream Dependencies](https://img.shields.io/hackage-deps/v/unification-fd.svg?style=flat)](http://packdeps.haskellers.com/specific?package=unification-fd)
[![Downstream Dependants](https://img.shields.io/hackage-deps/v/unification-fd.svg?style=flat)](http://packdeps.haskellers.com/reverse/unification-fd)

The unification-fd package offers generic functions for single-sorted
first-order structural unification (think of programming in Prolog,
or of the metavariables in type inference)[^1][^2]. The library
*is* sufficient for implementing higher-rank type systems à la
_Peyton Jones, Vytiniotis, Weirich, Shields_, but bear in mind that
unification variables are the metavariables of type inference— not
the type-variables.


## Build Warnings/Errors

This is a simple package and should be easy to install; however,
on older setups you may encounter some of the following warnings/errors.
If during building you see some stray lines that look like this:

    mkUsageInfo: internal name? t{tv a7XM}

Feel free to ignore them. They shouldn't cause any problems, even
though they're unsightly. This should be fixed in newer versions
of GHC. For more details, see:

    http://hackage.haskell.org/trac/ghc/ticket/3955

If you get a bunch of type errors about there being no `MonadLogic`
instance for `StateT`, this means that your copy of the logict
library is not compiled against the same mtl that we're using. To
fix this, update logict to use the same mtl.


## Portability

An effort has been made to make the package as portable as possible.
However, because it uses the `ST` monad and the mtl-2 package it
can't be H98 nor H2010. However, it only uses the following common
extensions which should be well supported[^3]:

* Rank2Types
* MultiParamTypeClasses
* FunctionalDependencies - Alas, necessary for type inference.
* FlexibleContexts - Necessary for practical use of MPTCs.
* FlexibleInstances - Necessary for practical use of MPTCs.
* UndecidableInstances - Needed for `Show` instances due to two-level types.


## Description

The unification API is generic in the type of the structures being
unified and in the implementation of unification variables, following
the two-level types pearl of Sheard (2001). This style mixes well
with Swierstra (2008), though an implementation of the latter is
not included in this package.

That is, all you have to do is define the functor whose fixed-point
is the recursive type you're interested in:

    -- The non-recursive structure of terms
    data S a = ...

    -- The recursive term type
    type PureTerm = Fix S

And then provide an instance for `Unifiable`, where `zipMatch`
performs one level of equality testing for terms and returns the
one-level spine filled with pairs of subterms to be recursively
checked (or `Nothing` if this level doesn't match).

    class (Traversable t) => Unifiable t where
        zipMatch :: t a -> t b -> Maybe (t (a,b))

The choice of which variable implementation to use is defined by
similarly simple classes `Variable` and `BindingMonad`. We store
the variable bindings in a monad, for obvious reasons. In case it's
not obvious, see Dijkstra et al. (2008) for benchmarks demonstrating
the cost of naively applying bindings eagerly.

There are currently two implementations of variables provided: one
based on `STRef`s, and another based on a state monad carrying an
`IntMap`. The former has the benefit of O(1) access time, but the
latter is plenty fast and has the benefit of supporting backtracking.
Backtracking itself is provided by the logict package and is described
in Kiselyov et al. (2005).

In addition to this modularity, unification-fd implements a number
of optimizations over the algorithm presented in Sheard (2001)—
which is also the algorithm presented in Cardelli (1987).

* Their implementation uses path compression, which we retain.
    Though we modify the compression algorithm in order to make
    sharing observable.
* In addition, we perform aggressive opportunistic observable
    sharing, a potentially novel method of introducing even more
    sharing than is provided by the monadic bindings. Basically,
    we make it so that we can use the observable sharing provided
    by the modified path compression as much as possible (without
    introducing any new variables).
* And we remove the notoriously expensive occurs-check, replacing
    it with visited-sets (which detect cyclic terms more lazily and
    without the asymptotic overhead of the occurs-check). A variant
    of unification which retains the occurs-check is also provided,
    in case you really need to fail fast.
* Finally, a highly experimental branch of the API performs *weighted*
    path compression, which is asymptotically optimal. Unfortunately,
    the current implementation is quite a bit uglier than the
    unweighted version, and I haven't had a chance to perform
    benchmarks to see how the constant factors compare. Hence moving
    it to an experimental branch.

These optimizations pass a test suite for detecting obvious errors.
If you find any bugs, do be sure to let me know. Also, if you happen
to have a test suite or benchmark suite for unification on hand,
I'd love to get a copy.


## Notes and limitations

[^1]: At present the library does not appear amenable for implementing
higher-rank unification itself; i.e., for higher-ranked metavariables,
or higher-ranked logic programming. To be fully general we'd have
to abstract over which structural positions are co/contravariant,
whether the unification variables should be predicative or
impredicative, as well as the isomorphisms of moving quantifiers
around. It's on my todo list, but it's certainly non-trivial. If
you have any suggestions, feel free to contact me.

[^2]: At present it is only suitable for single-sorted (aka untyped)
unification, à la Prolog. In the future I aim to support multi-sorted
(aka typed) unification, however doing so is complicated by the
fact that it can lead to the loss of MGUs; so it will likely be
offered as an alternative to the single-sorted variant, similar to
how the weighted path-compression is currently offered as an
alternative.

[^3]: With the exception of fundeps which are notoriously difficult
to implement. However, they are supported by Hugs and GHC 6.6, so
I don't feel bad about requiring them. Once the API stabilizes a
bit more I plan to release a unification-tf package which uses type
families instead, for those who feel type families are easier to
implement or use. There have been a couple requests for unification-tf,
so I've bumped it up on my todo list.


## References

<dl>
<dt
    >Luca Cardelli (1987)</dt>
<dd><i>Basic polymorphic typechecking</i>.
    Science of Computer Programming, 8(2): 147–172.</dd>
<dt
    ><a href="http://www.cs.uu.nl/research/techreps/repo/CS-2008/2008-027.pdf"
    >Atze Dijkstra, Arie Middelkoop, S. Doaitse Swierstra (2008)</a></dt>
<dd><i>Efficient Functional Unification and Substitution</i>.
    Technical Report UU-CS-2008-027, Utrecht University.</dd>
<dt
    ><a href="http://research.microsoft.com/en-us/um/people/simonpj/papers/higher-rank/putting.pdf"
    >Simon Peyton Jones, Dimitrios Vytiniotis, Stephanie Weirich, Mark
    Shields (2007)</a></dt>
<dd><i>Practical type inference for arbitrary-rank types</i>.
    JFP 17(1). The online version has some minor corrections/clarifications.</dd>
<dt
    ><a href="http://www.cs.rutgers.edu/~ccshan/logicprog/LogicT-icfp2005.pdf"
    >Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, and Amr Sabry (2005)</a></dt>
<dd><i>Backtracking, Interleaving, and Terminating Monad Transformers</i>.
    ICFP.</dd>
<dt
    ><a href="http://web.cecs.pdx.edu/~sheard/papers/generic.ps"
    >Tim Sheard (2001)</a></dt>
<dd><i>Generic Unification via Two-Level Types and Parameterized Modules</i>,
    Functional Pearl. ICFP.</dd>
<dt
    ><a href="http://web.cecs.pdx.edu/~sheard/papers/JfpPearl.ps"
    >Tim Sheard and Emir Pasalic (2004)</a></dt>
<dd><i>Two-Level Types and Parameterized Modules</i>.
    JFP 14(5): 547–587.
    This is an expanded version of Sheard (2001) with new examples.</dd>
<dt
    ><a href="http://www.cs.ru.nl/~wouters/Publications/DataTypesALaCarte.pdf"
    >Wouter Swierstra (2008)</a></dt>
<dd><i>Data types à la carte</i>,
    Functional Pearl. JFP 18: 423–436.</dd>
</dl>


## Links

* [Website](https://wrengr.org/)
* [Blog](http://winterkoninkje.dreamwidth.org/)
* [Twitter](https://twitter.com/wrengr)
* [Hackage](http://hackage.haskell.org/package/unification-fd)
* [GitHub](https://github.com/wrengr/unification-fd)
