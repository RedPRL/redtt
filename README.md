`redtt` is a core language for cartesian cubical type theory with extension
types. We plan to build an extensible interactive proof assistant around it,
using ideas from proof assistants like [RedPRL](https://www.redprl.org),
Epigram, and [Idris](https://www.idris-lang.org/).

Related work: [yacctt](https://github.com/mortberg/yacctt/), [RedPRL](https://www.redprl.org)
and [cubicaltt](https://github.com/mortberg/cubicaltt).

## Feature Summary

`redtt` is not yet documented; we have the following interesting features:

- path types definable in terms of more general extension types, which specify
  the boundary of an `n`-cube all at once

- source language with implicit arguments based on a cubical version of
  higher-order unification

- predicative hierarchy of cumulative universes

- level "polymorphic" definitions achieved using McBride's "Crude But Effective
  Stratification" (in which each thing is defined at the lowest level possible,
  and then hoisted upward when needed)

- two-level type theory in the style of RedPRL: currently we have only pretypes
  and (kan) types. Once we design a suitable account of exact equality types in
  the cubical setting, we will add these, and they will live side-by-side with
  path types as they did in RedPRL.

- some built-in inductive types: natural numbers, integers, booleans, the circle

- experimental support for Fitch-style modal guarded recursion


Features we intend to add in the near future:

- general higher inductive types, based on the [work of Evan Cavallo and Bob
  Harper](https://arxiv.org/abs/1801.01568)

- user-extensible tactic language

- namespacing



## Contributing Guidelines

Help is welcome and desired! Please see the [open
tickets](https://github.com/jonsterling/cubical-experiment/issues) and
especially our
[Roadmap](https://github.com/jonsterling/cubical-experiment/projects/2).
Currently, we are trying to limit the dependencies of this code; when something
is available as a package, but can easily be coded locally, we prefer the
latter.

We also want to avoid using things like syntax extensions/ppxs, though we may
end up using one of these for the lexer at one point.


## Installing

### Prerequisites

| prerequisite |      | version                                                                | how to install                  |
| ------------ | ---- | :--------------------------------------------------------------------- | ------------------------------- |
| Opam         | `>=` | [`1.2.2`](https://github.com/ocaml/opam/releases/tag/1.2.2)            | manually or via package manager |
| OCaml        | `>=` | [`4.06.1`](https://github.com/ocaml/ocaml/releases/tag/4.06.1)         | `opam switch 4.06.1`            |
| utop         | `>=` | [`2.0.2`](https://github.com/diml/utop/releases/tag/2.0.2)             | `opam install utop` (optional)  |

If this is your first time configuring OPAM, please run `opam init` before `opam switch`.

### Other recommended packages

We recommend installing `merlin` and `ocp-indent` using `opam`; the easiest way to edit
OCaml code out of the box is to install [Visual Studio
Code](https://code.visualstudio.com/?wt.mc_id=adw-brand&gclid=EAIaIQobChMImd3JoKeL2wIVUlmGCh1lHAQ1EAAYASAAEgLUxPD_BwE)
along with the [OCaml and Reason
IDE](https://marketplace.visualstudio.com/items?itemName=freebroccolo.reasonml)
package by Darin Morrison.

### Installing Dependencies

```
$ git clone https://github.com/RedPRL/redtt
$ cd redtt
$ opam update
$ opam pin add -y redtt . # the first time you build
$ opam upgrade            # after packages change
```

### Building

```
$ make
```

### Toplevel

Requires `utop` (see prerequisites).

```
$ make top
```

### Tests

```
$ make test
```



### Acknowledgments

This research was sponsored by the Air Force Office of Scientific Research under grant number FA9550-15-1-0053 and the National Science Foundation under grant number DMS-1638352. We also thank the Logic and Semantics Group at Aarhus University for their hospitality in during the summer of 2018, during which part of this work was undertaken. The views and conclusions contained here are those of the authors and should not be interpreted as representing the official policies, either expressed or implied, of any sponsoring institution, government or any other entity.
