This is an attempt to develop normalization-by-evaluation for [cartesian
cubical type theory](https://arxiv.org/abs/1712.01800), using the interval and
"extension types" to generalize path types.  As far as cubes are concerned,
this implementation is mostly inspired by
[yacctt](https://github.com/mortberg/yacctt/), [RedPRL](https://www.redprl.org)
and [cubicaltt](https://github.com/mortberg/cubicaltt). In our (to be
developed) source language, we aspire to be influenced by Epigram,
[Idris](https://www.idris-lang.org/) and RedPRL.

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
$ git clone https://github.com/jonsterling/cubical-experiment
$ cd tt
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
