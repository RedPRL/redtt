redtt mathematical library
=============

This is the home of the `redtt` mathematical library.


Style and conventions
---------------------

We have no absolute rules, but try to adhere to the following:

- Generally use lowercase
- Keep line lengths reasonably short (< 90 characters)
- Write multi-word semantic units with hyphen (`is-contr`, `weak-connection`)
- Write subordinate semantic units with slash (`plus/assoc`, `symm/unit`)
- Reserve `is-` and `has-` for h-propositions (`is-contr`, `has-hlevel`)

Library structure
-----------------

- `prelude/` contains definitions that are expected to be needed in all `redtt`
  developments.

- `data/` contains the bare definitions of datatypes, and whatever functions can
  be defined without needing other constructions and lemmas.

- `basics/` contains basic theorems of cubical type theory, which might not be
  needed everywhere.

- `paths/` contains theorems about the higher dimensional structure of types in
  cubical type theory, such as characterizations of loop spaces, etc.

- `cool/` contains cool constructions and theorems which aren't needed by anything;
  many new developments will first start in `cool/`, and become their own folders as
  become more complex and mature.
