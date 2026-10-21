# generators-group-homology
In the folders above we give a library of finitely-presented groups by presentations, focusing on special linear groups. In addition there is code to find bounds on the second homology of finitely-presented groups and find generators in some cases.

- The special linear group presentation is in Anton, "Homological symbols and the Quillen conjecture" - https://arxiv.org/abs/0804.3553.
- The code and some implementations are found in Roberts, "An algorithm for low dimensional group homology" - https://arxiv.org/abs/0901.2610, and "Generators for Group Homology and a Vanishing Conjecture" - https://arxiv.org/abs/2009.04069.

For a brief discussion of finitely-presented groups and using them in GAP have a look at [this page]( https://jd-roberts.github.io/generators-group-homology/finitely-presented-groups.html).

## Research development

- [How the algorithms work](docs/ALGORITHMS.md): mathematical interpretation, function inputs and outputs, and when an answer is only an upper bound.
- [Dependencies and reproduction](docs/REPRODUCING.md): GAP/KBMAG setup, tests, and bounded runs against the archived tables.
- [Research review](docs/RESEARCH-REVIEW.md): presentation audit, performance bottlenecks, limitations, and proposed improvements.

With GAP and compiled KBMAG installed, run from this directory:

```sh
gap -q -b --quitonbreak tests/smoke.g
gap -q -b --quitonbreak tests/historical-h1.g
bash scripts/reproduce-h2.sh SL2F3 3 120
```

The original algorithms, presentations, notebook, HTML, and result images are
preserved. The new runner uses all defining relators as candidates and writes
logs outside the checkout; a timeout is an unfinished run, not a homology value.

