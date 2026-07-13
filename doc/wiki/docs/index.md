# Theta
!!! abstract "About Theta"

    _Theta_ is a generic, modular and configurable model checking framework developed at the [Critical Systems Research Group](http://inf.mit.bme.hu/en) of [Budapest University of Technology and Economics](http://www.bme.hu/?language=en), aiming to support the design and evaluation of abstraction refinement-based algorithms for the reachability analysis of various formalisms.
    The main distinguishing characteristic of Theta is its architecture that allows the definition of input formalisms with higher level language front-ends, and the combination of various abstract domains, interpreters, and strategies for abstraction and refinement.
    Theta can both serve as a model checking backend, and also includes ready-to-use, stand-alone tools.

## How this wiki is organised

Every page here is **mirrored from a markdown file in the repository** — the wiki adds no
documentation of its own. Each page is named after the file it comes from, and says at the
top which file that is.

* **Modules** — documentation living inside the subprojects. A module can have up to three pages:

    | Page | Mirrors | What it is |
    |---|---|---|
    | `README.md` | `subprojects/<family>/<module>/README.md` | what the module is, conceptually |
    | `USING.md` | `.../USING.md` | how to *use* the module's API from elsewhere |
    | `CLAUDE.md` | `.../CLAUDE.md` | how to *modify* the module: invariants, conventions, change recipes |

    Larger modules may also carry `CLAUDE.md` files deeper inside (e.g. `common/core/type/`); those
    appear nested under the module, mirroring their location in the source tree.

* **Guides** — project-wide documentation, mirrored from [`doc/`](https://github.com/ftsrg/theta/tree/master/doc): building, coding conventions, CI, CEGAR configuration.

!!! note "About the `USING.md` and `CLAUDE.md` pages"

    These two are **code-facing**: largely derived from the source (and verified against it) rather
    than written as prose, and aimed at contributors — and at AI coding assistants, which load
    `CLAUDE.md` automatically when editing a module. They are deliberately terse and uneven in
    coverage. `README.md` pages are ordinary, hand-written documentation.

## Contributing to this wiki

Documentation lives **next to the code it describes**. Add a `README.md`, `USING.md`, or `CLAUDE.md` to any subproject and it appears here automatically the next time the wiki is built — no wrapper page, no nav entry, nothing to register. Project-wide documents go in [`doc/`](https://github.com/ftsrg/theta/tree/master/doc) and show up under *Guides*.

Pages that belong only to the wiki (like this one) live in [`doc/wiki/docs/`](https://github.com/ftsrg/theta/tree/master/doc/wiki). To preview your changes locally:

```bash
pip install -r doc/wiki/requirements.txt
cd doc/wiki && mkdocs serve      # http://127.0.0.1:8000
```

If you need to familiarize yourself with the features of [Markdown](https://www.markdownguide.org/), [MkDocs](http://mkdocs.org) or [MkDocs-Material](https://squidfunk.github.io/mkdocs-material/), please check their corresponding project pages or the [MkDocs-Material Reference](https://squidfunk.github.io/mkdocs-material/reference/).
