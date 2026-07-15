# Theta

[**About Theta**](about.md) — what Theta is, the tools it ships, an overview of the architecture, and how to cite it. (Mirrored from the repository's front page.)

## How this wiki is organised

Each page is named after the file it comes from, and says at the top which file that is.

* **Modules** — documentation living inside the subprojects. A module can have up to three pages:

    | Page | Mirrors | What it is |
    |---|---|---|
    | `README.md` | `subprojects/<family>/<module>/README.md` | what the module is; conceptual documentation |
    | `USING.md` | `.../USING.md` | how to *use* the module's API from elsewhere |
    | `CLAUDE.md` | `.../CLAUDE.md` | how to *modify* the module: invariants, conventions, change recipes |

    Larger modules may also carry `CLAUDE.md` files deeper inside (e.g. `common/core/type/`); those
    appear nested under the module, mirroring their location in the source tree.

* **Guides** — project-wide documentation, mirrored from [`doc/`](https://github.com/ftsrg/theta/tree/master/doc): building, coding conventions, CI, CEGAR configuration.

!!! note "About the `USING.md` and `CLAUDE.md` pages"

    These two are **code-facing**: largely derived from the source (and verified against it) rather
    than written as prose. They are aimed at both contributors and at AI coding assistants, which load
    `CLAUDE.md` automatically when editing a module. They are deliberately terse and uneven in
    coverage. `README.md` pages are ordinary, hand-written documentation.

## Contributing

Documentation lives next to the code it describes: add a `README.md`, `USING.md`, or `CLAUDE.md` to a subproject and it appears here automatically. See [Contributing](contributing.md) for the details and for how to preview the wiki locally.
