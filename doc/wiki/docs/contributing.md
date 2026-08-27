# Contributing to this wiki

Documentation lives **next to the code it describes**. Add a `README.md`, `USING.md`, or `CLAUDE.md` to any subproject and it appears here automatically the next time the wiki is built — no wrapper page, no nav entry, nothing to register. Project-wide documents go in [`doc/`](https://github.com/ftsrg/theta/tree/master/doc) and show up under *Guides*.

## What ends up where

| You write | It appears as |
|---|---|
| `subprojects/<family>/<module>/README.md` | the module's page under *Modules* |
| `subprojects/<family>/<module>/USING.md` | `USING.md`, under that module |
| `subprojects/<family>/<module>/CLAUDE.md` | `CLAUDE.md`, under that module |
| `doc/<name>.md` | a page under *Guides* |

`CLAUDE.md` files deeper inside a module (e.g. `common/core/src/.../core/type/CLAUDE.md`) appear nested under the module, mirroring their place in the source tree.

Links and images in these files are relative to the file itself, which is what makes them work on GitHub and in an IDE. They are rewritten to point at GitHub when the page is built, so write them as you normally would.

## Wiki-only pages

Pages that belong to the wiki rather than to a module — this one, and the front page — live in [`doc/wiki/docs/`](https://github.com/ftsrg/theta/tree/master/doc/wiki). The mirroring itself is implemented in [`doc/wiki/hooks.py`](https://github.com/ftsrg/theta/blob/master/doc/wiki/hooks.py).

## Previewing locally

```bash
pip install -r doc/wiki/requirements.txt
cd doc/wiki && mkdocs serve      # http://127.0.0.1:8000
```

The preview reloads when you edit any mirrored file, so you can write a module's `README.md` in your editor and watch the page update. `./gradlew buildDocs` builds the site once (it also needs the packages above installed).

The wiki is rebuilt in CI on every push and pull request, and deployed on release.

If you need to familiarize yourself with the features of [Markdown](https://www.markdownguide.org/), [MkDocs](http://mkdocs.org) or [MkDocs-Material](https://squidfunk.github.io/mkdocs-material/), please check their corresponding project pages or the [MkDocs-Material Reference](https://squidfunk.github.io/mkdocs-material/reference/).
