"""MkDocs hooks for the Theta wiki.

Docs live next to the code they describe; this file pulls them onto the wiki at
build time. Nothing is copied and nothing needs a wrapper page — drop a file in
your module and it appears on the site the next time the wiki is built.

Discovery rules
---------------
1. Any ``README.md`` / ``USING.md`` / ``CLAUDE.md`` under ``subprojects/`` becomes a
   page under *Modules*, at a nav path mirroring the module it belongs to
   (``subprojects/common/core/USING.md`` -> *Modules / common / core / Using*).
   Docs nested deeper inside a module (e.g. in a Java package) keep the package
   tail in their nav path, with ``src/main/java/hu/bme/mit/theta/<module>`` stripped.
2. Any ``*.md`` under ``doc/`` (except this wiki itself) becomes a page under
   *Guides*, plus the repository-level ``CLAUDE.md``.

So: a doc that belongs to one module lives in that module; a doc that belongs to
the project as a whole lives in ``doc/``. Both end up on the wiki.

Link fix-up
-----------
The discovered files use links relative to their own location on disk, which mean
nothing on the published site. Every relative link on such a page is therefore
rewritten to point at GitHub (``blob/`` for pages and source files, ``raw/`` for
images), resolved against the directory the file came from.
"""

from __future__ import annotations

import posixpath
import re
from pathlib import Path
from urllib.parse import urlsplit

from mkdocs.structure.files import File

REPO_ROOT = Path(__file__).resolve().parents[2]
GITHUB_BLOB = "https://github.com/ftsrg/theta/blob/master/"
GITHUB_RAW = "https://raw.githubusercontent.com/ftsrg/theta/master/"

# Pages are named after the file they mirror, so that the nav says plainly where each
# page comes from: a page called "USING.md" is that module's USING.md, nothing else.
# source filename -> destination basename
MODULE_DOCS = {
    "README.md": "readme.md",
    "USING.md": "using.md",
    "CLAUDE.md": "claude.md",
}

_BANNERS = {
    "USING.md": (
        '!!! info "`USING.md` — how to use this module"\n'
        "    Cookbook for *consuming* this module's API from elsewhere in Theta. Largely\n"
        "    derived from the source and verified against it, so it reads closer to code\n"
        "    than to prose.\n\n"
        "    Mirrored from [`{path}`]({url}) — edit it there, not here.\n"
    ),
    "CLAUDE.md": (
        '!!! info "`CLAUDE.md` — how to modify this module"\n'
        "    Invariants, conventions and change recipes for contributors — and for AI coding\n"
        "    assistants, which load this file automatically when editing the module. Largely\n"
        "    derived from the source and verified against it.\n\n"
        "    Mirrored from [`{path}`]({url}) — edit it there, not here.\n"
    ),
    "README.md": (
        '!!! info "`README.md` — what this module is"\n'
        "    Mirrored from [`{path}`]({url}) — edit it there, not here.\n"
    ),
}

_THETA_PACKAGE = ("hu", "bme", "mit", "theta")
_SOURCE_SET = ("main", "test", "testFixtures")
_SOURCE_LANG = ("java", "kotlin", "resources", "antlr")

_HREF_RE = re.compile(r'(<a href=")([^"]+)(")')
_IMG_RE = re.compile(r'(<img[^>]*?\ssrc=")([^"]+)(")')


def _title_for(rel: Path) -> str:
    """Nav/page title: the source filename, so provenance is obvious from the nav."""
    return rel.name


def _module_dest(rel: Path, *, shorten: bool = True) -> str:
    """subprojects/<family>/<module>/[...]/<KIND>.md -> Modules/<family>/<module>/[...]/<kind>.md

    With ``shorten``, boilerplate path segments (the Gradle source-set layout and the
    ``hu.bme.mit.theta.<module>`` package prefix) are dropped from the nav path. Callers
    fall back to ``shorten=False`` if two docs would otherwise land on the same page.
    """
    parts = rel.parts
    family, module = parts[1], parts[2]
    inner = list(parts[3:-1])

    if shorten:
        if inner and inner[0] == "src":  # src/[main|test]/[java|kotlin|resources]/...
            inner = inner[1:]
            if inner and inner[0] in _SOURCE_SET:
                inner = inner[1:]
            if inner and inner[0] in _SOURCE_LANG:
                inner = inner[1:]
        while inner and inner[0] in _THETA_PACKAGE:  # hu/bme/mit/theta
            inner = inner[1:]
        if inner and inner[0] == module.replace("-", ""):  # ...theta/core/type -> type
            inner = inner[1:]

    return posixpath.join("Modules", family, module, *inner, MODULE_DOCS[rel.name])


def _discover(config):
    """Return (absolute path, destination uri) for every doc the wiki should mirror."""
    wiki_dir = Path(config["config_file_path"]).parent

    module_docs = [
        path
        for path in sorted((REPO_ROOT / "subprojects").rglob("*.md"))
        if path.name in MODULE_DOCS and "build" not in path.parts
    ]
    # Two docs can shorten to the same nav path (e.g. a module's own README and one in
    # its resources). Keep the short path where it is unambiguous, spell it out otherwise.
    shortened = [_module_dest(p.relative_to(REPO_ROOT)) for p in module_docs]
    clashing = {dest for dest in shortened if shortened.count(dest) > 1}

    found = []
    for path, dest in zip(module_docs, shortened):
        if dest in clashing:
            dest = _module_dest(path.relative_to(REPO_ROOT), shorten=False)
        found.append((path, dest))

    for path in sorted((REPO_ROOT / "doc").rglob("*.md")):
        if wiki_dir not in path.parents:
            found.append(
                (path, posixpath.join("Guides", path.relative_to(REPO_ROOT / "doc").as_posix()))
            )

    root_claude = REPO_ROOT / "CLAUDE.md"
    if root_claude.is_file():
        found.append((root_claude, "Guides/repository-guide.md"))

    return found


def _page_source(path: Path, dest_uri: str) -> str:
    rel = path.relative_to(REPO_ROOT).as_posix()
    banner = _BANNERS.get(path.name, _BANNERS["README.md"])
    banner = banner.format(path=rel, url=GITHUB_BLOB + rel)

    front_matter = [f'source_dir: "{posixpath.dirname(rel)}"']
    if path.name in MODULE_DOCS and dest_uri.startswith("Modules/"):
        front_matter.append(f'title: "{_title_for(path.relative_to(REPO_ROOT))}"')

    return "---\n{}\n---\n\n{}\n{}".format(
        "\n".join(front_matter), banner, path.read_text(encoding="utf-8")
    )


def on_files(files, config):
    """Inject the out-of-tree docs as ordinary wiki pages."""
    for path, dest_uri in _discover(config):
        files.append(
            File.generated(config, dest_uri, content=_page_source(path, dest_uri))
        )
    return files


def on_page_content(html, page, config, files):
    """Rewrite links of mirrored pages so they resolve on the published site."""
    source_dir = page.meta.get("source_dir")
    if source_dir is None:
        return html

    def rewrite(match, base):
        target = match.group(2)
        parts = urlsplit(target)
        if parts.scheme or parts.netloc or not parts.path:
            return match.group(0)  # absolute URL, or a bare #anchor
        resolved = posixpath.normpath(posixpath.join(source_dir, parts.path))
        anchor = f"#{parts.fragment}" if parts.fragment else ""
        return f"{match.group(1)}{base}{resolved}{anchor}{match.group(3)}"

    html = _HREF_RE.sub(lambda m: rewrite(m, GITHUB_BLOB), html)
    return _IMG_RE.sub(lambda m: rewrite(m, GITHUB_RAW), html)


# Material renders the site name in the header as plain text; only the logo links home.
# Make the name a link too, reusing the logo's (correctly relativised) href.
_LOGO_HREF_RE = re.compile(r'<a href="([^"]*)"[^>]*class="md-header__button md-logo"')
_SITE_NAME_RE = re.compile(
    r'(<div class="md-header__topic">\s*<span class="md-ellipsis">)(\s*)([^<]+?)(\s*)(</span>)'
)


def on_post_page(output, page, config):
    logo = _LOGO_HREF_RE.search(output)
    if not logo:
        return output
    home = logo.group(1)

    def link_site_name(match):
        open_tag, lead, name, trail, close_tag = match.groups()
        return (
            f'{open_tag}{lead}<a href="{home}" class="md-header__site-link">{name}</a>'
            f"{trail}{close_tag}"
        )

    return _SITE_NAME_RE.sub(link_site_name, output, count=1)
