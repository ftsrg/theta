"""MkDocs hooks for the Theta wiki.

Link fix-up for pages that transclude a markdown file living elsewhere in the
repo (via pymdownx.snippets). Such files use repo-relative links that mean
nothing on the published site, so on pages that declare a `source_dir` in
their front-matter, every relative link is rewritten to point at the file on
GitHub, resolved against that directory.
"""

import posixpath
import re
from urllib.parse import urlsplit

GITHUB_BASE = "https://github.com/ftsrg/theta/blob/master/"

_HREF_RE = re.compile(r'(<a href=")([^"]+)(")')


def on_page_content(html, page, config, files):
    source_dir = page.meta.get("source_dir")
    if not source_dir:
        return html

    def rewrite(match):
        href = match.group(2)
        parts = urlsplit(href)
        if parts.scheme or parts.netloc or not parts.path:
            return match.group(0)  # absolute URL or pure #anchor: leave alone
        resolved = posixpath.normpath(posixpath.join(source_dir, parts.path))
        anchor = f"#{parts.fragment}" if parts.fragment else ""
        return f"{match.group(1)}{GITHUB_BASE}{resolved}{anchor}{match.group(3)}"

    return _HREF_RE.sub(rewrite, html)
