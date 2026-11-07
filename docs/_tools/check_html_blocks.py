#!/usr/bin/env python3
"""Fail when a docs page puts Markdown inside a raw HTML block that kramdown will not parse.

GitHub Pages renders these pages with kramdown, which treats the body of a block-level HTML
element (`<details>`, `<div>`, ...) as raw HTML unless the opening tag carries `markdown="1"`.
GitHub's own README renderer does parse it, so a page can look right on github.com and still
publish tables and code fences as literal `| a | b |` and three-backtick text.

Usage: python3 docs/_tools/check_html_blocks.py [docs-dir]   (exit 1 on any finding)
"""
import re
import sys
from pathlib import Path

BLOCK_TAGS = "details|div|section|aside|blockquote"
OPEN = re.compile(rf"^\s*<({BLOCK_TAGS})(\s[^>]*)?>\s*$")
MARKDOWN = re.compile(r"^\s*(\|.*\||```|~~~|[-*+] |\d+\. |#{1,6} )")


def findings(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines):
        m = OPEN.match(line)
        if not m or "markdown=" in (m.group(2) or ""):
            continue
        tag, depth = m.group(1), 0
        for j in range(i, len(lines)):
            depth += len(re.findall(rf"<{tag}[\s>]", lines[j])) - len(re.findall(rf"</{tag}>", lines[j]))
            if j > i and MARKDOWN.match(lines[j]):
                yield i + 1, tag, lines[j].strip()[:60]
                break
            if depth <= 0:
                break


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parents[1])
    bad = [(p, *f) for p in sorted(root.rglob("*.md")) for f in findings(p)]
    for p, line, tag, sample in bad:
        print(f"{p}:{line}: <{tag}> holds Markdown ({sample!r}) but lacks markdown=\"1\"")
    print(f"check_html_blocks: {len(bad)} finding(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
