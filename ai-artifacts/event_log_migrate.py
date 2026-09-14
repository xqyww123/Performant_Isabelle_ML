#!/usr/bin/env python3
"""One-off migration of Event_Log files from the space-stuffed format to the
marker format (EVENT_LOG_PLAN.md section 5, revision of 2026-09-14).

Old format: an item begins at a line whose first byte is "<"; every other line
that starts with optional spaces and "<" carries one extra stuffed space.
New format: every item is preceded by the line "<!-- record -->".

Usage: event_log_migrate.py <log directory or file>...
A file already in the new format (it starts with the marker) is left alone.
Each file is rewritten only when the number of well-formed <record> elements
read from the new text equals the number read from the old text; the rewrite
is atomic (temp file + os.replace).
"""

import os
import re
import sys
import tempfile
import xml.etree.ElementTree as ET
from pathlib import Path

MARKER = "<!-- record -->"
_OLD_BOUNDARY = re.compile(r"\n(?=<)")
_OLD_UNSTUFF = re.compile(r"\n (?= *<)")


def old_chunks(text):
    for chunk in _OLD_BOUNDARY.split(text):
        chunk = chunk.rstrip("\n")
        if chunk:
            yield _OLD_UNSTUFF.sub("\n", chunk)


def new_chunks(text):
    for chunk in text.split(MARKER):
        chunk = chunk.strip("\n")
        if chunk:
            yield chunk


def count_records(chunks):
    n = 0
    for chunk in chunks:
        if chunk.startswith("<!--"):
            continue
        try:
            if ET.fromstring(chunk).tag == "record":
                n += 1
        except ET.ParseError:
            pass
    return n


def migrate(path: Path) -> str:
    text = path.read_text(encoding="utf-8", errors="surrogateescape")
    if text.startswith(MARKER) or not text.strip():
        return "kept"
    items = list(old_chunks(text))
    new_text = "".join(MARKER + "\n" + item + "\n" for item in items)
    n_old = count_records(items)
    n_new = count_records(new_chunks(new_text))
    if n_old != n_new:
        return f"REFUSED (records old={n_old} new={n_new})"
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=path.name, suffix=".migrating")
    with os.fdopen(fd, "w", encoding="utf-8", errors="surrogateescape") as out:
        out.write(new_text)
    os.replace(tmp, path)
    return f"migrated ({n_new} records, {len(items)} items)"


def main():
    files = []
    for arg in sys.argv[1:]:
        p = Path(arg)
        files += sorted(q for q in p.rglob("*.xml") if q.is_file()) if p.is_dir() else [p]
    summary = {}
    for f in files:
        result = migrate(f)
        summary[result.split(" ")[0]] = summary.get(result.split(" ")[0], 0) + 1
        if not result.startswith("migrated") and result != "kept":
            print(f"{f}: {result}")
    print(summary)


if __name__ == "__main__":
    main()
