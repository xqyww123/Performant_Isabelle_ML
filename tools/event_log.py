#!/usr/bin/env python3
"""Reference reader for Event_Log files (EVENT_LOG_PLAN.md, section 8).

A log file is a sequence of top-level items -- <record> elements and
<!-- ... --> comments -- and the writer guarantees that a line's first byte
is "<" exactly at the start of an item: it inserts one extra space after
every newline that is followed by optional spaces and "<".  The reader
splits on lines starting with "<", then deletes exactly one space after
every newline followed by spaces and "<", restoring content byte-for-byte.

One corrupt item loses only itself: every chunk is parsed independently and
bad chunks are skipped (count them via the `bad` callback if you care).

Typical use:

    from event_log import records
    import pandas as pd
    df = pd.DataFrame(r.attrib for r in records(path))
"""

import argparse
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

_BOUNDARY = re.compile(r"\n(?=<)")
_UNSTUFF = re.compile(r"\n (?= *<)")


def chunks(text):
    """Split a log file's text into per-item strings, unstuffed."""
    for chunk in _BOUNDARY.split(text):
        chunk = chunk.rstrip("\n")  # the trailing newline the writer appends
        if chunk:
            yield _UNSTUFF.sub("\n", chunk)


def records(path, bad=None):
    """Yield one xml.etree Element per well-formed <record> in `path`.

    Comments are skipped silently; a chunk that fails to parse is passed to
    `bad` (if given) and skipped."""
    text = Path(path).read_text(encoding="utf-8", errors="replace")
    for chunk in chunks(text):
        if chunk.startswith("<!--"):
            continue
        try:
            elem = ET.fromstring(chunk)
        except ET.ParseError:
            if bad is not None:
                bad(chunk)
            continue
        if elem.tag == "record":
            yield elem


def log_files(path):
    """`path` is a log file, a category directory, or the log directory."""
    path = Path(path)
    if path.is_dir():
        return sorted(p for p in path.rglob("*.xml") if p.is_file())
    return [path]


def main():
    parser = argparse.ArgumentParser(
        description="Dump Event_Log record attributes as TSV.")
    parser.add_argument("paths", nargs="+",
                        help="log files, category directories, or the log directory")
    args = parser.parse_args()

    rows, columns, n_bad = [], [], 0

    def bad(_chunk):
        nonlocal n_bad
        n_bad += 1

    for path in args.paths:
        for f in log_files(path):
            for record in records(f, bad=bad):
                rows.append(record.attrib)
                for key in record.attrib:
                    if key not in columns:
                        columns.append(key)

    print("\t".join(columns))
    for row in rows:
        print("\t".join(row.get(key, "").replace("\t", " ").replace("\n", " ")
                        for key in columns))
    if n_bad:
        print(f"({n_bad} corrupt record(s) skipped)", file=sys.stderr)


if __name__ == "__main__":
    main()
