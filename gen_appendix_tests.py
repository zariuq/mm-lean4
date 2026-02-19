#!/usr/bin/env python3
"""Generate appendix_tests.tex from the metamath-test suite.

Parses run-testsuite-all for unit/ and core/small/ tests, groups by spec
reference, extracts spec text from SPEC_SECTION_4.txt, and includes .mm
file content as LaTeX listings.

Usage: python3 gen_appendix_tests.py
"""

import re
import os
from collections import defaultdict

TESTS_ROOT = "/home/zar/claude/hyperon/metamath/metamath-test"
MANIFEST = os.path.join(TESTS_ROOT, "run-testsuite-all")
SPEC_FILE = os.path.join(TESTS_ROOT, "SPEC_SECTION_4.txt")
OUTPUT = "appendix_tests.tex"

# Maximum lines for a .mm file to be included verbatim (skip huge ones)
MAX_LINES = 70

# Spec section ordering (for grouping)
SECTION_ORDER = [
    "L73-79",    # Character set
    "L77-79",    # Whitespace
    "L81-83",    # Token separation
    "L89-91",    # Comments
    "L105-106",  # Outermost scope
    "L153-155",  # Block delimiters
    "L156-158",  # $f global
    "L161-163",  # Declarations
    "L167-169",  # Labels
    "L174-175",  # $f scope
    "L174-178",  # Variable scope
    "L177-178",  # Variable must have $f
    "L179-180",  # Label uniqueness
    "L182-184",  # Mandatory hypotheses
    "L200-203",  # Proof labels (earlier)
    "L204-205",  # Self-substitution
    "L208-212",  # Typecode match
    "L211-214",  # Mandatory hyp order
    "L213-218",  # Proof labels
    "L218-220",  # Stack match
    "L221-223",  # ? steps
    "L286-292",  # Typecodes
    "L339-342",  # Math symbols
    "L547-549",  # $d syntax
    "L553-558",  # Duplicate $d
    "L1088",     # $c outermost
    "L1114-1115",# Missing $p
    "L1894-1895",# Compressed ?
    "4.2.1",     # Proof verification
    "4.2.5",     # Active hypotheses
    "4.2.6",     # $d symbols
    "4.2.7",     # $d violations
    "4.2.8",     # Includes
    "4.4",       # Compressed proof
    "AppB",      # Compressed format
    "Valid",     # Valid databases
    "other",     # Everything else
]


def load_spec_lines():
    """Load SPEC_SECTION_4.txt as a list of lines (1-indexed)."""
    with open(SPEC_FILE, "r") as f:
        return [""] + f.readlines()  # 1-indexed


def extract_spec_text(spec_lines, ref):
    """Extract spec text for a line reference like 'L73-79'."""
    m = re.match(r"L(\d+)(?:-(\d+))?", ref)
    if not m:
        return None
    start = int(m.group(1))
    end = int(m.group(2)) if m.group(2) else start
    if start >= len(spec_lines) or end >= len(spec_lines):
        return None
    return "".join(spec_lines[start : end + 1]).strip()


def parse_manifest():
    """Parse run-testsuite-all for pass/fail entries."""
    tests = []
    with open(MANIFEST, "r") as f:
        for line in f:
            line = line.strip()
            m = re.match(r'^(pass|fail)\s+((?:unit|core/small)/\S+)\s+"(.+)"', line)
            if m:
                verdict = m.group(1).upper()
                path = m.group(2)
                desc = m.group(3)
                tests.append((verdict, path, desc))
    return tests


def classify_spec_ref(desc):
    """Extract the spec reference key from a test description."""
    # Try Lxx-yy pattern first
    m = re.match(r"(L\d+(?:-\d+)?)", desc)
    if m:
        return m.group(1)
    # Try section refs like 4.2.7, 4.4, AppB
    m = re.match(r"((?:4\.\d+(?:\.\d+)?|AppB))", desc)
    if m:
        return m.group(1)
    # "Valid database" or similar
    if desc.startswith("Valid") or desc.startswith("Empty"):
        return "Valid"
    # SPEC DIVERGENCE
    if "SPEC DIVERGENCE" in desc:
        return "Valid"  # accepted by all implementations
    # EBNF
    if "EBNF" in desc:
        return "Valid"
    return "other"


def read_mm_file(path):
    """Read a .mm test file, return (content, line_count)."""
    full = os.path.join(TESTS_ROOT, "tests", path)
    if not os.path.exists(full):
        return None, 0
    with open(full, "r") as f:
        content = f.read()
    return content, content.count("\n") + (1 if content and not content.endswith("\n") else 0)


def escape_latex(s):
    """Escape special LaTeX characters in prose text."""
    # Order matters: backslash first, then others
    out = []
    for ch in s:
        if ch == '\\':
            out.append('\\textbackslash{}')
        elif ch == '{':
            out.append('\\{')
        elif ch == '}':
            out.append('\\}')
        elif ch == '$':
            out.append('\\$')
        elif ch == '#':
            out.append('\\#')
        elif ch == '%':
            out.append('\\%')
        elif ch == '&':
            out.append('\\&')
        elif ch == '_':
            out.append('\\_')
        elif ch == '^':
            out.append('\\^{}')
        elif ch == '~':
            out.append('\\~{}')
        else:
            out.append(ch)
    return ''.join(out)


def escape_filename(s):
    """Escape a filename for LaTeX text (only _ and $ need escaping)."""
    s = s.replace("_", "\\_")
    s = s.replace("$", "\\$")
    return s


def section_title(ref, tests_in_group):
    """Generate a human-readable section title for a spec reference."""
    titles = {
        "L73-79": "Character Set (L73--79)",
        "L77-79": "Whitespace Characters (L77--79)",
        "L81-83": "Token Separation (L81--83)",
        "L89-91": "Comment Delimiters (L89--91)",
        "L105-106": "Outermost Scope (L105--106)",
        "L153-155": "Block Delimiters (L153--155)",
        "L156-158": "\\$f Type Globality (L156--158)",
        "L161-163": "Constant/Variable Declarations (L161--163)",
        "L167-169": "Label Syntax (L167--169)",
        "L174-175": "\\$f Scope (L174--175)",
        "L174-178": "Variable Scope (L174--178)",
        "L177-178": "Variable Must Have \\$f (L177--178)",
        "L179-180": "Label Uniqueness (L179--180)",
        "L182-184": "Mandatory Hypotheses (L182--184)",
        "L200-203": "Proof Label References (L200--203)",
        "L204-205": "Self-Substitution (L204--205)",
        "L208-212": "Typecode Matching (L208--212)",
        "L211-214": "Mandatory Hypothesis Order (L211--214)",
        "L213-218": "Proof Labels (L213--218)",
        "L218-220": "Stack Matching (L218--220)",
        "L221-223": "Unknown Steps (L221--223)",
        "L286-292": "Typecodes in \\$f (L286--292)",
        "L339-342": "Math Symbol Syntax (L339--342)",
        "L547-549": "\\$d Syntax (L547--549)",
        "L553-558": "Duplicate \\$d (L553--558)",
        "L1088": "\\$c Outermost Scope (L1088)",
        "L1114-1115": "Missing \\$p (L1114--1115)",
        "L1894-1895": "Compressed Proof ? (L1894--1895)",
        "4.2.1": "Proof Verification Failures (\\S4.2.1)",
        "4.2.5": "Active Hypotheses (\\S4.2.5)",
        "4.2.6": "\\$d Symbol Requirements (\\S4.2.6)",
        "4.2.7": "Disjoint Variable Violations (\\S4.2.7)",
        "4.2.8": "Include Processing (\\S4.2.8)",
        "4.4": "Compressed Proof Format (\\S4.4)",
        "AppB": "Compressed Proof Encoding (Appendix B)",
        "Valid": "Valid Databases (Positive Tests)",
        "other": "Miscellaneous",
    }
    return titles.get(ref, ref)


def main():
    spec_lines = load_spec_lines()
    tests = parse_manifest()

    # Group by spec reference
    groups = defaultdict(list)
    for verdict, path, desc in tests:
        ref = classify_spec_ref(desc)
        groups[ref].append((verdict, path, desc))

    # Collect skipped (too large) files
    skipped = []

    with open(OUTPUT, "w") as out:
        out.write("% Auto-generated by gen_appendix_tests.py\n")
        out.write("% Source: metamath-test/run-testsuite-all\n\n")

        for ref in SECTION_ORDER:
            if ref not in groups:
                continue
            entries = groups[ref]

            title = section_title(ref, entries)
            out.write(f"\\subsection{{{title}}}\n\n")

            # Extract spec text if it's a line reference
            spec_text = extract_spec_text(spec_lines, ref)
            if spec_text:
                out.write("\\begin{quote}\\small\\itshape\n")
                # Escape for LaTeX but keep it readable
                safe = escape_latex(spec_text)
                out.write(safe + "\n")
                out.write("\\end{quote}\n\n")

            for verdict, path, desc in entries:
                content, nlines = read_mm_file(path)
                fname = os.path.basename(path)

                if nlines > MAX_LINES:
                    skipped.append((fname, verdict, nlines, desc))
                    continue

                if content is None:
                    continue

                # Verdict badge
                badge = "ACCEPT" if verdict == "PASS" else "REJECT"

                safe_fname = escape_filename(fname)
                # Add soft break points in prose-like descriptors.
                safe_desc = escape_latex(desc).replace("+", " + ")

                out.write(f"\\noindent\\textbf{{{safe_fname}}} [{badge}] "
                          f"\\textit{{{safe_desc}}}\\par\n\n")
                out.write("\\begin{lstlisting}[language=Metamath,"
                          "basicstyle=\\ttfamily\\scriptsize,"
                          "frame=single,framerule=0.3pt,"
                          "rulecolor=\\color{black!20},"
                          "backgroundcolor=\\color{black!2},"
                          "xleftmargin=1em,framexleftmargin=0.5em,"
                          "numbers=none,aboveskip=0.5em,belowskip=0.3em]\n")
                # Write content, stripping trailing whitespace
                for line in content.rstrip().split("\n"):
                    out.write(line.rstrip() + "\n")
                out.write("\\end{lstlisting}\n\n")

        # Summary table for skipped files
        if skipped:
            out.write("\\subsection{Large Test Files (Summary Only)}\n\n")
            out.write("The following test files exceed 70 lines and are "
                      "summarized rather than listed verbatim.\n\n")
            out.write("\\begin{tabular}{llrl}\n")
            out.write("\\toprule\n")
            out.write("\\textbf{File} & \\textbf{Verdict} & "
                      "\\textbf{Lines} & \\textbf{Spec Rule} \\\\\n")
            out.write("\\midrule\n")
            for fname, verdict, nlines, desc in skipped:
                badge = "ACCEPT" if verdict == "PASS" else "REJECT"
                safe = escape_filename(fname)
                sdesc = escape_latex(desc)
                out.write(f"\\texttt{{{safe}}} & {badge} & "
                          f"{nlines} & {sdesc} \\\\\n")
            out.write("\\bottomrule\n")
            out.write("\\end{tabular}\n\n")

    print(f"Generated {OUTPUT}")
    print(f"  Tests included: {sum(len(v) for v in groups.values()) - len(skipped)}")
    print(f"  Tests skipped (too large): {len(skipped)}")


if __name__ == "__main__":
    main()
