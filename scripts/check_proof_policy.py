#!/usr/bin/env python3
"""Enforce the repository's source, statement and axiom policy.

This guard is not Comparator and not an independent kernel. It checks:

1. every Lean file outside `.lake` and `.git` (project, vendored libraries, Challenge,
   Solution), with comments and string literals masked, for placeholders and
   proof-bypass constructs; `Challenge.lean` may contain exactly its two intentional
   placeholders, each the whole body of one compared theorem;
2. that `Solution.lean` states the two compared theorems with exactly the statements of
   `Challenge.lean`, that the development's theorems in `PrimeCarleson/Frozen` have the same
   statements, and that each definition stated in `Challenge.lean` is the development's
   definition in `PrimeCarleson/Frozen`, character for character;
3. that `comparator.json` names exactly the two compared theorems and permits only
   `propext`, `Classical.choice` and `Quot.sound`;
4. unless `--source-only` is given: the transitive axioms of the audited declarations, by
   Lean's `#print axioms` on the built project (run `lake build` first).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
CHALLENGE = ROOT / "Challenge.lean"
SOLUTION = ROOT / "Solution.lean"
FROZEN = ROOT / "PrimeCarleson" / "Frozen"
COMPARATOR_CONFIG = ROOT / "comparator.json"

# Compared theorem (short name) -> the development's theorem it is proved by, and its file.
CHALLENGE_THEOREMS = {
    "variation_norm_prime_carleson": "VariationNormPrimeCarleson.lean",
    "prime_carleson_maximal": "PrimeCarlesonMaximal.lean",
}
COMPARED = tuple("PrimeCarleson.Palomar." + name for name in CHALLENGE_THEOREMS)
# Definition stated in Challenge.lean -> the development's file that defines it.
CHALLENGE_DEFINITIONS = {
    "e": "Exp.lean",
    "rVariation": "RVariation.lean",
    "modulatedSum": "ModulatedSum.lean",
    "primeVariation": "PrimeVariation.lean",
    "carlesonMax": "CarlesonMax.lean",
}
AXIOM_AUDIT = COMPARED + tuple(
    "PrimeCarleson." + name
    for name in (
        "variation_norm_prime_carleson",
        "prime_carleson_maximal",
        "variation_norm_carleson_real",
        "msw_transference_variation",
        "vonMangoldt_sub_heathBrown_U3",
        "periodicBlockMax_bound",
        "admissible_sineWeight_carleson_unbounded",
        "gowersNorm_spec",
    )
)
AUDIT_IMPORTS = (
    "Solution",
    "PrimeCarleson.Frozen.VariationNormCarlesonReal",
    "PrimeCarleson.Frozen.MswTransferenceVariation",
    "PrimeCarleson.Frozen.VonMangoldtSubHeathBrownU3",
    "PrimeCarleson.Frozen.PeriodicBlockMaxBound",
    "PrimeCarleson.Frozen.AdmissibleSineWeightCarlesonUnbounded",
    "PrimeCarleson.Frozen.GowersNormSpec",
)

# Searched in sources whose comments and string literals are masked.
FORBIDDEN = re.compile(
    r"(?<![.\w])stop\b(?!\s*:)|"  # the `stop` tactic, not a field `stop : …` or `h.stop`
    r"\b(sorry|admit|sorryAx|axiom|axioms|implemented_by|extern|native_decide|"
    r"ofReduceBool|ofReduceNat|trustCompiler|run_tac|run_cmd|run_elab|opaque|"
    r"initialize|builtin_initialize|simproc|dsimproc|simproc_decl|"
    r"macro|elab|macro_rules|elab_rules|syntax|declare_syntax_cat)\b|"
    r"\bunsafe\b(?!\s+(\d+%\s+)?(apply|cases|constructors|destruct|forward)\b)|"
    r"@\[\s*(command_elab|term_elab|tactic|csimp|init|builtin_init)\b|"
    r"debug\.skipKernelTC|kernel\.trust|#eval\b|#exit\b"
)
# Top-level commands allowed in Challenge.lean (masked; indented lines are continuations).
CHALLENGE_COMMANDS = re.compile(
    r"(module|public import Mathlib(\.[A-Za-z0-9_.]+)?|@\[expose\] public noncomputable section|"
    r"open( scoped)? [A-Za-z][A-Za-z0-9_. ]*|set_option autoImplicit false|"
    r"namespace [A-Za-z][A-Za-z0-9_.]*|end [A-Za-z][A-Za-z0-9_.]*|def \S+ .*|theorem \S+ .*)"
)
IDENT_CHAR = re.compile(r"[A-Za-z0-9_'!?Ͱ-Ͽἀ-῿₀-ₜᵢ-ᵪ]")
CHAR_LITERAL = re.compile(r"'(\\(x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'")
RAW_STRING = re.compile(r'r(#*)"')
PLACEHOLDER = re.compile(r"^[ \t]*sorry[ \t]*$", re.MULTILINE)
REPORT = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",
    re.MULTILINE,
)
COMPARATOR_KEYS = frozenset({
    "challenge_module", "solution_module", "theorem_names", "permitted_axioms",
    "definition_names", "enable_nanoda",
})


def mask(text: str) -> str:
    """Blank out comments (nested block comments included), string, raw-string and character
    literals. The result has the same length and line structure as the input."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        after_ident = i > 0 and IDENT_CHAR.match(text[i - 1]) is not None
        if not depth and text[i] == "'" and not after_ident and (m := CHAR_LITERAL.match(text, i)):
            out.append("'" + " " * (m.end() - i - 2) + "'")
            i = m.end()
        elif not depth and text[i] == "r" and not after_ident and (m := RAW_STRING.match(text, i)):
            close = '"' + m.group(1)
            j = text.find(close, m.end())
            if j < 0:
                raise ValueError("unterminated raw string literal")
            body = text[m.end():j]
            out.append(text[i:m.end()] + re.sub(r"[^\n]", " ", body) + close)
            i = j + len(close)
        elif text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth:
            if text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if j >= n:
                raise ValueError("unterminated string literal")
            out.append('"' + re.sub(r"[^\n]", " ", text[i + 1:j]) + '"')
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("unterminated block comment")
    return "".join(out)


def lean_sources() -> list[Path]:
    files = []
    for directory, directories, names in os.walk(ROOT):
        directories[:] = sorted(d for d in directories if d not in {".lake", ".git"})
        for name in directories + sorted(names):
            path = Path(directory) / name
            if path.is_symlink():
                raise ValueError(f"symlink could evade the scan: {path.relative_to(ROOT)}")
            if name.endswith(".lean") and path.is_file():
                files.append(path)
    return files


def forbidden_matches(path: Path, text: str) -> list[str]:
    masked = mask(text)
    lines = masked.splitlines()
    return [
        f"{path.relative_to(ROOT)}:{masked.count(chr(10), 0, m.start()) + 1}: "
        f"{lines[masked.count(chr(10), 0, m.start())].strip()[:100]}"
        for m in FORBIDDEN.finditer(masked)
    ]


def validate_challenge_source(challenge: str) -> None:
    masked = mask(challenge)
    if len(PLACEHOLDER.findall(masked)) != len(CHALLENGE_THEOREMS):
        raise ValueError("Challenge.lean must contain exactly one placeholder per compared theorem.")
    for name in CHALLENGE_THEOREMS:
        body = re.compile(
            rf"^theorem {re.escape(name)}\b(?:(?!^theorem\b).)*?:=\s*by\s*\n[ \t]*sorry[ \t]*$",
            re.MULTILINE | re.DOTALL,
        )
        if not body.search(masked):
            raise ValueError(f"the placeholder of Challenge.lean must be the body of {name}")
    rest = PLACEHOLDER.sub("", masked)
    if FORBIDDEN.search(rest):
        raise ValueError("Challenge.lean contains a forbidden construct outside its placeholders.")
    for number, line in enumerate(masked.splitlines(), start=1):
        if line.strip() and not line[0].isspace() and not CHALLENGE_COMMANDS.fullmatch(line.rstrip()):
            raise ValueError(f"Challenge.lean:{number}: command not allowed in the challenge: "
                             f"{line.strip()[:60]}")


def unique_span(source: str, pattern: str, where: str, what: str, group: int = 0) -> str:
    """Locate `pattern` in the masked source, exactly once, and return the original text there
    (masking preserves offsets, so a commented-out decoy cannot be matched)."""
    matches = list(re.finditer(pattern, mask(source), re.MULTILINE | re.DOTALL))
    if len(matches) != 1:
        raise ValueError(f"{where} must contain exactly one {what}; found {len(matches)}")
    return source[matches[0].start(group):matches[0].end(group)]


def theorem_statement(source: str, name: str, where: str) -> str:
    """The text from `theorem <name>` up to the `:=` that ends its statement."""
    return unique_span(source, rf"^theorem {re.escape(name)}\b(.*?):=[ \t]*(?:by[ \t]*)?$",
                       where, f"theorem {name}", group=1).strip()


def definition_text(source: str, name: str, where: str) -> str:
    """The text of `def <name>` through the end of its body (the next blank or `end` line)."""
    text = unique_span(source, rf"^(?:noncomputable )?def {re.escape(name)}\b.*?(?=^\s*$|^end\b)",
                       where, f"definition {name}")
    return "\n".join(line.rstrip() for line in text.strip().splitlines())


def check_statements() -> None:
    challenge = CHALLENGE.read_text(encoding="utf-8")
    solution = SOLUTION.read_text(encoding="utf-8")
    validate_challenge_source(challenge)
    if re.search(r"^\s*(public\s+)?import\s+Challenge\b", solution, re.MULTILINE):
        raise ValueError("Solution.lean must not import Challenge.lean.")
    if not re.search(r"^namespace PrimeCarleson\.Palomar$", solution, re.MULTILINE):
        raise ValueError("Solution.lean must state the theorems in PrimeCarleson.Palomar.")
    for name, frozen_file in CHALLENGE_THEOREMS.items():
        stated = theorem_statement(challenge, name, "Challenge.lean")
        proved = theorem_statement(solution, name, "Solution.lean")
        frozen = theorem_statement((FROZEN / frozen_file).read_text(encoding="utf-8"), name,
                                   f"PrimeCarleson/Frozen/{frozen_file}")
        if not stated == proved == frozen:
            raise ValueError(f"the statements of {name} differ between Challenge.lean, "
                             f"Solution.lean and PrimeCarleson/Frozen/{frozen_file}")
        if not re.search(rf"^theorem {name}\b.*?:=\s*\n\s*PrimeCarleson\.{name}\s*$",
                         solution, re.MULTILINE | re.DOTALL):
            raise ValueError(f"Solution.lean must prove {name} by PrimeCarleson.{name}")
    for name, frozen_file in CHALLENGE_DEFINITIONS.items():
        if definition_text(challenge, name, "Challenge.lean") != definition_text(
                (FROZEN / frozen_file).read_text(encoding="utf-8"), name,
                f"PrimeCarleson/Frozen/{frozen_file}"):
            raise ValueError(f"the definition {name} of Challenge.lean is not the development's")
    defined = set(re.findall(r"^(?:noncomputable )?def (\S+)", mask(challenge), re.MULTILINE))
    if defined != set(CHALLENGE_DEFINITIONS):
        raise ValueError(f"Challenge.lean defines {sorted(defined)}, expected "
                         f"{sorted(CHALLENGE_DEFINITIONS)}")
    stated = set(re.findall(r"^theorem (\S+)", mask(challenge), re.MULTILINE))
    if stated != set(CHALLENGE_THEOREMS):
        raise ValueError(f"Challenge.lean states {sorted(stated)}, expected "
                         f"{sorted(CHALLENGE_THEOREMS)}")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def validate_config(config) -> None:
    if not isinstance(config, dict):
        raise ValueError("comparator.json must be a JSON object")
    if set(config) - COMPARATOR_KEYS:
        raise ValueError(f"unknown comparator.json keys: {sorted(set(config) - COMPARATOR_KEYS)}")
    permitted = config.get("permitted_axioms")
    if (not isinstance(permitted, list) or not all(isinstance(a, str) for a in permitted)
            or not set(permitted) <= ALLOWED_AXIOMS):
        raise ValueError("permitted_axioms must be a subset of propext, Classical.choice, Quot.sound")
    if config.get("enable_nanoda") is not True:
        raise ValueError("comparator.json must enable NanoDa")


def check_config() -> None:
    config = json.loads(COMPARATOR_CONFIG.read_text(encoding="utf-8"),
                        object_pairs_hook=unique_object)
    validate_config(config)
    if (config.get("challenge_module") != "Challenge"
            or config.get("solution_module") != "Solution"
            or config.get("theorem_names") != list(COMPARED)):
        raise ValueError("comparator.json must name Challenge, Solution and the two compared theorems")


def check_sources() -> None:
    files = lean_sources()
    if len(files) < 100:
        raise ValueError("too few Lean files found; refusing an empty scan")
    matches = []
    for path in files:
        text = path.read_text(encoding="utf-8")
        if not re.match(r"(\s*(--[^\n]*|/-.*?-/))*\s*module\b", text, re.DOTALL):
            matches.append(f"{path.relative_to(ROOT)}: no `module` header")
        if path != CHALLENGE:
            matches.extend(forbidden_matches(path, text))
    if matches:
        raise ValueError("forbidden constructs:\n" + "\n".join(matches))
    check_statements()
    check_config()
    print(f"PASS: source policy ({len(files)} Lean files, all modules; the two placeholders of "
          "Challenge.lean are the bodies of the compared theorems).")
    print("PASS: Challenge, Solution and PrimeCarleson/Frozen state the same two theorems and "
          "the same five definitions; comparator.json names exactly those theorems.")


def validate_reports(output: str, expected) -> None:
    reports = list(REPORT.finditer(output))
    names = [report.group(1) for report in reports]
    if len(names) != len(expected) or set(names) != set(expected):
        raise ValueError("missing, duplicate or unexpected axiom reports:\n" + output)
    for report in reports:
        used = {a.strip() for a in (report.group(2) or "").split(",") if a.strip()}
        if used - ALLOWED_AXIOMS:
            raise ValueError(f"{report.group(1)} depends on {sorted(used - ALLOWED_AXIOMS)}")


def check_axioms() -> None:
    probe_text = "".join(f"import {module}\n" for module in AUDIT_IMPORTS) + "\n" + "".join(
        f"#print axioms {name}\n" for name in AXIOM_AUDIT)
    with tempfile.TemporaryDirectory() as directory:
        probe = Path(directory) / "AxiomAudit.lean"
        probe.write_text(probe_text, encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                                capture_output=True, text=True)
    if result.returncode != 0:
        raise ValueError("the axiom audit failed:\n" + result.stdout + result.stderr)
    print(result.stdout, end="")
    validate_reports(result.stdout, AXIOM_AUDIT)
    print(f"PASS: all {len(AXIOM_AUDIT)} audited declarations use only propext, "
          "Classical.choice and Quot.sound.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--source-only", action="store_true",
                        help="check sources and configuration only; skip the axiom audit")
    args = parser.parse_args()
    check_sources()
    if args.source_only:
        print("NOTE: the axiom audit was not run (--source-only).")
    else:
        check_axioms()


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
