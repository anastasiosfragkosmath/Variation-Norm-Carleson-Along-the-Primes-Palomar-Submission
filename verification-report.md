# Verification boundary and reproducible checks

This file intentionally does not claim a Comparator run or a registry verification for this or
any other revision. Verification evidence applies to the exact commit that was checked.

## Local Lean checks

With the pinned `lean-toolchain` (Lean v4.35.0) and the committed `lake-manifest.json`
(Mathlib v4.35.0, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`), run:

```sh
lake exe cache get
lake build
python3 -B scripts/test_proof_policy.py
python3 -B scripts/check_proof_policy.py
```

The first command downloads Mathlib's prebuilt files. `lake build` compiles all 1,796 Lean
files of this repository: the project library `PrimeCarleson`, the vendored libraries `OAI` and
`Carleson`, `Challenge` and `Solution`. Every declaration is checked by the Lean kernel when its
module is compiled. The only `sorry` warnings are the two intentional placeholders of
`Challenge.lean`.

`scripts/test_proof_policy.py` tests the rejection behaviour of the policy checker.
`scripts/check_proof_policy.py`:

- scans every Lean file of the repository, the vendored libraries included, with comments and
  string literals masked, for `sorry`, `admit`, the `stop` tactic, `axiom`, `opaque`, `unsafe`
  code, `implemented_by`, `extern`, `native_decide`, `#eval`, `#exit`, macros, elaborators,
  initializers and kernel-bypassing options, and checks that every Lean file is a module;
- checks that the two placeholders of `Challenge.lean` are the bodies of the two compared
  theorems and that `Challenge.lean` contains only the expected commands;
- checks that `Challenge.lean`, `Solution.lean` and `PrimeCarleson/Frozen/` state the same two
  theorems and the same five definitions, character for character, and that
  [`comparator.json`](comparator.json) names exactly these theorems and the standard axioms;
- prints `#print axioms` for 10 declarations (the two compared theorems, the development's
  theorems that prove them, and the other main results in `PrimeCarleson/Frozen/`) and requires
  each to depend only on `propext`, `Classical.choice` and `Quot.sound`.

To check the axioms of the compared theorems by hand, compile a file containing

```lean
import Solution

#print axioms PrimeCarleson.Palomar.variation_norm_prime_carleson
#print axioms PrimeCarleson.Palomar.prime_carleson_maximal
```

with `lake env lean <file>`.

Recorded local checks (2026-11-13, on a MacBook Pro (M4, 24 GB) running macOS, with at most four
Lean compiler processes at a time):

- a build from a fresh checkout, after `lake exe cache get`, completed with 10,845 jobs in about
  25 minutes; the only `sorry` warnings were the two of `Challenge.lean`. After later edits to
  comments and docstrings only, an incremental `lake build` of the final files completed with
  the same result;
- `scripts/test_proof_policy.py` passed its 16 tests;
- `scripts/check_proof_policy.py` passed the source, statement and configuration checks, and each
  of the 10 audited declarations reported exactly `propext`, `Classical.choice` and `Quot.sound`.

## Comparator and NanoDa

[`comparator.json`](comparator.json) configures Comparator for the challenge module
`Challenge` and the solution module `Solution`, the two theorems
`PrimeCarleson.Palomar.variation_norm_prime_carleson` and
`PrimeCarleson.Palomar.prime_carleson_maximal`, the permitted axioms `propext`, `Quot.sound` and
`Classical.choice`, and NanoDa (`enable_nanoda: true`). Lake v4.35.0 has a built-in
`comparator` command that reads `comparator.json` by default. On Linux, with `bubblewrap`
installed (it needs unprivileged user namespaces or a setuid install) and `nanoda_bin`, which
ships with the toolchain, on the `PATH`, run:

```sh
lake comparator
```

It builds and exports the project inside the sandbox, and checks that the theorems of
`Solution.lean` prove exactly the statements of `Challenge.lean`, use only the permitted axioms,
and are accepted by the Lean kernel and by NanoDa. It has not yet been run on this repository.

The official Palomar registry performs the final, independent verification of the public
repository and selected immutable commit. Its checks include its own fresh checkout and
protected Challenge handling, so a local run would not be a registry acceptance.
