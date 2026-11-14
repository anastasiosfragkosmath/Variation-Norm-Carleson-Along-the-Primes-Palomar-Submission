# Lean verification for *A Variation Norm Carleson Theorem Along the Primes*

A Lean 4 + Mathlib formalization of the two main theorems of Anastasios Fragkos, Ben Krause,
Nazar Miheisi and Yu-Chen Sun, *A Variation Norm Carleson Theorem Along the Primes*
([`sources/Variational_Carleson.tex`](sources/Variational_Carleson.tex)).

## Main results

The following main results have been formally verified in Lean:

- Theorem 1.3: for every $r \gt 2$, the variation-norm prime Carleson operator
  $\mathcal{V}^r_{\mathbb{P}}$ is bounded on $\ell^p(\mathbb{Z})$ for
  $\mathbf{c}(r) \lt p \lt \mathbf{C}(r)$, where $r' \lt \mathbf{c}(r) \lt 2 \lt \mathbf{C}(r)$,
  $\mathbf{c}(r) \to 1$ and $\mathbf{C}(r) \to \infty$ as $r \to \infty$;
- Theorem 1.4: the maximally modulated prime Carleson operator $\mathcal{C}_{\mathbb{P}}$ is
  bounded on $\ell^p(\mathbb{Z})$ for every $1 \lt p \lt \infty$.

Here, for a finitely supported $f : \mathbb{Z} \to \mathbb{C}$, $\mathcal{V}^r_{\mathbb{P}} f(x)$
is the $r$-variation over $\lambda \in [0,1)$, and $\mathcal{C}_{\mathbb{P}} f(x)$ the supremum
over $\lambda \in [0,1)$ of the modulus, of

$$S_\lambda f(x) = \sum_{n \neq 0} f(x-n)\,\Lambda(\lvert n\rvert)\,\frac{e(\lambda n)}{n},
\qquad e(t) = e^{2\pi i t},$$

where $\Lambda$ is the von Mangoldt function.

`lake build` compiles the formalization with the pinned toolchain. The source-policy checks
prohibit placeholders and proof-bypass mechanisms in every Lean file of the repository, the
vendored libraries included, except the two intentional placeholders of `Challenge.lean`. The
explicit axiom audit reports only Lean's standard axioms `propext`, `Classical.choice` and
`Quot.sound` for the audited declarations. Every result of other papers that the proofs use is
proved in this repository or in the vendored Lean libraries; none is assumed. Through the `U³`
approximation of the von Mangoldt function, both main theorems use the absence of Landau–Siegel
zeros, proved in the vendored openai/math library
(`OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap`). To our knowledge this is not
an established result in the published literature; here it rests only on that library's Lean
proof, which the Lean kernel checks as part of the build.

The two main theorems are configured for Comparator ([`comparator.json`](comparator.json)), which
compares the statements in [`Challenge.lean`](Challenge.lean) with the proofs made available
through [`Solution.lean`](Solution.lean). `Challenge.lean` is a statement
specification that imports Mathlib only and has two intentional placeholders. The verification
report records which checks have been run, and on which commit.

This repository reports local Lean verification: the included proofs are checked by Lean's
kernel with the pinned toolchain. The [verification report](verification-report.md) records the
scope and reproducible evidence for that claim.

## Main Lean declarations

The review-facing statements, with the definitions they use, are in
[`Challenge.lean`](Challenge.lean). The two principal exports are:

- `PrimeCarleson.Palomar.variation_norm_prime_carleson` (Theorem 1.3, `t:main`)
- `PrimeCarleson.Palomar.prime_carleson_maximal` (Theorem 1.4, `t:carmax`)

```lean
theorem variation_norm_prime_carleson :
    ∃ c C : ℝ → ℝ,
      (∀ r : ℝ, 2 < r → r / (r - 1) < c r ∧ c r < 2 ∧ 2 < C r) ∧
      Tendsto c atTop (𝓝 1) ∧ Tendsto C atTop atTop ∧
      ∀ r : ℝ, 2 < r → ∀ p : ℝ, c r < p → p < C r →
        ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
          eLpNorm (primeVariation r f) (ENNReal.ofReal p) Measure.count ≤
            ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count
```

```lean
theorem prime_carleson_maximal :
    ∀ p : ℝ, 1 < p → ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ →₀ ℂ,
      eLpNorm (carlesonMax (ArithmeticFunction.vonMangoldt : ℕ → ℝ) f) (ENNReal.ofReal p)
          Measure.count ≤
        ENNReal.ofReal K * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count
```

`Solution.lean` proves them by the development's theorems
`PrimeCarleson.variation_norm_prime_carleson` and `PrimeCarleson.prime_carleson_maximal`, which
have the same statements. These, and every other main statement and definition of the
development, are in [`PrimeCarleson/Frozen/`](PrimeCarleson/Frozen), one declaration per file,
in the exact form the author approved before any proof used them.

The development also proves the variation norm Carleson theorem on the real line of Oberlin,
Seeger, Tao, Thiele and Wright (`PrimeCarleson.variation_norm_carleson_real`), the
Magyar–Stein–Wainger transference principle for variation norms
(`PrimeCarleson.msw_transference_variation`), the `U³` approximation of the von Mangoldt function
of Fornal, Fragkos, Krause, Lacey, Mousavi and Sun (`PrimeCarleson.vonMangoldt_sub_heathBrown_U3`),
Proposition 6.1 of the paper (`PrimeCarleson.periodicBlockMax_bound`) and the counterexample of
its Appendix A.1 (`PrimeCarleson.admissible_sineWeight_carleson_unbounded`). The
[semantic audit](semantic-audit.md) documents the precise correspondence and the Lean-level
formulation details.

## Build and verify

Install the Lean toolchain selected by `lean-toolchain` (via
[elan](https://github.com/leanprover/elan)). Dependencies are pinned in the committed
`lake-manifest.json`; obtain the cache and then build:

```sh
lake exe cache get
lake build
python3 -B scripts/test_proof_policy.py
python3 -B scripts/check_proof_policy.py
```

The cache command downloads Mathlib's prebuilt files and makes the initial build much faster.
`lake build` compiles all 1,796 Lean files of this repository, including the vendored libraries;
an initial build needs about 16 GB of free disk space. Do not run `lake update` merely to
verify this checkout: it is a maintainer operation that changes the dependency lockfile. The
last command scans every Lean file, checks that `Challenge.lean`, `Solution.lean` and
`PrimeCarleson/Frozen/` state the same two theorems and the same definitions, and checks the
transitive axioms of the 10 audited declarations.

To inspect the axiom report of the two compared theorems directly, compile a file containing

```lean
import Solution

#print axioms PrimeCarleson.Palomar.variation_norm_prime_carleson
#print axioms PrimeCarleson.Palomar.prime_carleson_maximal
```

with `lake env lean <file>`. Each declaration depends only on `propext`, `Classical.choice` and
`Quot.sound`.

To run Comparator locally with Lake's built-in `comparator` command, which reads
[`comparator.json`](comparator.json) (Linux, with `bubblewrap` installed and `nanoda_bin`, which
ships with the toolchain, on the `PATH`):

```sh
lake comparator
```

## Navigation

- [Paper-facing theorem statements and definitions](Challenge.lean)
- [Frozen statements and definitions of the development](PrimeCarleson/Frozen)
- [Local verification report](verification-report.md)
- [Semantic comparison with the paper](semantic-audit.md)
- [Vendored libraries and their provenance](vendor/README.md)

## License

The Lean source code and repository documentation are licensed under [Apache-2.0](LICENSE). The
vendored libraries keep their upstream licences, also Apache-2.0:
[`vendor/openai-math/LICENSE`](vendor/openai-math/LICENSE) and
[`vendor/provenance/third-party-licenses/CARLESON-LICENSE`](vendor/provenance/third-party-licenses/CARLESON-LICENSE).
Attribution and the changes made in porting are recorded in
[`vendor/provenance/THIRD-PARTY.md`](vendor/provenance/THIRD-PARTY.md). The manuscript in
[`sources/`](sources) is included for reference; it is not covered by the Apache-2.0 licence,
and its copyright stays with its authors.

## Acknowledgement

The proofs were written by AI agents (Claude Opus and Claude Sonnet, in Claude Code) under the
direction of Anastasios Fragkos, who approved every main statement and definition in its exact
Lean form before any proof used it. Statements were compared with the paper by independent
reviewing agents, and every claimed result is checked by Lean; details are in
[`formalization.yaml`](formalization.yaml).

The organization and verification workflow of this formalization come from the agent skills of
LeanAutoformalizationSkills by Scott Armstrong:

> LeanAutoformalizationSkills by Scott Armstrong,
> <https://github.com/scottnarmstrong/LeanAutoformalizationSkills>, licensed under
> [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

The agents followed these skills throughout, among them `lean-orchestrator`,
`lean-statement-audit`, `build-proof-dependency-graph`, `lean-project-architecture`,
`lean-elaboration` and `lean-public-release`: exact Lean statements approved by the author and
frozen before any proof work, a source-level dependency graph of the paper and of the cited
papers, bounded proof tasks, independent audits of every statement and proof assembly, and the
elaboration and release checks. The copies used were those of revision
[`1837b95`](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/1837b95b3d5a9fd8d311367603902ad7fe261adf)
of the collection, unchanged except for three added files for macOS in `lean-orchestrator` (a
compile gate, a note on machine resources and its test). The skills themselves are not included
in this repository.

The formalization builds on Mathlib, on the [openai/math](https://github.com/openai/math)
library and on the [Carleson project](https://github.com/fpvandoorn/carleson) of Floris van
Doorn and collaborators.
