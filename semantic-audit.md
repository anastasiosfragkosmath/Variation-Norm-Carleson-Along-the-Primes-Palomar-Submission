# Semantic correspondence with the article

This document records the statement-level correspondence between the Lean development and
*A Variation Norm Carleson Theorem Along the Primes* by Anastasios Fragkos, Ben Krause, Nazar
Miheisi and Yu-Chen Sun
([`sources/Variational_Carleson.tex`](sources/Variational_Carleson.tex); line numbers `L…` below
refer to that file). It is a guide to the written Lean theorem types, not a substitute for reading
those types or for the build and axiom evidence in
[the verification report](verification-report.md).

## Headline results

The public review entry point is [`Challenge.lean`](Challenge.lean), which states the two main
theorems together with the definitions they use, importing Mathlib only.
[`Solution.lean`](Solution.lean) proves both statements. Its headline declarations have the
following correspondence.

| Article result | Lean declarations | Scope of the written Lean statements |
| --- | --- | --- |
| Theorem 1.3 (`t:main`), the variation-norm prime Carleson theorem | `PrimeCarleson.Palomar.variation_norm_prime_carleson`, proved by `PrimeCarleson.variation_norm_prime_carleson` | There are functions `c, C : ℝ → ℝ` with `r/(r−1) < c(r) < 2 < C(r)` for every `r > 2`, `c(r) → 1` and `C(r) → ∞` as `r → ∞`, such that for every `r > 2` and every real `p` with `c(r) < p < C(r)` one positive real constant `K` gives `‖𝒱^r_ℙ f‖_{ℓ^p} ≤ K ‖f‖_{ℓ^p}` for every finitely supported `f : ℤ → ℂ`. |
| Theorem 1.4 (`t:carmax`), the maximal bound | `PrimeCarleson.Palomar.prime_carleson_maximal`, proved by `PrimeCarleson.prime_carleson_maximal` | For every real `p > 1`, one positive real constant `K` gives `‖𝒞_ℙ f‖_{ℓ^p} ≤ K ‖f‖_{ℓ^p}` for every finitely supported `f : ℤ → ℂ`. |

Here `𝒱^r_ℙ f(x)` is the `r`-variation over `λ ∈ [0, 1)`, and `𝒞_ℙ f(x)` the supremum over
`λ ∈ [0, 1)` of the modulus, of `S_λ f(x) = Σ_{n ≠ 0} f(x − n) Λ(|n|) e(λn)/n`, where `Λ` is the
von Mangoldt function and `e(t) = exp(2πit)` (`e:Carweight`, `e:CP`, L280–L327).

These two declarations are the Comparator targets of [`comparator.json`](comparator.json). The
development states the same two theorems, with the same definitions, in
[`PrimeCarleson/Frozen/`](PrimeCarleson/Frozen), one declaration per file, and `Solution.lean`
proves each compared statement by the development's theorem.

## Lean-level representation conventions

The following conventions are relevant when reading the written Lean types.

- **Finitely supported inputs.** The paper says that it suffices by density to work with
  finitely supported functions and treats every sequence as finitely supported (footnote, L288).
  The input type is `ℤ →₀ ℂ`, so every sum defining the operators has finitely many nonzero
  terms. The extension of the inequalities to all of `ℓ^p` by density is not formalized.
- **Values in `[0, ∞]`.** The `r`-variation and the maximal function take values in `[0, ∞]`,
  and norms are `eLpNorm … Measure.count` on `ℤ` with the counting measure. The variation of a
  finitely supported input is not assumed to be finite pointwise; the theorem proves that its
  `ℓ^p` norm is at most `K ‖f‖_{ℓ^p}`, and hence finite. Since `ℤ` carries the discrete
  σ-algebra, every function on `ℤ` is measurable and the extended norm is the usual
  `(Σ_x |g(x)|^p)^{1/p}`.
- **Frequencies and the variation.** The paper defines the `r`-variation over an ordered index
  set but does not order `𝕋` (L248–L256). `rVariation r a` is the supremum over `J ∈ ℕ` and
  strictly increasing `t₀ < ⋯ < t_J` in `[0, 1)`, with the order of `ℝ`, of
  `(Σ_{i<J} ‖a(t_i) − a(t_{i+1})‖^r)^{1/r}`. Non-decreasing chains give the same value, since a
  repeated point contributes `0`. Cutting the circle at another point gives the same theorem:
  the sums are 1-periodic in `λ`, and the window `[θ, θ + 1)` amounts to replacing `f` by
  `e(−θ·) f`, which is again finitely supported with the same `ℓ^p` norm.
- **The sum and the weight.** `modulatedSum w f λ x` is the sum over `n : ℤ` of
  `f(x − n) w(|n|) e(λn)/n` with the term at `n = 0` set to `0`. The weight of both theorems is
  Mathlib's `ArithmeticFunction.vonMangoldt` evaluated at `|n|`, the even extension of `Λ` used by
  the paper (`e:wweight`).
- **Quantifiers of Theorem 1.3.** The paper asks for constants `𝐜(r), 𝐂(r)` with limits as
  `r → ∞` (L302–L309), so they are functions of `r`: they are chosen first, and their values at
  `r ≤ 2` are unconstrained. The constant `K` depends only on `r` and `p`. The development
  constructs `𝐜` and `𝐂` explicitly (`PrimeCarleson.Proof.Paper.cR`,
  `PrimeCarleson.Proof.Paper.CR`) and proves the bounds and the limits.
- **The maximal operator.** `carlesonMax w f x` is the supremum over `λ ∈ [0, 1)` of
  `‖modulatedSum w f λ x‖`; by periodicity in `λ` this is the supremum over `𝕋`. Theorem 1.4 is
  stated for every real `p > 1`, which is the paper's range `1 < p < ∞`.

These are representation and statement-organization conventions; they do not assert a
different result from the article.

## Other article-facing declarations

The development also exposes the following reviewable declarations, each in its own file in
[`PrimeCarleson/Frozen/`](PrimeCarleson/Frozen) together with the definitions it uses
(`rVariationOn`, `partialFourierIntegral`, `multiplierOp`, `multiplierOpDis`, `heathBrownModel`,
`blockWeight`, `ramanujanSum`, `gowersNormInterval`, `periodicBlockMax`, `Admissible`,
`sineWeight` and others). The first three are results of other papers that the proofs of the
two main theorems use. The last two are results of the article itself: Proposition 6.1 is a step
of the proof of the main theorems, and Lemma A.1 is a separate counterexample.

| Article-facing item | Lean declaration | Written scope |
| --- | --- | --- |
| Variation norm Carleson theorem on `ℝ`: Oberlin, Seeger, Tao, Thiele, Wright, Theorem 1.2 (arXiv:0910.1555v2), used for Lemma 4.1 and Proposition B.1 | `PrimeCarleson.variation_norm_carleson_real` | For every `r > 2` and every real `p > r/(r−1)`, a real `C` with `‖𝒱^r(ξ ↦ 𝒮f(ξ, x) : ξ ∈ ℝ)‖_{L^p(ℝ)} ≤ C ‖f‖_{L^p(ℝ)}` for every Schwartz function `f`, where `𝒮f(ξ, x) = ∫_{η ≤ ξ} f̂(η) e(ηx) dη`; the variation is over all finite increasing sequences in `ℝ`. The extension to all of `L^p` and the restricted weak-type endpoint `p = r'` are not formalized. |
| Transference from `ℝ` to `ℤ`: Magyar, Stein, Wainger, the proposition of Section 2 (arXiv:math/0409365v1), for `r`-variation norms | `PrimeCarleson.msw_transference_variation` | One absolute constant `C`. For every real `p ≥ 1` and `r ≥ 1`, every finite `T ⊂ ℝ` and bounded measurable multipliers `m_λ` (`λ ∈ T`) supported in `(−1/2, 1/2]`: if the `L^p(ℝ)` norm of `𝒱^r(T_{m_λ}F : λ ∈ T)` is at most `A ‖F‖_{L^p}` for every Schwartz `F`, then the `ℓ^p(ℤ)` norm of the corresponding discrete variation is at most `C A ‖f‖_{ℓ^p}` for every finitely supported `f`. This is the one-dimensional, scalar case; `p = ∞` is not included. |
| `U³` approximation of the von Mangoldt function: Fornal, Fragkos, Krause, Lacey, Mousavi, Sun, Proposition 3.1 (arXiv:2601.10459v3) | `PrimeCarleson.vonMangoldt_sub_heathBrown_U3` | For every real `A ≥ 1`, a real `C` with `‖Λ − Λ_{≤Q_N}‖_{U³[N]} ≤ C (log N)^{−A}` for every integer `N ≥ 2`, where `Q_N = exp((log N)^{1/10})`, `Λ_{≤T}` is the Heath-Brown model summed over the dyadic blocks `(Q/2, Q]` with `Q = 2^j ≤ T`, `[N] = {1, …, N}`, and the `U³[N]` norm is normalized by the norm of `1_{[N]}`. The proposition is printed for `N ≥ 1`; at `N = 1` its right side `(log 1)^{−A}` is infinite. |
| Proposition 6.1 (`p:goal0`) | `PrimeCarleson.periodicBlockMax_bound` | There is `κ₀ > 0` such that for every `0 < κ ≤ κ₀`, every `0 < ε ≤ κ/100` and every real comparability constant `A`, there is a constant `C` with `𝔪_B ≤ C Q^{κ−1−ε}` for every `Q = 2^j` (`j ≥ 0`) and every set `B` of squarefree integers in `(Q/2, Q]` with `Q^κ ≤ A·#B` and `#B ≤ A·Q^κ`; the operator bound is written as an `ℓ²` inequality over the residues modulo `lcm(B)`. The paper states the bound as `𝔪_B ≲ Q^{κ−1−ε}`, with an implied constant, as here. |
| Lemma A.1 (Appendix A.1) | `PrimeCarleson.admissible_sineWeight_carleson_unbounded` | For `0 < α < 1` and every integer `q₀ ≥ 3`, the weight `v(n) = 1 + α sin(2πn/q₀)` is admissible, and for every `p ∈ [1, ∞]` there is no constant `K` with `‖𝒞_v f‖_{ℓ^p} ≤ K ‖f‖_{ℓ^p}` for all finitely supported `f`; `𝒞_v` is `carlesonMax` with weight `v`, a sum over `n ≠ 0`. In the definition of admissibility (L2830–L2845) each `o(1)` exponent is read as "for every `ε > 0` there is a constant `C_ε`". |

## Verification boundary

The axiom audit and the build are described in the [verification report](verification-report.md).
Comparator checks exactly the two declarations of the headline table. The two `sorry`s of
`Challenge.lean` are the challenge's intentional placeholders, not proofs; `lake build` compiles
`Challenge.lean` as well and reports them, and `Solution.lean` does not import it.

Every result of other work that the proofs use is proved in this repository: in
[`PrimeCarleson/Proof/`](PrimeCarleson/Proof), or in two vendored Lean libraries that are
compiled with it.

- From [openai/math](https://github.com/openai/math): the quasi-polynomial inverse theorem for
  the `U³` norm (`vendor/openai-math/OAI/Combinatorics/Progressions`, pruned to the declarations
  used), the absence of Landau–Siegel zeros
  (`OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap`, in
  `vendor/openai-math/OAI/NumberTheory/SiegelZeros`) and one file on logarithmic control of
  Dirichlet `L`-functions. Through the `U³` approximation above, both main theorems use the
  absence of Landau–Siegel zeros; the printed proof of that approximation allows for a possible
  Siegel zero instead. To our knowledge the absence of Landau–Siegel zeros is not an
  established result in the published literature. Here it rests only on the vendored Lean proof
  (201 modules), which the Lean kernel checks as part of the build.
- From the [Carleson project](https://github.com/fpvandoorn/carleson): real interpolation, the
  Hardy–Littlewood maximal theorem and Lorentz spaces (`vendor/carleson`).

Their upstream revisions, licences and every change made in porting are recorded in
[`vendor/provenance/THIRD-PARTY.md`](vendor/provenance/THIRD-PARTY.md).

The development formalizes the two main theorems and the results listed above. It does not
formalize every intermediate statement of the article in its printed form. In particular:

- the extension of the inequalities from finitely supported or Schwartz inputs to all of `ℓ^p`
  or `L^p` by density is not formalized;
- Lemma 2.1 (`l:ET`, Eisner–Tao) is proved for `s ∈ {1, 2, 3}`, which includes the case `s = 3`
  that the paper uses;
- several intermediate estimates are proved in the form the proof needs: in Lemma 4.3 and
  Propositions 4.4, 4.5 and 5.1 the entropy argument is run at a fixed exponent `2 < s < r` with
  power losses, as in the paper (`Q^δ` for every `δ > 0` in Proposition 4.5, and in
  Proposition 5.1 the case `δ = ε/10` that the proof uses); the norm `Ṽ^s` of Lemma 4.3 and
  Proposition 4.4 is handled as the seminorm `V^s` together with the value at a base point;
  constants depend on `r` and `p` without an explicit rate; and Corollary B.2 is proved only for
  the kernels it is applied to;
- some proofs follow routes that differ from the printed ones: Lemma 4.3 (`l:entest`), which the
  paper obtains from Zorin-Kranich's Lemma 2.6, is proved here by a self-contained chaining
  argument, and the `U³` approximation uses the absence of Landau–Siegel zeros as described above.

Line numbers `L…` in the docstrings and comments of the Lean files refer to
[`sources/Variational_Carleson.tex`](sources/Variational_Carleson.tex) when they cite the main
paper; citations of other papers name those papers.

An internal declaration with an explicit hypothesis should be read according to that hypothesis;
it is not evidence that the hypothesis has been proved elsewhere in this repository.

For the exact Lean types and their imports, inspect [`Challenge.lean`](Challenge.lean) and
[`PrimeCarleson/Frozen/`](PrimeCarleson/Frozen). For reproducible build and audit commands, see
the [verification report](verification-report.md).
