# Third-party source provenance

All vendored code is under the Apache-2.0 licence. Every vendored file keeps its upstream
notices; a header comment added to each openai/math file names the upstream commit and path and
states that the file was modified.

## openai/math `DirichletL.LogarithmicControl` (`vendor/openai-math/OAI/NumberTheory/DirichletL`, library `OAI`)

One file, `OAI/NumberTheory/DirichletL/LogarithmicControl.lean` (558 lines, Mathlib only), used by the prime number
theorem in arithmetic progressions (`PrimeCarleson/Proof/Fplus31/PNTSW/`) and the zero-free region
(`PrimeCarleson/Proof/Fplus31/ZeroFree/`). It comes from openai/math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, converted to a Lean module (module header and public
visibility), with a 9-line attribution header comment. Hashes and upstream path: `openai-logarithmic-control.json`. Licence:
Apache-2.0, `vendor/openai-math/LICENSE`.

## Carleson project slice (`vendor/carleson`, library `Carleson`)

- **Source.** `https://github.com/fpvandoorn/carleson`, commit `52cba54d4b7b444e937c7abbc67835afa2a0bb16`. Upstream pins Lean `v4.36.0-rc1` and Mathlib `d88814353fcbcc0461c55b2a4585d3f44d903df1`; the port builds with Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- **Licence.** Apache-2.0. The upstream `LICENSE` is copied unchanged to `third-party-licenses/CARLESON-LICENSE` (SHA-256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`). The six files with a copyright header (`MeasureTheory/Integral/Layercake.lean`, `MeasureTheory/Measure/NoAtoms/*.lean`) keep it unchanged; the other files have none upstream (the upstream lakefile disables the header linter), and none was added. Each of the six changed files starts with a one-line comment stating that it was modified here.
- **What was ported and why.** The import closure, inside the Carleson project, of `Carleson.ToMathlib.RealInterpolation.Main`, `Carleson.ToMathlib.HardyLittlewood` and `Carleson.ToMathlib.LorentzType`: 40 modules, 16,130 lines, already in the module system, with upstream paths and module names (`vendor/carleson/Carleson/...`). It includes `Carleson.Defs`, `Carleson.ToMathlib.Rearrangement` and `Carleson.ToMathlib.MeasureTheory.Measure.IsDoubling` (the instance `MeasureTheory.InnerProductSpace.IsDoubling` gives Lebesgue measure on `ℝ` the doubling constant `2 ^ finrank ℝ ℝ`). It provides the Marcinkiewicz theorem `MeasureTheory.exists_hasStrongType_real_interpolation`, the Hardy–Littlewood bounds `hasWeakType_maximalFunction_one`, `hasStrongType_maximalFunction_one` and `measurable_maximalFunction`, and `MeasureTheory.HasRestrictedWeakType.hasLorentzType`, used in the proof of [O+] Theorem 1.2. `Carleson/ToMathlib/RealInterpolation/LorentzInterpolation.lean`, which has live `sorry`, is not in the closure and was not copied. With comments stripped, the 40 files contain no `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by`, `extern` or heartbeat option; the word `sorry` left in some files sits inside upstream comments.
- **Build options.** The `[[lean_lib]] Carleson` block in `lakefile.toml` follows the upstream lakefile: `autoImplicit = false` and `relaxedAutoImplicit = false`, with Lean's default `maxSynthPendingDepth = 1` (upstream does not set it, whereas this project sets 3) and the Mathlib linter set off, as for the openai/math port. `roots` names the three target modules so that `lake build Carleson` is well defined (there is no `Carleson.lean`).
- **Compatibility changes** (17 lines in 6 files; no proof was rewritten, no helper lemma or `Compat.lean` was needed):
  1. Upstream Mathlib proves `+`, `-` and `0` on simple functions through the generic `FunLike.coe_add`, `FunLike.coe_sub` and `FunLike.coe_zero`; in the pinned Mathlib `SimpleFunc` has no `IsAddApply` instance, so those lemmas do not fire. They were replaced by `SimpleFunc.coe_add`, `SimpleFunc.coe_sub` and `SimpleFunc.coe_zero` (same statements for `SimpleFunc`): 14 lines, in `MeasureTheory/Function/SimpleFunc.lean` (9), `MeasureTheory/Integral/Layercake.lean` (2), `MeasureTheory/Integral/Misc.lean` (1) and `LorentzType.lean` (2).
  2. In the pinned Mathlib, `congr with x` on an equality of sets leaves the right-hand side as an application `(A \ B) x` rather than `x ∈ A \ B`. `Rearrangement.lean` line 316 (`congr with x; grind`) and line 834 (lemma `setLIntegral_enorm_eq`) now restate the goal with `change _ ↔ x ∈ (_ : Set α)` (a definitional `change`) before the original tactics: 2 lines.
  3. `HardyLittlewood.lean` line 207: `hasWeakType_maximalFunction_one` is private upstream (a module-system file without a public section); it is now `public theorem`, so that importers can use it. Statement and proof are unchanged.
- **File record.** `carleson-files.json` lists, for each file, the module, upstream path, upstream and vendored SHA-256, line count and whether it changed (6 of 40 changed).
- **Verification.** The three target modules build with no errors and no warnings. `#print axioms` for the five named theorems and the `ℝ` doubling instance reports only `propext`, `Classical.choice` and `Quot.sound`. Each of the 40 modules was replayed in the Lean kernel with `leanchecker`.

## openai/math `Combinatorics.Progressions` (`vendor/openai-math/OAI/Combinatorics/Progressions`, library `OAI`)

Used for the `U³` approximation of the von Mangoldt function ([F+] Proposition 3.1).

- **Source.** `https://github.com/openai/math`, commit `4eaee87548250b2682affda7d05d947c05554bae`.
  Upstream pins Lean `v4.34.1`; the port builds with Lean `v4.35.0` and Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679`. Licence Apache-2.0 (`vendor/openai-math/LICENSE`).
- **What.** The import closure of the quasi-polynomial `U³` inverse theorem
  `OAI.Erdos3.exists_native_inverse_on_cyclic_encoding` (`Estimates/AxisCompression.lean`): 2,100 files and
  469,519 lines before pruning, with the upstream paths and module names. The upstream files carry no copyright
  header; each ported file gets a header naming the upstream commit and path, the module conversion and any
  compatibility edit.
- **Conversion.** `module`, `public import` for every import, `@[expose] public section`, the upstream
  body unchanged. 30 files received compatibility edits (+131/−108 body lines; no proof rewritten):
  changed Mathlib API (`contDiff_apply`/`contDiffAt_apply` codomain families; removal of
  `PMF.uniformOfFintype`, replaced by a 12-line shim `OAI.Erdos3.uniformPMFOfFintype` with the same
  values), instance search (explicit instance terms or `have`s, and in two files a local instance
  priority, where typeclass search timed out; no heartbeat option), module visibility (missing
  `public import`s, `private` modifiers used in exposed definitions, one auto-generated private proof
  term replaced by an explicit one), one renamed lemma, one redundant `rfl`, and two formatting edits so
  that a source check of this repository does not misread a term `constant d` at the start of a line.
- **Pruning.** Every whole command (a declaration with its docstring, attributes and `open … in` /
  `omit … in` prefix) that the final proofs neither use nor need to compile a kept declaration was deleted; the
  modules left without needed content were then dropped and their importers' imports rewritten to the frontier. Kept declarations are byte-identical to the port. Result: 2,100 → 1,043
  files, 469,519 → 217,177 lines, 26,038 → 11,023 named declarations. 127 declarations were kept by hand: 9 rfl
  `simp` lemmas that the first build showed `simp` needs without a trace in the proof term, 117 further rfl `simp`
  lemmas of the same kind kept as a precaution, and one lemma that keeps an `open` resolving. Every deletion is
  listed in `openai-progressions-pruning.json`.
- **Record.** `openai-progressions-files.json`: per kept file the module, upstream path, upstream and vendored
  SHA-256, lines, whether edited, the fix categories and the number of deleted declarations, and every fix.
- **Verification.** No `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, heartbeat option or
  `set_option` in any ported file; `#print axioms` on `exists_native_inverse_on_cyclic_encoding` reports only
  `propext`, `Classical.choice`, `Quot.sound`. Every kept module was replayed in the Lean kernel with
  `leanchecker`.

## openai/math `NumberTheory.SiegelZeros` (`vendor/openai-math/OAI/NumberTheory/SiegelZeros`, library `OAI`)

Used, with the classical zero-free region proved in `PrimeCarleson/Proof/Fplus31/ZeroFree/`, for the prime number
theorem in arithmetic progressions in the proof of [F+] Proposition 3.1.

- **Source.** `https://github.com/openai/math`, commit `4eaee87548250b2682affda7d05d947c05554bae` (the same
  commit as the `Combinatorics.Progressions` port above). Upstream pins Lean `v4.34.1`; the port builds with
  Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Licence Apache-2.0
  (`vendor/openai-math/LICENSE`).
- **What.** The import closure of `OAI.NumberTheory.SiegelZeros.Conclusions.Theorem`, whose theorem
  `OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap` states that there is an absolute `c > 0`
  with `c <= (1 - beta) * log q` for every real zero `beta` in `(0, 1)` of a primitive real non-principal
  Dirichlet L-function of modulus `q >= 3`: 201 files, 37,269 upstream lines (39,094 after conversion), all
  under `OAI/NumberTheory/SiegelZeros`, same paths and module names. The closure imports only Mathlib and
  itself (no Std, Batteries, Aesop or other package) and shares no module with the Progressions port. The
  upstream files carry no copyright header; each ported file gets a header naming the upstream commit and path,
  the module conversion and any compatibility edit.
- **Conversion.** `module`, `public import` for every import, `@[expose] public section`, the upstream body
  unchanged. 6 of the 201 files received compatibility edits (+13/-3 body lines; no proof rewritten):
  (1) in `Structure/FieldAutomorphisms` and `Structure/ConcreteArchimedean`, Mathlib now has
  `QuadraticAlgebra.mk_zero_eq_C` and `QuadraticAlgebra.C_eq_algebraMap` as simp lemmas, which inside `simp`
  rewrite the literal `<2, 0>` in the type of the biquadratic algebra and defeat `re_add`/`re_mul`: one
  line `attribute [-simp] ...` per namespace block (4 lines, 2 files); (2) `Differentials/SelectedCotangent`:
  `IsLocalization.AtPrime.equivQuotMaximalIdeal` is now an `AlgEquiv`, so `.symm.toRingEquiv.trans` replaces
  `.symm.trans` (1 line); (3) `LocalAlgebra/RegularParameterSelectionLemmas`: `simp` now closes a side goal by
  itself, so one trailing `rfl` was dropped (1 line); (4) module visibility: `private` removed from
  `exists_dyadic_bound` (used in the body of an exposed def, `EntireFunctions/ZeroShellBounds`), and two
  `public import` lines added in `LocalAlgebra/GenericRegularity` (`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
  `Mathlib.Algebra.Module.SpanRankOperations`).
- **Record.** `openai-siegelzeros-files.json`: per file the module, upstream path, upstream and vendored
  SHA-256, lines, whether edited and the fix categories, and every fix (7 rows).
- **Verification.** With comments stripped, none of the 201 upstream or ported files contains `sorry`, `admit`,
  `sorryAx`, `native_decide`, `axiom`, `opaque`, `unsafe`, `implemented_by`, `extern`, `partial`, `set_option` (so
  no heartbeat option) or `macro`/`elab`/`syntax`/`initialize`; the only hits are 56 file-local
  `attribute [local instance ...]` lines. The closure builds with 4 upstream deprecation warnings (three renamed
  Mathlib lemmas and one deprecated import) and no errors.
  `#print axioms OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap` reports only `propext`,
  `Classical.choice`, `Quot.sound`. Every module was replayed in the Lean kernel with `leanchecker`.

## openai/math code copied into `PrimeCarleson/Proof/Fplus31/ZeroFree/Positivity.lean`

Used for the classical zero-free region.

- **Source.** `https://github.com/openai/math`, commit `4eaee87548250b2682affda7d05d947c05554bae`, files
  `lean/OAI/NumberTheory/Jacobsthal/Harmonic/CharacterPositivity.lean` (the declarations from `characterPhase`
  to `character_log_derivative_positivity`) and `lean/OAI/NumberTheory/Jacobsthal/Sieve/PrincipalEulerCorrection.lean`
  (from `localEulerFactor` to `principal_neg_real_log_derivative_le`). Licence Apache-2.0
  (`vendor/openai-math/LICENSE`). Both bodies use only Mathlib.
- **Changes.** The imports; the namespace (`OAI.Erdos970.Erdos970Dependency.SiegelWalfisz` became
  `PrimeCarleson.Proof.Fplus31.ZeroFree`); the `open` lines other than `open scoped ComplexOrder` were dropped,
  so `𝓝 s` is written `nhds s` (one place); `noncomputable def` became `def` inside the file's
  `noncomputable section`; docstrings were added and long lines wrapped. No statement or proof step changed.
  The file's module docstring records the same; `real_character_log_derivative_positivity` in that file is new.
