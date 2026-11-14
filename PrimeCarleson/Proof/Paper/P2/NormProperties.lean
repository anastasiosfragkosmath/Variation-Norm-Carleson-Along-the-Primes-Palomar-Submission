module

public import PrimeCarleson.Proof.Paper.P2.Foliate
public import PrimeCarleson.Proof.Common.GowersCauchySchwarz

/-!
# Higher Gowers norms are norms; the normalized norms `U^s(I)`

The statement of [F+], L517 ("for `s = 1` this is a semi-norm, while higher orders are norms";
consumers: the triangle inequality in the proof of `[F+]` Proposition 3.1, L1548–L1550, and the
subadditivity at L2138), for every `s ≥ 2` (the paper
uses `s = 3`), and for the normalized norms `U^s(I)` (the `gowersNormInterval` is the case
`I = [N]`).

* for `s ≥ 2` the Gowers norm `‖·‖_{U^s(ℤ)}` on finitely supported functions is subadditive (the
  Gowers–Cauchy–Schwarz route, `Common.gowersNorm_add_le`), absolutely homogeneous
  (`Common.gowersNorm_smul`) and definite (`eq_zero_of_gowersNorm_eq_zero`, from the foliation
  identity `e:foliate`, `Foliate.lean`); these are the inputs of the statements below;
* `gowersNormOn_norm_properties` and `gowersNormInterval_three_norm_properties`: "consequently the
  same for the normalized norm `U^3[N]`" (the former for every `s`, resp. every `s ≥ 2` for
  definiteness):
  `‖f + g‖_{U^s(I)} ≤ ‖f‖_{U^s(I)} + ‖g‖_{U^s(I)}`, `‖c g‖_{U^s(I)} = |c| ‖g‖_{U^s(I)}`, and
  for `I` nonempty and `s ≥ 2`, `‖g‖_{U^s(I)} = 0 ↔ g = 0` on `I`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson

/-- The Gowers norm of the zero function is `0` (`s ≥ 1`). -/
theorem gowersNorm_finsupp_zero (s : ℕ+) : gowersNorm s (0 : ℤ →₀ ℂ) = 0 := by
  have h := Common.gowersNorm_smul s (0 : ℂ) 0
  simpa using h

/-- **The normalized norms `U^s(I)` are seminorms, and norms for `s ≥ 2`** (Source: [F+]
`sub:gowers_norms`, L517, "consequently the same for the normalized norm"): for
every finite set `I ⊆ ℤ` and every `s`, `‖f + g‖_{U^s(I)} ≤ ‖f‖_{U^s(I)} + ‖g‖_{U^s(I)}` and
`‖c g‖_{U^s(I)} = |c| ‖g‖_{U^s(I)}`; for `I` nonempty and `s ≥ 2`, `‖g‖_{U^s(I)} = 0` iff `g`
vanishes on `I`. -/
theorem gowersNormOn_norm_properties (s : ℕ+) (I : Finset ℤ) :
    (∀ f g : ℤ → ℂ, gowersNormOn s I (f + g) ≤ gowersNormOn s I f + gowersNormOn s I g) ∧
      (∀ (c : ℂ) (g : ℤ → ℂ), gowersNormOn s I (c • g) = ‖c‖ * gowersNormOn s I g) ∧
        (2 ≤ s → I.Nonempty → ∀ g : ℤ → ℂ, gowersNormOn s I g = 0 ↔ ∀ n ∈ I, g n = 0) := by
  refine ⟨gowersNormOn_add_le s I, gowersNormOn_smul s I, fun hs hI g => ?_⟩
  have hpos := gowersNorm_restrictFinset_one_pos s hI
  have h1 : gowersNormOn s I g = 0 ↔ gowersNorm s (restrictFinset I g) = 0 := by
    rw [gowersNormOn, div_eq_zero_iff]
    exact ⟨fun h => h.resolve_right hpos.ne', fun h => Or.inl h⟩
  rw [h1]
  constructor
  · intro h n hn
    have h0 := eq_zero_of_gowersNorm_eq_zero s hs h
    have := congrArg (fun F : ℤ →₀ ℂ => F n) h0
    simpa [restrictFinset_apply, hn] using this
  · intro h
    have : restrictFinset I g = 0 := by
      ext n
      rw [restrictFinset_apply]
      by_cases hn : n ∈ I
      · simp [hn, h n hn]
      · simp [hn]
    rw [this]
    exact gowersNorm_finsupp_zero s

/-- **`U^3[N]`, the normalized norm of the paper** (Source: [F+] `sub:gowers_norms`, L517): the
`gowersNormInterval 3 N` is subadditive and
absolutely homogeneous: `‖f + g‖_{U³([N])} ≤ ‖f‖_{U³([N])} + ‖g‖_{U³([N])}`,
`‖c g‖_{U³([N])} = |c| ‖g‖_{U³([N])}`, and it vanishes only for `g = 0` on `[N]`. -/
theorem gowersNormInterval_three_norm_properties (N : ℕ+) :
    (∀ f g : ℤ → ℂ,
        gowersNormInterval 3 N (f + g) ≤ gowersNormInterval 3 N f + gowersNormInterval 3 N g) ∧
      (∀ (c : ℂ) (g : ℤ → ℂ), gowersNormInterval 3 N (c • g) = ‖c‖ * gowersNormInterval 3 N g) ∧
        (∀ g : ℤ → ℂ, gowersNormInterval 3 N g = 0 ↔ ∀ n ∈ Finset.Icc (1 : ℤ) N, g n = 0) := by
  have hI : (Finset.Icc (1 : ℤ) N).Nonempty :=
    ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by exact_mod_cast N.pos⟩⟩
  obtain ⟨h1, h2, h3⟩ := gowersNormOn_norm_properties 3 (Finset.Icc (1 : ℤ) N)
  exact ⟨h1, h2, h3 (by decide) hI⟩

end PrimeCarleson.Proof.Paper
