module

public import PrimeCarleson.Proof.Common.HausdorffYoung
public import PrimeCarleson.Proof.Goal0.Basic

/-!
# The endpoint term of `e:embed`: discrete Hausdorff-Young after separating residue classes

Source: main paper `e:embed`, L1129–L1137 (proof of `e:embed`); the discrete Hausdorff–Young
inequality on cyclic groups (`Common.hausdorffYoung_cyclic`, a folklore fact), with the constant
`C_r`.

For `M ≥ 1` and `P(λ) = ∑_{|n| ≤ M} c_n e(λ n)`:
`(∑_{j=0}^{M-1} |P(j/M)|^r)^{1/r} ≤ C_r' M^{1/r} (∑_{|n| ≤ M} |c_n|^{r'})^{1/r'}` with
`C_r' = 3 C_r` (`endpoint_hausdorffYoung`). The `2M + 1` frequencies `|n| ≤ M` lie in the three
blocks
`[-M, 0)`, `[0, M)`, `[M, 2M)` of `M` consecutive integers; in each block the residues modulo `M`
are distinct (`endpointBlock`, `sum_Icc_eq_cyclicSum`), so that `e(jn/M)` only depends on the
position of `n` in its block, and the cyclic inequality applies to each block
(`sum_endpointBlock_le` for the `ℓ^{r'}` norms of the blocks).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Paper

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Goal0

/-- The block decomposition of the frequencies `[-M, M] ⊆ [-M, 2M)` into three consecutive blocks
of length `M`: the frequency `-M + (l + M s)` (`l < M`, `s < 3`), cut off to `[-M, M]`. -/
def endpointBlock (M : ℕ) (c : ℤ → ℂ) (s l : ℕ) : ℂ :=
  if (-(M : ℤ) + ((l + M * s : ℕ) : ℤ)) ∈ Finset.Icc (-(M : ℤ)) M then
    c (-(M : ℤ) + ((l + M * s : ℕ) : ℤ)) else 0

/-- For `j < M`, the sum `∑_{|n| ≤ M} c_n e(jn/M)` is the sum over the three blocks
(`s < 3`) of the cyclic Fourier sums `∑_{l < M} B_{s,l} e(jl/M)` of the blocks
(`e(j(l + Ms - M)/M) = e(jl/M)` since `j` is an integer). -/
theorem sum_Icc_eq_cyclicSum {M : ℕ} (hM : 0 < M) (c : ℤ → ℂ) {j : ℕ} (hj : j < M) :
    ∑ n ∈ Finset.Icc (-(M : ℤ)) M, c n * e (((j : ℝ) / M) * n) =
      ∑ s ∈ Finset.range 3, cyclicSum M (endpointBlock M c s) j := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsub : Finset.Icc (-(M : ℤ)) M ⊆ Finset.Ico (-(M : ℤ)) (2 * M) := by
    intro n hn
    simp only [Finset.mem_Icc, Finset.mem_Ico] at hn ⊢
    omega
  have h1 : ∑ n ∈ Finset.Icc (-(M : ℤ)) M, c n * e (((j : ℝ) / M) * n) =
      ∑ n ∈ Finset.Ico (-(M : ℤ)) (2 * M),
        if n ∈ Finset.Icc (-(M : ℤ)) M then c n * e (((j : ℝ) / M) * n) else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
  rw [h1, Int.Ico_eq_finset_map, Finset.sum_map]
  have h3 : (2 * (M : ℤ) - -(M : ℤ)).toNat = M * 3 := by omega
  rw [h3, sum_range_mul_eq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [cyclicSum, hj, ↓reduceIte]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply,
    endpointBlock]
  by_cases hn : (-(M : ℤ) + ((a + M * s : ℕ) : ℤ)) ∈ Finset.Icc (-(M : ℤ)) M
  · simp only [hn, ↓reduceIte]
    congr 1
    have : ((j : ℝ) / M) * ((-(M : ℤ) + ((a + M * s : ℕ) : ℤ) : ℤ) : ℝ) =
        (j : ℝ) * a / M + (((j : ℤ) * s - j : ℤ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [this, e_add_intCast]
  · simp only [hn, ↓reduceIte, zero_mul]


/-- Each block of frequencies has `ℓ^{r'}` norm at most that of `c` on `[-M, M]`. -/
theorem sum_endpointBlock_le {M : ℕ} (c : ℤ → ℂ) (s : ℕ) {r' : ℝ} (hr' : 0 < r') :
    ∑ l ∈ Finset.range M, ‖endpointBlock M c s l‖ ^ r' ≤
      ∑ n ∈ Finset.Icc (-(M : ℤ)) M, ‖c n‖ ^ r' := by
  classical
  set φ : ℕ → ℤ := fun l => -(M : ℤ) + ((l + M * s : ℕ) : ℤ) with hφ
  have hinj : Function.Injective φ := by
    intro l l' h
    simp only [hφ] at h
    have : ((l + M * s : ℕ) : ℤ) = ((l' + M * s : ℕ) : ℤ) := by linarith
    have := Nat.cast_injective this
    omega
  have hg : ∀ l : ℕ, ‖endpointBlock M c s l‖ ^ r' =
      (fun n : ℤ => if n ∈ Finset.Icc (-(M : ℤ)) M then ‖c n‖ ^ r' else 0) (φ l) := by
    intro l
    unfold endpointBlock
    by_cases hn : φ l ∈ Finset.Icc (-(M : ℤ)) M
    · have hn' : -(M : ℤ) + ((l + M * s : ℕ) : ℤ) ∈ Finset.Icc (-(M : ℤ)) M := hn
      simp only [hφ, hn', ↓reduceIte]
    · have hn' : -(M : ℤ) + ((l + M * s : ℕ) : ℤ) ∉ Finset.Icc (-(M : ℤ)) M := hn
      simp only [hφ, hn', ↓reduceIte, norm_zero, Real.zero_rpow hr'.ne']
  simp_rw [hg]
  rw [← Finset.sum_image
    (f := fun n : ℤ => if n ∈ Finset.Icc (-(M : ℤ)) M then ‖c n‖ ^ r' else 0) (g := φ)
    (fun l _ l' _ h => hinj h), Finset.sum_ite_mem]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun _ _ _ => by positivity)

/-- **The endpoint term of `e:embed`** (L1129–L1137): for conjugate exponents `2 ≤ r`, `r'`, there
is a constant `C` depending only on `r` (`C = 3 C_r`, `C_r` the constant of the discrete
Hausdorff-Young inequality on `ℤ/M`, `Common.hausdorffYoung_cyclic`) such that for every `M ≥ 1` and
`c : ℤ → ℂ`, with `P(λ) = ∑_{|n| ≤ M} c_n e(λ n)`,
`(∑_{j=0}^{M-1} |P(j/M)|^r)^{1/r} ≤ C M^{1/r} (∑_{|n| ≤ M} |c_n|^{r'})^{1/r'}`.
The frequencies `|n| ≤ M` are separated into the three families `-M + l + Ms` (`l < M`,
`s < 3`) with distinct residues modulo `M` ("finitely many residue classes", L1129-L1130);
Minkowski's inequality in `ℓ^r_j` and the cyclic Hausdorff-Young inequality for each family
give the bound. Source: main paper `e:embed`, L1129–L1137. -/
theorem endpoint_hausdorffYoung {r r' : ℝ} (hr : 2 ≤ r) (hrr' : r.HolderConjugate r') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ), 0 < M → ∀ c : ℤ → ℂ,
      (∑ j ∈ Finset.range M,
        ‖∑ n ∈ Finset.Icc (-(M : ℤ)) M, c n * e (((j : ℝ) / M) * n)‖ ^ r) ^ (1 / r) ≤
        C * (M : ℝ) ^ (1 / r) * (∑ n ∈ Finset.Icc (-(M : ℤ)) M, ‖c n‖ ^ r') ^ (1 / r') := by
  obtain ⟨C₀, hC₀, hHY⟩ := hausdorffYoung_cyclic hr hrr'
  have hr0 : 0 < r := by linarith
  have hr'0 : 0 < r' := hrr'.symm.pos
  refine ⟨3 * C₀, by positivity, fun M hM c => ?_⟩
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set S : Finset ℤ := Finset.Icc (-(M : ℤ)) M with hS
  set K : ℝ := C₀ * (M : ℝ) ^ (1 / r) * (∑ n ∈ S, ‖c n‖ ^ r') ^ (1 / r') with hK
  have hK0 : 0 ≤ K := by positivity
  set Fs : ℕ → ℕ → ℂ := fun s => cyclicSum M (endpointBlock M c s) with hFs
  set Q : ℕ → ℂ := fun j => ∑ s ∈ Finset.range 3, Fs s j with hQ
  have hQ0 : ∀ j ∉ Finset.range M, Q j = 0 := by
    intro j hj
    simp [hQ, hFs, cyclicSum, Finset.mem_range.not.1 hj]
  have hQE : eLpNorm Q (ENNReal.ofReal r) Measure.count =
      ENNReal.ofReal ((∑ j ∈ Finset.range M, ‖Q j‖ ^ r) ^ (1 / r)) :=
    eLpNorm_count_eq_ofReal_sum hQ0 hr0
  have hQj : ∀ j ∈ Finset.range M, Q j = ∑ n ∈ S, c n * e (((j : ℝ) / M) * n) :=
    fun j hj => (sum_Icc_eq_cyclicSum hM c (Finset.mem_range.1 hj)).symm
  have hmink : eLpNorm Q (ENNReal.ofReal r) Measure.count ≤
      ∑ s ∈ Finset.range 3, eLpNorm (Fs s) (ENNReal.ofReal r) Measure.count := by
    have := eLpNorm_sum_le (μ := Measure.count) (s := Finset.range 3) (f := Fs)
      (p := ENNReal.ofReal r) (ENNReal.one_le_ofReal.2 (by linarith))
    simpa [Finset.sum_fn, hQ] using this
  have hFsK : ∀ s, eLpNorm (Fs s) (ENNReal.ofReal r) Measure.count ≤ ENNReal.ofReal K := by
    intro s
    have hT : ∀ j ∉ Finset.range M, Fs s j = 0 := fun j hj => by
      simp [hFs, cyclicSum, Finset.mem_range.not.1 hj]
    rw [eLpNorm_count_eq_ofReal_sum hT hr0]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hHY M (endpointBlock M c s)
    have hcongr : ∑ j ∈ Finset.range M, ‖Fs s j‖ ^ r =
        ∑ j ∈ Finset.range M,
          ‖∑ l ∈ Finset.range M, endpointBlock M c s l * e ((j : ℝ) * l / M)‖ ^ r := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [hFs, cyclicSum, Finset.mem_range.1 hj, ↓reduceIte]
    rw [hcongr]
    refine h.trans ?_
    rw [hK]
    gcongr
    exact sum_endpointBlock_le c s hr'0
  have hmain : ENNReal.ofReal ((∑ j ∈ Finset.range M,
        ‖∑ n ∈ S, c n * e (((j : ℝ) / M) * n)‖ ^ r) ^ (1 / r)) ≤ ENNReal.ofReal (3 * K) := by
    have h1 : ∑ j ∈ Finset.range M, ‖∑ n ∈ S, c n * e (((j : ℝ) / M) * n)‖ ^ r =
        ∑ j ∈ Finset.range M, ‖Q j‖ ^ r :=
      Finset.sum_congr rfl fun j hj => by rw [hQj j hj]
    rw [h1, ← hQE]
    calc eLpNorm Q (ENNReal.ofReal r) Measure.count
        ≤ ∑ s ∈ Finset.range 3, eLpNorm (Fs s) (ENNReal.ofReal r) Measure.count := hmink
      _ ≤ ∑ s ∈ Finset.range 3, ENNReal.ofReal K := Finset.sum_le_sum fun s _ => hFsK s
      _ = ENNReal.ofReal (3 * K) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat, Nat.cast_ofNat]
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain
  calc _ ≤ 3 * K := hmain
    _ = 3 * C₀ * (M : ℝ) ^ (1 / r) * (∑ n ∈ S, ‖c n‖ ^ r') ^ (1 / r') := by rw [hK]; ring

end PrimeCarleson.Proof.Paper
