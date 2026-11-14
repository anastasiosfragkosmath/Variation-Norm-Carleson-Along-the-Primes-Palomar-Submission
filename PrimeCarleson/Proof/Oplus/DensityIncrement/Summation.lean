module

public import PrimeCarleson.Proof.Oplus.DensityIncrement.Disjoint
public import PrimeCarleson.Proof.Oplus.DensityIncrement.Covering

/-!
# The bound `∑_j |I_{T_j}| ≲ den^{-r'} |E|` ([O+] L1931-L1967)

Source: [O+] `thirddtreeintervalbound`, L1932–L1934; [O+] `densityincrementprop`, L1955–L1966
(L1931-L1967): "To prove
(dtreeintervalbound), it will suffice to verify (thirddtreeintervalbound)
`∑_j |I_{T_j}| ≲ den^{-r'} |E|`. [...] For each `ℓ` we let `𝒯^{(ℓ)} = {T_j : ℓ_j = ℓ}` [...]
Summing over `ℓ`, we obtain (thirddtreeintervalbound)."

`thirddtreeintervalbound` combines the pieces: the truncated density
(`exists_trunc_density`, one integer `ℓ_j ≥ 1` for each selected tree, chosen from
(treehaslargedensity) of `T_j`), the disjointness of the tiles of the selected trees
(`IsDensitySelection.tiles_disjoint`), the bound for each fibre `{j : ℓ_j = ℓ}`
(`covering_fiber_bound`: `8^ℓ den^{r'} ∑ ≤ 2^{ℓ+3} 2^{8+r'} |E|`), and the sum of the geometric
series over `ℓ` (`sum_inv_two_pow_le_two`): `den^{r'} ∑_{j < n} |I_{T_j}| ≤ 16 · 2^{8+r'} |E|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeCarleson.Proof.Oplus

/-- `∑_{ℓ ∈ t} 2^{-ℓ} ≤ 2` for every finite set `t` of exponents. -/
theorem sum_inv_two_pow_le_two (t : Finset ℕ) : ∑ ℓ ∈ t, (ENNReal.ofReal ((2 : ℝ) ^ ℓ))⁻¹ ≤ 2 := by
  have h : ∀ ℓ : ℕ, (ENNReal.ofReal ((2 : ℝ) ^ ℓ))⁻¹ = (2⁻¹ : ℝ≥0∞) ^ ℓ := fun ℓ => by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  simp only [h]
  calc ∑ ℓ ∈ t, (2⁻¹ : ℝ≥0∞) ^ ℓ ≤ ∑' ℓ : ℕ, (2⁻¹ : ℝ≥0∞) ^ ℓ := ENNReal.sum_le_tsum t
    _ = 2 := by rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

section Summation

variable {ρ : Idx} [Fact ρ.IsOneOrTwo] {C₁ C₂ C₃ : ℝ} {M : ℤ} {r : ℝ} {L : Linearization r}
  {E : Set ℝ} {den : ℝ}

namespace IsDensitySelection

variable {𝔓 : Finset (Multitile ρ)} {n : ℕ} {S T Tp Tm : ℕ → MultitileTree ρ}
  (sel : IsDensitySelection C₁ C₂ M L E den 𝔓 n S T Tp Tm)
include sel

/-- **`trunctreehaslargedensity`** for the selected trees ([O+] L1937-L1940): for each `j < n`
there is an integer `ℓ_j ≥ 1` with `|I_{T_j}| ≤ 2^{8 + r'} 2^{-3ℓ_j} den^{-r'}
∫_{E ∩ 2^{ℓ_j} I_{T_j}} ∑_{k : ξ_{k-1}(x) ∈ ω_{T_j}} |a_k(x)|^{r'} dx` (written without negative
powers), from (treehaslargedensity) of `T_j`. -/
theorem exists_trunc_density_of_lt (hr : 1 < r) (hden : 0 < den) {j : ℕ} (hj : j < n) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧
      ENNReal.ofReal (8 ^ ℓ * den ^ Real.conjExponent r) * ENNReal.ofReal (T j).I.length ≤
        ENNReal.ofReal (2 ^ (8 + Real.conjExponent r)) *
          ∫⁻ x in E ∩ (T j).I.dilate ((2 : ℝ) ^ ℓ), L.tailSum ((T j).ωT C₂) x :=
  _root_.PrimeCarleson.Proof.Oplus.exists_trunc_density hr hden L E C₂ (T j)
    (sel.T_dense hj).large

/-- **`thirddtreeintervalbound`** ([O+] L1932-L1967): `∑_j |I_{T_j}| ≲ den^{-r'} |E|` for the
selected trees, in the form `den^{r'} ∑_{j < n} |I_{T_j}| ≤ 16 · 2^{8 + r'} |E|`. -/
theorem thirddtreeintervalbound (hr : 1 < r) (hden : 0 < den)
    (hC : AdmissibleConstants C₁ C₂ C₃) (hρ : ρ.IsStd) :
    ENNReal.ofReal (den ^ Real.conjExponent r) * ∑ j ∈ Finset.range n,
        ENNReal.ofReal (T j).I.length ≤
      ENNReal.ofReal (16 * 2 ^ (8 + Real.conjExponent r)) * volume E := by
  classical
  have hC₂ : 1 < C₂ := lt_of_le_of_lt hC.one_le hC.lt₁
  set p := Real.conjExponent r with hp
  have hp0 : 0 < p := by
    rw [hp]; unfold Real.conjExponent
    exact div_pos (by linarith) (by linarith)
  -- the integers `ℓ_j`
  have hex : ∀ j : ℕ, ∃ ℓ : ℕ, j < n → 1 ≤ ℓ ∧
      ENNReal.ofReal (8 ^ ℓ * den ^ p) * ENNReal.ofReal (T j).I.length ≤
        ENNReal.ofReal (2 ^ (8 + p)) *
          ∫⁻ x in E ∩ (T j).I.dilate ((2 : ℝ) ^ ℓ), L.tailSum ((T j).ωT C₂) x := fun j => by
    by_cases hj : j < n
    · obtain ⟨ℓ, hℓ, h⟩ := sel.exists_trunc_density_of_lt hr hden hj
      exact ⟨ℓ, fun _ => ⟨hℓ, h⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose ℓ hℓ using hex
  set Dd : ℝ≥0∞ := ENNReal.ofReal (den ^ p) with hDd
  set K' : ℝ≥0∞ := ENNReal.ofReal (2 ^ (8 + p)) * volume E with hK'
  set X : ℕ → ℝ≥0∞ := fun ℓ0 => ∑ j ∈ (Finset.range n).filter (fun j => ℓ j = ℓ0),
    ENNReal.ofReal (T j).I.length with hX
  have hfib : ∀ ℓ0 ∈ (Finset.range n).image ℓ, Dd * X ℓ0 ≤ (ENNReal.ofReal ((2 : ℝ) ^ ℓ0))⁻¹ *
      (8 * K') := by
    intro ℓ0 _
    set u : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ ℓ0) with hu
    have hu0 : u ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hut : u ≠ ∞ := ENNReal.ofReal_ne_top
    have hfb := covering_fiber_bound (C₂ := C₂) hr hC₂ L E ℓ0 T
      ((Finset.range n).filter (fun j => ℓ j = ℓ0))
      (fun j hj j' hj' hne => sel.tiles_disjoint hC hρ (Finset.mem_range.1
        (Finset.mem_filter.1 hj).1) (Finset.mem_range.1 (Finset.mem_filter.1 hj').1) hne)
      (fun j hj => by
        obtain ⟨hjr, hjℓ⟩ := Finset.mem_filter.1 hj
        have := (hℓ j (Finset.mem_range.1 hjr)).2
        rwa [hjℓ] at this)
    have e1 : u * (u * Dd) ≤ ENNReal.ofReal (8 ^ ℓ0 * den ^ p) := by
      rw [hu, hDd, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (1 : ℝ) ≤ 2 ^ ℓ0 := one_le_pow₀ (by norm_num)
      have h2 : (2 : ℝ) ^ ℓ0 * 2 ^ ℓ0 ≤ 8 ^ ℓ0 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have h3 : (0 : ℝ) ≤ den ^ p := by positivity
      nlinarith
    have e2 : ENNReal.ofReal (2 ^ (ℓ0 + 3)) = 8 * u := by
      rw [hu, pow_add, ENNReal.ofReal_mul (by positivity), mul_comm]
      congr 1
      norm_num
    rw [e2] at hfb
    have h4 : u * (u * (Dd * X ℓ0)) ≤ u * (8 * K') := by
      calc u * (u * (Dd * X ℓ0)) = (u * (u * Dd)) * X ℓ0 := by ring
        _ ≤ ENNReal.ofReal (8 ^ ℓ0 * den ^ p) * X ℓ0 := mul_le_mul' e1 le_rfl
        _ ≤ 8 * u * K' := hfb
        _ = u * (8 * K') := by ring
    have h5 := (ENNReal.mul_le_mul_iff_right hu0 hut).1 h4
    exact (ENNReal.mul_le_iff_le_inv hu0 hut).1 h5
  have hmaps : ∀ j ∈ Finset.range n, ℓ j ∈ (Finset.range n).image ℓ := fun j hj =>
    Finset.mem_image_of_mem ℓ hj
  calc Dd * ∑ j ∈ Finset.range n, ENNReal.ofReal (T j).I.length
      = Dd * ∑ ℓ0 ∈ (Finset.range n).image ℓ, X ℓ0 := by
        rw [hX]
        congr 1
        exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ ℓ0 ∈ (Finset.range n).image ℓ, Dd * X ℓ0 := Finset.mul_sum _ _ _
    _ ≤ ∑ ℓ0 ∈ (Finset.range n).image ℓ, (ENNReal.ofReal ((2 : ℝ) ^ ℓ0))⁻¹ * (8 * K') :=
        Finset.sum_le_sum hfib
    _ = (∑ ℓ0 ∈ (Finset.range n).image ℓ, (ENNReal.ofReal ((2 : ℝ) ^ ℓ0))⁻¹) * (8 * K') :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * (8 * K') := mul_le_mul' (sum_inv_two_pow_le_two _) le_rfl
    _ = ENNReal.ofReal (16 * 2 ^ (8 + p)) * volume E := by
        rw [hK', ENNReal.ofReal_mul (by norm_num), ← mul_assoc, ← mul_assoc]
        congr 1
        rw [show (ENNReal.ofReal 16) = 2 * 8 by
          rw [show (16 : ℝ) = 2 * 8 by norm_num, ENNReal.ofReal_mul (by norm_num)]
          simp]

end IsDensitySelection

end Summation

end PrimeCarleson.Proof.Oplus
