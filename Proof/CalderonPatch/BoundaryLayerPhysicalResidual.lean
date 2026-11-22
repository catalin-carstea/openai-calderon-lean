/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
module

public import Proof.CalderonPatch.BoundaryLayerCutoffEstimate

import Mathlib.Tactic

public section

noncomputable section

open Set
namespace CalderonPatch.BoundaryLayer

/-- The three uniform Taylor remainder estimates of a signed scalar operator. -/
@[expose] def LayerCoefficientTaylorError {n : ℕ}
    {ξ : Fin n → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (A : EuclideanSpace ℝ (Fin n) × ℝ → Matrix (Fin n) (Fin n) ℝ)
    (τ : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (c : EuclideanSpace ℝ (Fin n) × ℝ → Fin n → ℝ)
    (B : BoundaryLayerCoefficients ξ U) (K : Set (EuclideanSpace ℝ (Fin n)))
    (r : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ z, z.1 ∈ K → z.2 ∈ Icc 0 r →
    (∀ i j, ‖(A z i j : ℂ) - B.matrixTaylor N z.1 z.2 i j‖ ≤ C * z.2 ^ (N + 1)) ∧
    ‖(τ z : ℂ) - B.normalTaylor N z.1 z.2‖ ≤ C * z.2 ^ (N + 1) ∧
    (∀ i, ‖(c z i : ℂ) - B.tangentTaylor N z.1 z.2 i‖ ≤ C * z.2 ^ (N + 1))

end CalderonPatch.BoundaryLayer

open Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "H" => Y × ℝ

theorem coefficient_jet_product_bound {C J t h s : ℝ} {a v : ℂ} (p : ℕ)
    (hC : 0 ≤ C) (hh : 0 ≤ h) (ht : t = h * s)
    (ha : ‖a‖ ≤ C * t ^ p) (hv : s ^ p * ‖v‖ ≤ J) :
    ‖a‖ * ‖v‖ ≤ C * J * h ^ p := by
  calc
    _ ≤ (C * t ^ p) * ‖v‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ = C * h ^ p * (s ^ p * ‖v‖) := by rw [ht, mul_pow]; ring
    _ ≤ C * h ^ p * J := mul_le_mul_of_nonneg_left hv (mul_nonneg hC (pow_nonneg hh _))
    _ = _ := by ring

namespace BoundaryLayerCoefficients

theorem exists_taylor_operator_error_bound 
    (A₀ : H → Matrix (Fin n) (Fin n) ℝ) (τ₀ : H → ℝ)
    (c₀ : H → Fin n → ℝ) {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (M : ℕ) {r CT : ℝ} (hCT : 0 ≤ CT) (he : LayerCoefficientTaylorError A₀ τ₀ c₀ B K r M CT) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ M → ∀ z : H,
      z.1 ∈ K → z.2 ∈ Icc (0 : ℝ) r →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖conjugatedSplitOperator (Matrix.of (fun i l => (A₀ z i l : ℂ))) (τ₀ z)
          (fun i => (c₀ z i : ℂ)) ξ h (B.profile a j)
          z.1 (z.2 / h) -
        conjugatedSplitOperator (B.matrixTaylor M z.1 z.2)
          (B.normalTaylor M z.1 z.2)
          (B.tangentTaylor M z.1 z.2) ξ h (B.profile a j)
          z.1 (z.2 / h)‖ ≤ C * h ^ (M + 1) := by
  obtain ⟨c, J, hc, hJ, hb⟩ := B.exists_uniform_actual_layerJet_moment_exp_bound hU hK hKU a ha ha0 M (M + 1)
  refine ⟨CT * J * scalarFrequencyWeight ξ, mul_nonneg (mul_nonneg hCT hJ) (scalarFrequencyWeight_nonneg ξ), ?_⟩
  intro j hj z hz ht h hh hh1
  let y := z.1
  let t := z.2
  let s := t / h
  have hs : 0 ≤ s := div_nonneg ht.1 hh.le
  have hts : t = h * s := by dsimp [s]; field_simp
  obtain ⟨hv, hn, hd, hdd⟩ := hb j hj y hz s hs
  have hexp : J * Real.exp (-c * s) ≤ J := by
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith)) hJ).trans_eq (mul_one _)
  have hv' := hv.trans hexp
  have hn' := hn.trans hexp
  have hd' := fun i => (hd i).trans hexp
  have hdd' := fun i l => (hdd i l).trans hexp
  obtain ⟨hA, hτ, hc'⟩ := he z hz ht
  rw [conjugatedSplitOperator_sub]
  have hp {u v : ℂ} (hu : ‖u‖ ≤ CT * t ^ (M + 1)) (hv : s ^ (M + 1) * ‖v‖ ≤ J) :
      ‖u‖ * ‖v‖ ≤ CT * J * h ^ (M + 1) :=
    coefficient_jet_product_bound (M + 1) hCT hh.le hts hu hv
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i l => (A₀ z i l : ℂ))
  have hbound := scalarCoefficientDifference_product_bound
    (A - B.matrixTaylor M y t)
    ((τ₀ z : ℂ) - B.normalTaylor M y t)
    ((fun i => (c₀ z i : ℂ)) - B.tangentTaylor M y t)
    ξ hh.le hh1 (by positivity : 0 ≤ CT * J * h ^ (M + 1)) (B.profile a j) y s
    (fun i l => hp (hA i l) hv') (hp hτ hn')
    (fun i l => hp (hA i l) (hd' l)) (fun i => hp (hc' i) hv')
    (fun i l => hp (hA i l) (hdd' i l)) (fun i => hp (hc' i) (hd' i))
  exact hbound.trans_eq (by ring)

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "H" => Y × ℝ

theorem exists_uncut_scalar_residual_bound 
    (A₀ : H → Matrix (Fin n) (Fin n) ℝ) (τ₀ : H → ℝ)
    (c₀ : H → Fin n → ℝ) {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (M : ℕ) {r CT : ℝ} (hCT : 0 ≤ CT) (he : LayerCoefficientTaylorError A₀ τ₀ c₀ B K r M CT) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : H,
      z.1 ∈ K → z.2 ∈ Icc (0 : ℝ) r →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) *
        conjugatedSplitOperator (Matrix.of (fun i l => (A₀ z i l : ℂ))) (τ₀ z)
          (fun i => (c₀ z i : ℂ)) ξ h (B.profile a j)
          z.1 (z.2 / h)‖ ≤ C * h ^ (M + 1) := by
  obtain ⟨C₀, hC₀, hb₀⟩ := B.finiteResidualProfile_bound hU hK hKU a ha ha0 M
  obtain ⟨C₁, hC₁, hb₁⟩ := B.exists_taylor_operator_error_bound A₀ τ₀ c₀ hU hK hKU a ha ha0 M hCT he
  refine ⟨C₀ + (M + 1 : ℕ) * C₁, by positivity, ?_⟩
  intro z hz ht h hh hh1
  let y := z.1
  let t := z.2
  let s := t / h
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i l => (A₀ z i l : ℂ))
  let T (j : ℕ) := conjugatedSplitOperator (B.matrixTaylor M y t) (B.normalTaylor M y t)
    (B.tangentTaylor M y t) ξ h (B.profile a j) y s
  let V (j : ℕ) := conjugatedSplitOperator A (τ₀ z)
    (fun i => (c₀ z i : ℂ)) ξ h (B.profile a j) y s
  have hts : h * s = t := by dsimp [s]; field_simp
  have heq : (∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * V j) =
      B.finiteResidualProfile a M h (y, s) + ∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * (V j - T j) := by
    rw [B.finiteResidualProfile_eq_TaylorOperator_sum hU hK.isClosed a ha ha0 M (hKU hz) h s, hts, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    change (h ^ j : ℂ) * V j = (h ^ j : ℂ) * T j + (h ^ j : ℂ) * (V j - T j)
    ring
  have heach (j : ℕ) (hj : j ∈ Finset.range (M + 1)) :
      ‖(h ^ j : ℂ) * (V j - T j)‖ ≤ C₁ * h ^ (M + 1) := by
    have hp : ‖(h ^ j : ℂ)‖ ≤ 1 := by
      simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] using
        pow_le_one₀ (n := j) hh.le hh1
    have hjM : j ≤ M := by have hj' := Finset.mem_range.mp hj; omega
    calc
      _ ≤ 1 * (C₁ * h ^ (M + 1)) := by
        rw [norm_mul]
        exact mul_le_mul hp (hb₁ j hjM z hz ht h hh hh1) (norm_nonneg _) (by positivity)
      _ = _ := one_mul _
  change ‖∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * V j‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖B.finiteResidualProfile a M h (y, s)‖ + ‖∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * (V j - T j)‖ := norm_add_le _ _
    _ ≤ C₀ * h ^ (M + 1) + ∑ j ∈ Finset.range (M + 1), C₁ * h ^ (M + 1) := by
      apply add_le_add (hb₀ y hz h hh hh1 s (div_nonneg ht.1 hh.le))
      exact (norm_sum_le _ _).trans (sum_le_sum heach)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "H" => Y × ℝ

theorem exists_cutoff_scalar_residual_bound 
    (A₀ : H → Matrix (Fin n) (Fin n) ℝ) (τ₀ : H → ℝ)
    (c₀ : H → Fin n → ℝ) {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ)) (M : ℕ) {CT T : ℝ} (hCT : 0 ≤ CT) (hT : 0 ≤ T)
    (he : LayerCoefficientTaylorError A₀ τ₀ c₀ B K η.rOut M CT)
    (hS : ∀ z : H, z.1 ∈ K →
      z.2 ∈ Icc (0 : ℝ) η.rOut → ∀ i l, A₀ z i l = A₀ z l i)
    (hτ : ∀ z : H, z.1 ∈ K →
      z.2 ∈ Icc (0 : ℝ) η.rOut → |τ₀ z| ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : H,
      z.1 ∈ K → z.2 ∈ Icc (0 : ℝ) η.rOut →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
      ‖∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * ((h : ℂ) ^ 2 *
        complexSplitOperator (Matrix.of (fun i l => (A₀ z i l : ℂ))) (τ₀ z)
          (fun i => (c₀ z i : ℂ))
          (normalCutoffWave η (scaledPlaneWave ξ h (B.profile a j)))
          z.1 z.2)‖ ≤ C * h ^ (M + 1) := by
  obtain ⟨C₀, hC₀, hb₀⟩ := B.exists_uncut_scalar_residual_bound A₀ τ₀ c₀ hU hK hKU a ha ha0 M hCT he
  obtain ⟨C₁, hC₁, hb₁⟩ := B.exists_cutoff_defect_bound hU hK hKU a ha ha0 η hT M (M + 1)
  refine ⟨C₀ + (M + 1 : ℕ) * C₁, by positivity, ?_⟩
  intro z hz ht h hh hh1
  let y := z.1
  let t := z.2
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i l => (A₀ z i l : ℂ))
  let c : Fin n → ℂ := fun i => (c₀ z i : ℂ)
  let V (j : ℕ) := conjugatedSplitOperator A (τ₀ z) c ξ h (B.profile a j) y (t / h)
  let E (j : ℕ) := scaledCutoffDefect (τ₀ z) η h (B.profile a j) y t
  have hsymm : ∀ i l, A i l = A l i := by
    intro i l
    exact congrArg Complex.ofReal (hS z hz ht i l)
  have heq : (∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * ((h : ℂ) ^ 2 *
      complexSplitOperator A (τ₀ z) c (normalCutoffWave η (scaledPlaneWave ξ h (B.profile a j))) y t)) =
      tangentialWave ξ h y * ((η t : ℂ) * (∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * V j) +
        ∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * E j) := by
    simp only [mul_add, mul_sum, sum_add_distrib]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rw [complexSplitOperator_scaledCutoff A hsymm (τ₀ z) c ξ η.contDiff hh.ne'
      (B.profile_contDiff hU hK.isClosed hKU a ha ha0 j)]
    change _ = tangentialWave ξ h y * ((η t : ℂ) * ((h ^ j : ℂ) * V j)) +
      tangentialWave ξ h y * ((h ^ j : ℂ) * E j)
    ring
  have heach (j : ℕ) (hj : j ∈ Finset.range (M + 1)) : ‖(h ^ j : ℂ) * E j‖ ≤ C₁ * h ^ (M + 1) := by
    have hjM : j ≤ M := by have hhj := Finset.mem_range.mp hj; omega
    have hp : ‖(h ^ j : ℂ)‖ ≤ 1 := by
      simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] using pow_le_one₀ (n := j) hh.le hh1
    have hτ' : ‖(τ₀ z : ℂ)‖ ≤ T := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hτ z hz ht
    rw [norm_mul]
    exact (mul_le_mul hp (hb₁ j hjM y hz t ht.1 h hh hh1 (τ₀ z) hτ')
      (norm_nonneg _) (by positivity)).trans_eq (one_mul _)
  change ‖∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * ((h : ℂ) ^ 2 *
    complexSplitOperator A (τ₀ z) c (normalCutoffWave η (scaledPlaneWave ξ h (B.profile a j))) y t)‖ ≤ _
  rw [heq, norm_mul, norm_tangentialWave, one_mul]
  calc
    _ ≤ ‖(η t : ℂ) * (∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * V j)‖ +
      ‖∑ j ∈ Finset.range (M + 1), (h ^ j : ℂ) * E j‖ := norm_add_le _ _
    _ ≤ C₀ * h ^ (M + 1) + ∑ j ∈ Finset.range (M + 1), C₁ * h ^ (M + 1) := by
      apply add_le_add
      · rw [norm_mul]
        have hη : ‖(η t : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg η.nonneg] using η.le_one
        exact (mul_le_mul hη (hb₀ z hz ht h hh hh1) (norm_nonneg _) (by positivity)).trans_eq (one_mul _)
      · exact (norm_sum_le _ _).trans (sum_le_sum heach)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
