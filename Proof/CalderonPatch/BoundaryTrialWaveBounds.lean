module

public import Proof.CalderonPatch.NativeBoundaryWave

import Proof.CalderonPatch.BoundaryLayerScalar
import Mathlib.Tactic

public section

noncomputable section
open Filter Finset Set
open scoped ContDiff Manifold

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n+1)

/-- The positive-side trial values are uniformly bounded as the
tangential frequency tends to infinity. -/
theorem BoundaryLayerCoefficients.exists_finiteWave_norm_bound
    {ξ : I n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (hU : IsOpen U)
    {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ContDiffBump (0 : ℝ)) (N : ℕ) :
    ∃ A ≥ (0 : ℝ), ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ y : Y, ∀ t ≥ (0 : ℝ),
      ‖B.finiteWave a η N h (y,t)‖ ≤ A := by
  obtain ⟨c,C,hc,hC,hprof⟩ :=
    B.exists_uniform_layerJet_moment_exp_bound hU hK hKU a ha ha0 N 0
  refine ⟨(N+1 : ℕ) * C, by positivity, fun h hh hh₁ y t ht => ?_⟩
  by_cases hy : y ∈ K
  · rw [finiteWave,norm_mul,norm_tangentialWave,one_mul]
    apply (norm_sum_le _ _).trans
    have hsum : (∑ _j ∈ range (N + 1), C) = (N + 1 : ℕ) * C := by
      simp [nsmul_eq_mul]
    rw [← hsum]
    apply sum_le_sum
    intro j hj
    have hj' : j < N + 1 := mem_range.mp hj
    let k : Fin (N + 1) := ⟨j,hj'⟩
    have hq := hprof k (Sum.inl PUnit.unit) y hy (t / h) (div_nonneg ht hh.le)
    have hP : ‖B.profile a j (y,t / h)‖ ≤ C := by
      apply (show ‖B.profile a j (y,t / h)‖ ≤ C * Real.exp (-c * (t / h)) from ?_).trans
        ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (div_nonneg ht hh.le))) hC).trans_eq (mul_one _))
      simpa only [pow_zero,one_mul,profile,layerJetPolynomial,k] using hq
    rw [norm_mul, norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh.le]
    have he : ‖cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h (y,t)‖ ≤ C := by
      change ‖(η t : ℝ) • B.profile a j (y,t / h)‖ ≤ C
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg η.nonneg]
      exact (mul_le_mul η.le_one hP (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    exact (mul_le_mul (pow_le_one₀ hh.le hh₁) he (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · have hSupp := B.finiteWave_tsupport_subset hU hK.isClosed a ha ha0 η N h
    have hz : B.finiteWave a η N h (y,t) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hSupp h).1)
    rw [hz,norm_zero]
    positivity

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

omit [T2Space M] in
/-- A uniform bound for a trial wave on the positive side of its
signed domain bounds both of its native components. -/
theorem abs_nativeWaveComponent_le
    {g : SmoothMetric (n+1) M} {p : M} (D : NativeBoundaryMetricChart g p)
    {V : Y × ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hV : ∀ y : Y, ∀ t ≥ (0 : ℝ), ‖V (y,t)‖ ≤ A)
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, |L z| ≤ ‖z‖) (x : M) :
    |nativeWaveComponent D V L x| ≤ A := by
  by_cases hx : x ∈ D.coord.source
  · rw [nativeWaveComponent,boundaryChartTest,indicator_of_mem hx]
    have h := D.coord.map_source hx
    rw [D.target_eq] at h
    let z := signedLayerCoordinates.symm (D.coord x)
    have ht : 0 ≤ z.2 := by
      rw [← signedLayerCoordinates_height z]
      exact mem_inwardHalfSpace.mp
        ((signedLayerCoordinates.apply_symm_apply (D.coord x)).symm ▸ h.2)
    exact (hL _).trans (hV z.1 z.2 ht)
  · simpa only [nativeWaveComponent,boundaryChartTest,indicator_of_notMem hx,abs_zero] using hA

end CalderonPatch.BoundaryLayer
