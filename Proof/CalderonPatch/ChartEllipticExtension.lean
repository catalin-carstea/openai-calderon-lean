module

public import Proof.CalderonPatch.ChartEllipticBounds

import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace TauCeti.PDE
open scoped ContDiff ENNReal Matrix.Norms.Elementwise NNReal Topology RealInnerProductSpace

namespace CalderonPatch

open CalderonN (X I Mat MetricField divergenceCoeff contDiffOn_divergenceCoeff)

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem contDiff_matrixBilinearForm_of_contDiff {A : X n → Mat n}
    (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (fun z => matrixBilinearForm (A z)) := by
  apply contDiffOn_univ.mp
  let : NormedAddCommGroup (X n →L[ℝ] X n →L[ℝ] ℝ) := inferInstance
  let B (z : X n) := matrixBilinearForm (A z)
  have hAOn : ContDiffOn ℝ ∞ A Set.univ := hA.contDiffOn
  have hB : ContDiffOn ℝ ∞ B Set.univ :=
    ((matrixBilinearFormLinear (n := I n)).contDiff.comp_contDiffOn hAOn).congr
      fun _ _ => (matrixBilinearFormLinear_apply _).symm
  exact hB

/-- A signed metric energy coefficient field on a compact coordinate
region has a globally smooth, bounded and elliptic extension. Blend
with the identity in a region where the original matrix is positive,
so the difference from the identity has compact support. -/
theorem exists_smooth_divergenceMatrix_extension_constantOutside {O C : Set (X n)} (hO : IsOpen O)
    {g : MetricField n} (hg : CalderonN.SmoothMetric O g) (hC : IsCompact C) (hCO : C ⊆ O) :
    ∃ (A : X n → Mat n) (U : Set (X n)) (lam Lam : ℝ) (L : ℝ≥0),
      IsOpen U ∧ C ⊆ U ∧ U ⊆ O ∧
      EqOn A (fun z => Matrix.of (divergenceCoeff g z)) U ∧
      ContDiff ℝ ∞ A ∧
      ContDiff ℝ ∞ (fun z => matrixBilinearForm (A z)) ∧
      UniformlyEllipticOn Set.univ A lam Lam ∧
      LipschitzWith L (fun z => matrixBilinearForm (A z)) ∧
      (∀ z v, v ≠ 0 → 0 < matrixBilinearForm (A z) v v) ∧
      HasCompactSupport (fun z => A z - 1) := by
  let A₀ (z : X n) : Mat n := Matrix.of (divergenceCoeff g z)
  obtain ⟨K,hK,_,hCK,hKO⟩ := exists_compact_closed_between hC hO hCO
  obtain ⟨χ,hχ,hχrange,hχ1,hχc,hχs⟩ := hC.exists_contDiff_cutoff isOpen_interior hCK
  let U := interior (χ ⁻¹' {1})
  let A (z : X n) : Mat n := χ z • A₀ z + (1 - χ z) • (1 : Mat n)
  have hχK : tsupport χ ⊆ K := hχs.trans interior_subset
  have hUχ (z : X n) (hz : z ∈ U) : χ z = 1 :=
    mem_singleton_iff.mp (interior_subset hz : z ∈ χ ⁻¹' {1})
  have hUK : U ⊆ K := fun z hz => hχK (subset_tsupport _ (by simp [hUχ z hz]))
  have hOut (z : X n) (hz : z ∉ tsupport χ) : A =ᶠ[𝓝 z] fun _ => (1 : Mat n) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    simp [A,hw]
  have hA₀ : ContDiffOn ℝ ∞ A₀ O :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => contDiffOn_divergenceCoeff hg i j
  have hA : ContDiff ℝ ∞ A := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ O
    · exact ((hχ.contDiffOn.smul hA₀).add
        ((contDiffOn_const.sub hχ.contDiffOn).smul contDiffOn_const)).contDiffAt (hO.mem_nhds hz)
    · exact contDiffAt_const.congr_of_eventuallyEq (hOut z (fun hs => hz (hKO (hχK hs))))
  obtain ⟨lam,Lam,hEll⟩ := exists_uniformlyEllipticOn_divergenceMatrix hg hK hKO
  let lo := min lam 1
  let hi := max Lam 1
  have hlo : 0 < lo := lt_min hEll.pos zero_lt_one
  have hhi : lo ≤ hi := (min_le_left _ _).trans (hEll.le.trans (le_max_left _ _))
  have hOne (v w : X n) : matrixBilinearForm (1 : Mat n) v w = ⟪v,w⟫ := by
    rw [matrixBilinearForm_one_apply]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hBL (z : X n) (v w : X n) :
      matrixBilinearForm (A z) v w =
        χ z * matrixBilinearForm (A₀ z) v w + (1 - χ z) * ⟪v,w⟫ := by
    dsimp only [A]
    rw [matrixBilinearForm_add_apply, matrixBilinearForm_smul_apply,
      matrixBilinearForm_smul_apply, hOne]
  have hExt : UniformlyEllipticOn Set.univ A lo hi := by
    refine ⟨hlo,hhi,fun z _ => ?_⟩
    have hχz := hχrange (mem_range_self z)
    have ht : 0 ≤ 1 - χ z := sub_nonneg.mpr hχz.2
    by_cases hz : z ∈ K
    · constructor
      · intro v
        rw [← matrixBilinearForm_self,hBL,real_inner_self_eq_norm_sq,matrixBilinearForm_self]
        have hbase := (mul_le_mul_of_nonneg_right (min_le_left lam 1) (sq_nonneg ‖v‖)).trans
          (hEll.lower_bound hz v)
        have hId : lo * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_right lam 1) (sq_nonneg ‖v‖)
        have hsum := add_le_add (mul_le_mul_of_nonneg_left hbase hχz.1)
          (mul_le_mul_of_nonneg_left hId ht)
        convert hsum using 1 <;> ring
      · intro v w
        rw [← matrixBilinearForm_apply,hBL]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul,abs_mul,abs_of_nonneg hχz.1,abs_of_nonneg ht,matrixBilinearForm_apply]
        have hbase := (hEll.upper_bound hz v w).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left Lam 1)
            (norm_nonneg v)) (norm_nonneg w))
        have hId : |⟪v,w⟫| ≤ hi * ‖v‖ * ‖w‖ := (abs_real_inner_le_norm _ _).trans
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right Lam 1)
              (norm_nonneg v)) (norm_nonneg w))
        calc
          _ ≤ χ z * (hi * ‖v‖ * ‖w‖) + (1 - χ z) * (hi * ‖v‖ * ‖w‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hbase hχz.1) (mul_le_mul_of_nonneg_left hId ht)
          _ = _ := by ring
    · have hz1 : A z = 1 := (hOut z (fun h => hz (hχK h))).eq_of_nhds
      constructor
      · intro v
        rw [← matrixBilinearForm_self,hz1,hOne]
        change lo * ‖v‖ ^ 2 ≤ ⟪v,v⟫
        rw [real_inner_self_eq_norm_sq]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_right lam 1) (sq_nonneg ‖v‖)
      · intro v w
        rw [← matrixBilinearForm_apply,hz1,hOne]
        change |⟪v,w⟫| ≤ _
        apply (abs_real_inner_le_norm _ _).trans
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right Lam 1) (norm_nonneg v)) (norm_nonneg w)
  let F (z : X n) := matrixBilinearForm (A z)
  let : NormedAddCommGroup (X n →L[ℝ] X n →L[ℝ] ℝ) := inferInstance
  have hF : ContDiff ℝ ∞ F := contDiff_matrixBilinearForm_of_contDiff hA
  obtain ⟨B,hB⟩ := hχc.exists_bound_of_continuousOn
    ((hF.continuous_fderiv (by simp)).continuousOn)
  have hLip : LipschitzWith (⟨max B 0,le_max_right _ _⟩ : ℝ≥0) F := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (hF.differentiable (by simp))
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact_mod_cast (hB z hz).trans (le_max_left B 0)
    · have hZ : F =ᶠ[𝓝 z] fun _ => matrixBilinearForm (1 : Mat n) :=
        (hOut z hz).fun_comp matrixBilinearForm
      rw [hZ.fderiv_eq]
      have hConst : fderiv ℝ (fun _ : X n => matrixBilinearForm (1 : Mat n)) z = 0 := by simp
      rw [hConst,nnnorm_zero]
      exact zero_le
  refine ⟨A,U,lo,hi,_,isOpen_interior,hχ1,hUK.trans hKO,fun z hz => ?_,hA,hF,hExt,hLip,?_,?_⟩
  · simp [A,A₀,hUχ z hz]
  · intro z v hv
    rw [matrixBilinearForm_self]
    exact (mul_pos hlo (pow_pos (norm_pos_iff.mpr hv) 2)).trans_le (hExt.lower_bound (mem_univ _) v)

  · apply hχc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport χ)
    intro z hz
    by_contra hs
    exact hz (sub_eq_zero.mpr ((hOut z hs).eq_of_nhds))

/-- A signed metric energy coefficient field on a compact coordinate
region has a globally smooth, bounded and elliptic extension. Blend
with the identity in a region where the original matrix is positive. -/
theorem exists_smooth_divergenceMatrix_extension {O C : Set (X n)} (hO : IsOpen O)
    {g : MetricField n} (hg : CalderonN.SmoothMetric O g) (hC : IsCompact C) (hCO : C ⊆ O) :
    ∃ (A : X n → Mat n) (U : Set (X n)) (lam Lam : ℝ) (L : ℝ≥0),
      IsOpen U ∧ C ⊆ U ∧ U ⊆ O ∧
      EqOn A (fun z => Matrix.of (divergenceCoeff g z)) U ∧
      ContDiff ℝ ∞ A ∧
      ContDiff ℝ ∞ (fun z => matrixBilinearForm (A z)) ∧
      UniformlyEllipticOn Set.univ A lam Lam ∧
      LipschitzWith L (fun z => matrixBilinearForm (A z)) ∧
      (∀ z v, v ≠ 0 → 0 < matrixBilinearForm (A z) v v) := by
  obtain ⟨A,U,lam,Lam,L,hU,hCU,hUO,hEq,hA,hF,hEll,hLip,hPos,_⟩ :=
    exists_smooth_divergenceMatrix_extension_constantOutside hO hg hC hCO
  exact ⟨A,U,lam,Lam,L,hU,hCU,hUO,hEq,hA,hF,hEll,hLip,hPos⟩

end CalderonPatch
