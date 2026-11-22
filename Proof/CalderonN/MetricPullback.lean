module

public import Proof.CalderonN.Piola
public import Proof.CalderonN.MetricDivergence

import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Covariant metric in a general smooth coordinate map. -/
@[expose] def pullbackMetric (g : (MetricField dim)) (F : (X dim) → (X dim)) (x : (X dim)) : (Mat dim) :=
  (coordinateJacobian F x)ᵀ * g (F x) * coordinateJacobian F x

@[expose] def metricFluxVector (g : (MetricField dim)) (u : (X dim) → ℝ) (x : (X dim)) : (X dim) :=
  WithLp.toLp 2 (fun i => divergenceFlux g u x i)

theorem contDiffOn_metricFluxVector {U : Set (X dim)} (hU : IsOpen U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) {u : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (metricFluxVector g u) U :=
  (contDiffOn_piLp 2).mpr fun i => contDiffOn_divergenceFlux hU hg hu i

theorem chartVolume_pullbackMetric (g : (MetricField dim)) (F : (X dim) → (X dim)) (x : (X dim)) :
    chartVolume (pullbackMetric g F) x = |(coordinateJacobian F x).det| * chartVolume g (F x) := by
  let J := coordinateJacobian F x
  unfold chartVolume pullbackMetric
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  change Real.sqrt (J.det * (g (F x)).det * J.det) = |J.det| * Real.sqrt (g (F x)).det
  rw [show J.det * (g (F x)).det * J.det = J.det^2 * (g (F x)).det by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

theorem smoothMetric_pullbackMetric {U V : Set (X dim)} {g : (MetricField dim)} (hg : SmoothMetric U g)
    {F : (X dim) → (X dim)} (hF : ContDiff ℝ ∞ F) (hMap : MapsTo F V U)
    (hJ : ∀ x ∈ V, (coordinateJacobian F x).det ≠ 0) :
    SmoothMetric V (pullbackMetric g F) := by
  refine ⟨?_,?_⟩
  · intro i j
    simp only [pullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
    exact ContDiffOn.sum fun a _ => (ContDiffOn.sum fun b _ =>
      (contDiff_coordinateJacobian_entry F hF b i).contDiffOn.mul
        ((hg.1 b a).comp hF.contDiffOn hMap)).mul
          (contDiff_coordinateJacobian_entry F hF a j).contDiffOn
  · intro x hx
    unfold pullbackMetric
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (hg.2 _ (hMap hx)).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr (hJ x hx))))

/-- The change of variables for the metric divergence flux. At this
stage it is pointwise and uses only the derivative of the chart. -/
theorem metricFluxVector_pullbackMetric {F : (X dim) → (X dim)} {g : (MetricField dim)} {u : (X dim) → ℝ} {x : (X dim)}
    (hF : DifferentiableAt ℝ F x) (hu : DifferentiableAt ℝ u (F x))
    (hJ : (coordinateJacobian F x).det ≠ 0) :
    metricFluxVector (pullbackMetric g F) (u ∘ F) x =
      |(coordinateJacobian F x).det| •
        WithLp.toLp 2 ((coordinateJacobian F x)⁻¹ *ᵥ
          (fun i => divergenceFlux g u (F x) i)) := by
  let J := coordinateJacobian F x
  let V := fun i => coordDeriv i u (F x)
  let A := g (F x)
  have hCalc (H : (MetricField dim)) (f : (X dim) → ℝ) (y : (X dim)) :
      (fun i => divergenceFlux H f y i) =
        chartVolume H y • ((H y)⁻¹ *ᵥ (fun j => coordDeriv j f y)) := by
    ext i
    simp only [divergenceFlux,divergenceCoeff,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,
      dotProduct,Finset.mul_sum,mul_assoc]
  have hgrad : (fun i => coordDeriv i (u ∘ F) x) = Jᵀ *ᵥ V := by
    funext i
    rw [coordDeriv,(hu.hasFDerivAt.comp x hF.hasFDerivAt).fderiv]
    change fderiv ℝ u (F x) (fderiv ℝ F x (axis i)) = _
    conv_lhs => rw [← vector_eq_sum_axis (fderiv ℝ F x (axis i))]
    simp only [map_sum,map_smul,smul_eq_mul,J,coordinateJacobian]
    rfl
  have hInv : (Jᵀ * A * J)⁻¹ = J⁻¹ * A⁻¹ * (Jᵀ)⁻¹ := by
    rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,Matrix.mul_assoc]
  have hId : (Jᵀ)⁻¹ * Jᵀ = 1 := Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (by rwa [Matrix.det_transpose]))
  have he : (fun i => divergenceFlux (pullbackMetric g F) (u ∘ F) x i) =
      |J.det| • (J⁻¹ *ᵥ (fun i => divergenceFlux g u (F x) i)) := by
    rw [hCalc,hgrad,chartVolume_pullbackMetric]
    change (|J.det| * chartVolume g (F x)) • ((Jᵀ*A*J)⁻¹ *ᵥ (Jᵀ *ᵥ V)) = _
    rw [hInv,Matrix.mulVec_mulVec,Matrix.mul_assoc (J⁻¹ * A⁻¹) (Jᵀ)⁻¹ Jᵀ,hId,mul_one,
      mul_smul,← Matrix.mulVec_mulVec,← Matrix.mulVec_smul,hCalc]
  exact congrArg (WithLp.toLp 2) he

theorem coordinateFluxDivergence_metricPullback {U : Set (X dim)} (hU : IsOpen U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) {F : (X dim) → (X dim)} (hF : ContDiff ℝ ∞ F)
    {u : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    {x : (X dim)} (hx : F x ∈ U) (hJ : (coordinateJacobian F x).det ≠ 0) :
    coordinateFluxDivergence (metricFluxVector (pullbackMetric g F) (u ∘ F)) x =
      |(coordinateJacobian F x).det| * coordinateFluxDivergence (metricFluxVector g u) (F x) := by
  let J := coordinateJacobian F
  let Z := metricFluxVector g u
  have hDet : Continuous (fun y => (J y).det) :=
    (contDiffOn_univ.mp (contDiffOn_det_of_entries (fun i j =>
      (contDiff_coordinateJacobian_entry F hF i j).contDiffOn))).continuous
  have hFnear : ∀ᶠ y in 𝓝 x, F y ∈ U := hF.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
  have hZd : DifferentiableAt ℝ Z (F x) :=
    ((contDiffOn_metricFluxVector hU hg hu).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hAdj (A : (Mat dim)) (hA : A.det ≠ 0) : A.adjugate = A.det • A⁻¹ := by
    rw [Matrix.inv_def,Ring.inverse_eq_inv',smul_smul,mul_inv_cancel₀ hA,one_smul]
  have hSigned (y : (X dim)) (hy : (J y).det ≠ 0) :
      signedPiolaFlux F Z y = (J y).det • WithLp.toLp 2 ((J y)⁻¹ *ᵥ fun i => divergenceFlux g u (F y) i) := by
    change WithLp.toLp 2 ((J y).adjugate *ᵥ fun i => divergenceFlux g u (F y) i) = _
    rw [hAdj (J y) hy,Matrix.smul_mulVec]
    rfl
  by_cases hPos : 0 < (J x).det
  · have hNear : ∀ᶠ y in 𝓝 x, 0 < (J y).det := hDet.continuousAt.eventually (lt_mem_nhds hPos)
    have he : metricFluxVector (pullbackMetric g F) (u ∘ F) =ᶠ[𝓝 x] signedPiolaFlux F Z := by
      filter_upwards [hNear,hFnear] with y hy hyU
      rw [metricFluxVector_pullbackMetric (hF.differentiable (by simp) y)
        ((hu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hyU)) hy.ne',
        hSigned y hy.ne',abs_of_pos hy]
    rw [coordinateFluxDivergence_congr_germ he,coordinateFluxDivergence_signedPiolaFlux F Z hF x hZd hJ,
      abs_of_pos hPos]
  · have hNeg : (J x).det < 0 := lt_of_le_of_ne (le_of_not_gt hPos) hJ
    have hNear : ∀ᶠ y in 𝓝 x, (J y).det < 0 := hDet.continuousAt.eventually (gt_mem_nhds hNeg)
    have he : metricFluxVector (pullbackMetric g F) (u ∘ F) =ᶠ[𝓝 x] fun y => -signedPiolaFlux F Z y := by
      filter_upwards [hNear,hFnear] with y hy hyU
      rw [metricFluxVector_pullbackMetric (hF.differentiable (by simp) y)
        ((hu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hyU)) hy.ne,
        hSigned y hy.ne,abs_of_neg hy,neg_smul]
    rw [coordinateFluxDivergence_congr_germ he]
    have hn : coordinateFluxDivergence (fun y => -signedPiolaFlux F Z y) x =
        -coordinateFluxDivergence (signedPiolaFlux F Z) x := by
      simp only [coordinateFluxDivergence,coordDeriv,PiLp.neg_apply,fderiv_fun_neg,neg_apply,
        Finset.sum_neg_distrib]
    rw [hn,coordinateFluxDivergence_signedPiolaFlux F Z hF x hZd hJ,abs_of_neg hNeg,neg_mul]

/-- The actual chart Laplacian is invariant under the smooth local
coordinate change wherever the derivative is invertible. -/
theorem laplace_pullbackMetric {U : Set (X dim)} (hU : IsOpen U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) {F : (X dim) → (X dim)} (hF : ContDiff ℝ ∞ F)
    {u : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    {x : (X dim)} (hx : F x ∈ U) (hJ : (coordinateJacobian F x).det ≠ 0) :
    laplace (pullbackMetric g F) (u ∘ F) x = laplace g u (F x) := by
  let V := F ⁻¹' U ∩ {z | (coordinateJacobian F z).det ≠ 0}
  have hDet : Continuous (fun y => (coordinateJacobian F y).det) :=
    (contDiffOn_univ.mp (contDiffOn_det_of_entries (fun i j =>
      (contDiff_coordinateJacobian_entry F hF i j).contDiffOn))).continuous
  have hV : IsOpen V := (hU.preimage hF.continuous).inter (isOpen_ne_fun hDet continuous_const)
  have hxV : x ∈ V := ⟨hx,hJ⟩
  have hMap : MapsTo F V U := fun _ hz => hz.1
  have hG := smoothMetric_pullbackMetric hg hF hMap (fun y hy => hy.2)
  have hUcomp := hu.comp hF.contDiffOn hMap
  have hLeft := chartVolume_mul_laplace_eq_divergence hV hG hUcomp hxV
  have hRight := chartVolume_mul_laplace_eq_divergence hU hg hu hx
  have hEq := coordinateFluxDivergence_metricPullback hU hg hF hu hx hJ
  change (∑ i : (I dim), coordDeriv i (fun y => divergenceFlux (pullbackMetric g F) (u ∘ F) y i) x) =
    |(coordinateJacobian F x).det| * ∑ i : (I dim), coordDeriv i (fun y => divergenceFlux g u y i) (F x) at hEq
  rw [← hLeft,← hRight,chartVolume_pullbackMetric,← mul_assoc] at hEq
  exact mul_left_cancel₀ (mul_ne_zero (abs_ne_zero.mpr hJ)
    (Real.sqrt_pos.mpr (hg.2 _ hx).det_pos).ne') hEq

end CalderonN
