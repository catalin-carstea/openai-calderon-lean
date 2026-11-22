module

public import Proof.Manuscript.MovingTrace.SphericalCollarMetric
public import Proof.Manuscript.MovingTrace.CollarPrincipalRadiusJet
public import Proof.CalderonN.ConstantMetricScale
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Metric
open scoped ContDiff Matrix

namespace CalderonPaper

variable {n : ℕ}
local notation "Z" => X (n + 1)

theorem framedNormalMetric_eq_normalizedBallMetric {d : ℕ} [NeZero d]
    (g : MetricField d) (E : X d × X d → X d) (hE : ContDiff ℝ ∞ E) (e : Frame d) (y : X d) (r : ℝ) :
    framedNormalMetric g e E y r = normalizedBallMetric g E e y r := by
  funext z
  ext i j
  simp only [normalizedBallMetric, Matrix.mul_apply, Matrix.transpose_apply, coordinateMatrix_apply,
    normalizedBallDerivative, ContinuousLinearMap.comp_apply, frameVectorL_apply _ _ y, frameVector_axis]
  unfold framedNormalMetric normalPullbackMetricPair metricPair
  rw [← Finset.sum_comm]
  have hVertical (v w : X d) :
      fderiv ℝ (fun ξ => E (y,ξ)) v w = fderiv ℝ E (y,v) (0,w) := by
    have h := ((hE.differentiable (by simp) (y,v)).hasFDerivAt.comp v
      ((hasFDerivAt_const y v).prodMk (hasFDerivAt_id v))).fderiv
    exact congrArg (fun L : X d →L[ℝ] X d => L w) h
  simp only [Finset.sum_mul, normalBallChartMap, hVertical]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem framedNormalMetric_conformal {d : ℕ} [NeZero d]
    {g γ : MetricField d} {E : X d × X d → X d} (e : Frame d) (y z : X d) (r c : ℝ)
    (h : g (E (y,r • frameVector e y z)) = c • γ (E (y,r • frameVector e y z))) :
    framedNormalMetric g e E y r z = c • framedNormalMetric γ e E y r z := by
  ext i j
  change normalPullbackMetricPair g E y r (frameVector e y z) (e y i) (e y j) =
    c * normalPullbackMetricPair γ E y r (frameVector e y z) (e y i) (e y j)
  unfold normalPullbackMetricPair metricPair
  rw [h]
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem pullbackMetric_pointwise_smul {d : ℕ} [NeZero d]
    (g γ : MetricField d) (F : X d → X d) (z : X d) (c : ℝ) (h : g (F z) = c • γ (F z)) :
    pullbackMetric g F z = c • pullbackMetric γ F z := by
  unfold pullbackMetric
  rw [h, Matrix.mul_smul, Matrix.smul_mul]

/-- A conformal first metric in the spherical collar has no mixed
principal terms. Dividing by its radial coefficient cancels the
conformal scalar and recovers the inverse tangential reference block. -/
theorem normalized_first_collar_principal
    {G Γ : MetricField (n+1)} {O : Set Z} {z : Z} (hz : z ∈ O)
    (hΓ : HasNormalMetricBlock 0 Γ O) (hPos : (Γ z).PosDef)
    {c : ℝ} (hc : 0 < c) (hConf : G z = c • Γ z) :
    0 < (G z)⁻¹ 0 0 ∧
      (∀ j : I n, (G z)⁻¹ 0 j.succ = 0 ∧ (G z)⁻¹ j.succ 0 = 0) ∧
      ∀ i j : I n, (G z)⁻¹ i.succ j.succ / (G z)⁻¹ 0 0 = (Γ z)⁻¹ i.succ j.succ := by
  have hInv : (G z)⁻¹ = c⁻¹ • (Γ z)⁻¹ := by
    rw [hConf]
    exact Matrix.inv_smul' _ (Units.mk0 c hc.ne') (isUnit_iff_ne_zero.mpr hPos.det_pos.ne')
  have hR (i : I (n+1)) := inverse_normalMetricBlock_row hΓ hz hPos i
  have hDiag : (G z)⁻¹ 0 0 = c⁻¹ := by
    simp [hInv,hR 0]
  refine ⟨hDiag ▸ inv_pos.mpr hc, ?_, ?_⟩
  · intro i
    have hZero : (Γ z)⁻¹ 0 i.succ = 0 := by
      simpa only [ite_eq_right (Fin.succ_ne_zero i).symm] using hR i.succ
    have hSym : (Γ z)⁻¹ i.succ 0 = (Γ z)⁻¹ 0 i.succ :=
      congrFun (congrFun hPos.inv.isHermitian.isSymm.eq 0) i.succ
    constructor <;> simp [hInv,hSym,hZero]
  · intro i j
    rw [hDiag, hInv]
    simp only [Matrix.smul_apply,smul_eq_mul]
    field_simp

end CalderonPaper
