module

public import Proof.Manuscript.MovingTrace.StereographicPolarCollar
public import Proof.CalderonN.MetricPullback
public import Proof.CalderonN.NormalizedBallMetric
public import Proof.CalderonPatch.NativeBoundaryLayerOperator
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Filter Metric
open scoped ContDiff Topology Matrix

namespace CalderonPaper

variable {n : ℕ}
local notation "Z" => X (n + 1)
local notation "Y" => X n
local notation "S" => sphere (0 : Z) 1

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

/-- The signed collar written in the Euclidean coordinates whose zero axis
is inward depth. This is the input chart used by the released split operator. -/
def signedSphericalCollar (v : ↥S) (z : Z) : Z :=
  polarCollar (angularPoint v) (signedLayerCoordinates.symm z)

theorem signedSphericalCollar_contDiff (v : ↥S) : ContDiff ℝ ∞ (signedSphericalCollar v) := by
  have hF : ContDiff ℝ ∞ (polarCollar (angularPoint v)) :=
    (contDiff_const.sub contDiff_snd).smul ((angularPoint_contDiff v).comp contDiff_fst)
  exact hF.comp signedLayerCoordinates.symm.contDiff

theorem signedSphericalCollar_derivative_apply (v : ↥S) (z : Z) (u : Y × ℝ) :
    fderiv ℝ (signedSphericalCollar v) z (signedLayerCoordinates u) =
      fderiv ℝ (polarCollar (angularPoint v)) (signedLayerCoordinates.symm z) u := by
  have hF : Differentiable ℝ (polarCollar (angularPoint v)) := by
    exact ((contDiff_const.sub contDiff_snd).smul
      ((angularPoint_contDiff v).comp contDiff_fst)).differentiable (by simp)
  change fderiv ℝ (polarCollar (angularPoint v) ∘ signedLayerCoordinates.symm) z _ = _
  rw [fderiv_comp z (hF _) signedLayerCoordinates.symm.differentiableAt]
  rw [show fderiv ℝ (⇑signedLayerCoordinates.symm) z = signedLayerCoordinates.symm.toContinuousLinearMap from
    signedLayerCoordinates.symm.toContinuousLinearMap.fderiv]
  simp

theorem signedSphericalCollar_derivative_bijective (v : ↥S) (z : Z)
    (hz : (signedLayerCoordinates.symm z).2 < 1) :
    Function.Bijective (fderiv ℝ (signedSphericalCollar v) z) := by
  let F := signedSphericalCollar v
  let G : Z → Z := signedLayerCoordinates ∘ polarReadout v
  let O : Set Z := {q | (signedLayerCoordinates.symm q).2 < 1}
  have hO : IsOpen O := isOpen_lt (continuous_snd.comp signedLayerCoordinates.symm.continuous) continuous_const
  have hG : ContDiffOn ℝ ∞ G (polarReadoutDomain v) :=
    signedLayerCoordinates.contDiff.comp_contDiffOn (polarReadout_contDiffOn v)
  have hzT : F z ∈ polarReadoutDomain v := polarCollar_mapsTo v hz
  have hD := (hG.contDiffAt ((polarReadoutDomain_isOpen v).mem_nhds hzT)).differentiableAt (by simp)
  have hFG : G ∘ F =ᶠ[𝓝 z] (id : Z → Z) := by
    filter_upwards [hO.mem_nhds hz] with q hq
    change signedLayerCoordinates (polarReadout v (polarCollar (angularPoint v) (signedLayerCoordinates.symm q))) = q
    rw [polarReadout_polarCollar v _ hq, signedLayerCoordinates.apply_symm_apply]
  have hLeft : fderiv ℝ G (F z) ∘SL fderiv ℝ F z = ContinuousLinearMap.id ℝ Z := by
    rw [← fderiv_comp z hD ((signedSphericalCollar_contDiff v).differentiable (by simp) z),
      hFG.fderiv_eq,fderiv_id]
  have hInj : Function.Injective (fderiv ℝ F z) := by
    have hInv : Function.LeftInverse (fderiv ℝ G (F z)) (fderiv ℝ F z) := fun u =>
      congrArg (fun L : Z →L[ℝ] Z => L u) hLeft
    exact hInv.injective
  exact ⟨hInj, (LinearMap.injective_iff_surjective (f := (fderiv ℝ F z).toLinearMap)).mp hInj⟩

theorem pullbackMetric_entry_metricPair {d : ℕ} [NeZero d] (g : MetricField d) (F : X d → X d)
    (z : X d) (i j : I d) :
    pullbackMetric g F z i j = metricPair g (F z) (fderiv ℝ F z (axis i)) (fderiv ℝ F z (axis j)) := by
  simp only [pullbackMetric,coordinateJacobian,Matrix.mul_apply,Matrix.transpose_apply,
    coordinateMatrix_apply,metricPair,Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Gauss lemma in the signed stereographic boundary chart of the
rescaled reference normal ball. -/
theorem signedSphericalCollar_unit_radial_row
    {A Ω : Set Z} (hΩ : IsOpen Ω) {K : ℝ} {γ : MetricField (n+1)}
    (hEll : Elliptic Ω K γ) (hK : 0 < K)
    {E : Z × Z → Z} {R : Z → ℝ}
    (hN : NormalCoordinates A Ω γ E R) {y : Z} (hy : y ∈ A) (hyΩ : y ∈ Ω)
    (e : Frame (n+1)) (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : ℝ} (hr : r ≠ 0) (v : ↥S)
    {O : Set Z} (hO : ∀ z ∈ O, (signedLayerCoordinates.symm z).2 < 1)
    (hVelocity : ∀ z ∈ O, r • frameVector e y (signedSphericalCollar v z) ∈ interior (disk γ y (R y))) :
    HasNormalMetricBlock 0 (pullbackMetric (framedNormalMetric γ e E y r) (signedSphericalCollar v)) O := by
  intro z hz j
  let q := signedLayerCoordinates.symm z
  obtain ⟨hRadial,hMixed⟩ :=
    framedNormalMetric_polarCollar_radial_block hΩ hEll hK hN hy hyΩ e he hr
      isOpen_univ (angularPoint v) (fun x _ => angularPoint_norm v x) q (mem_univ _) (hO z hz)
      ((angularPoint_contDiff v).differentiable (by simp) q.1) (hVelocity z hz)
  rw [pullbackMetric_entry_metricPair, ← signedLayerCoordinates_axis_normal,
    signedSphericalCollar_derivative_apply]
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [← signedLayerCoordinates_axis_normal,signedSphericalCollar_derivative_apply,ite_eq_left rfl]
    exact hRadial
  · rw [← signedLayerCoordinates_axis_tangent,signedSphericalCollar_derivative_apply,ite_eq_right (Fin.succ_ne_zero k).symm]
    exact hMixed (axis k)

end CalderonPaper
