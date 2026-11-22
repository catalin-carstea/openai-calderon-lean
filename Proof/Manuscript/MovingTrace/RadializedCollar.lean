module

public import Proof.Manuscript.MovingTrace.RadializedMetric
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2900000

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Metric Matrix Filter
open scoped ContDiff InnerProductSpace Topology

namespace CalderonPaper

variable {d : ℕ} [NeZero d]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Near the unit sphere the metric is radialized completely. Near the
origin it is left unchanged and the radial projection is unnecessary. -/
def radialCutoff (z : X d) : ℝ := Real.smoothTransition (4 * ‖z‖^2 - 1)

theorem radialCutoff_contDiff : ContDiff ℝ ∞ (radialCutoff : X d → ℝ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_norm_sq ℝ)).sub contDiff_const)

theorem radialCutoff_range (z : X d) : 0 ≤ radialCutoff z ∧ radialCutoff z ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem radialCutoff_zero {z : X d} (hz : ‖z‖ ≤ 1/2) : radialCutoff z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith [norm_nonneg z])

theorem radialCutoff_one {z : X d} (hz : 3/4 ≤ ‖z‖) : radialCutoff z = 1 :=
  Real.smoothTransition.one_of_one_le (by nlinarith [norm_nonneg z])

theorem contDiffOn_radialReflection_entry (i j : I d) :
    ContDiffOn ℝ ∞ (fun z : X d => coordinateMatrix (radialReflection z) i j) {0}ᶜ := by
  have hDen : ContDiffOn ℝ ∞ (fun z : X d => 2 / ‖z‖^2) {0}ᶜ :=
    contDiffOn_const.div (contDiff_norm_sq ℝ).contDiffOn (fun z hz =>
      pow_ne_zero _ (norm_ne_zero_iff.mpr hz))
  have hInner : ContDiff ℝ ∞ (fun z : X d => ⟪z,axis j⟫_ℝ) := contDiff_id.inner ℝ contDiff_const
  have hRead : ContDiff ℝ ∞ (fun z : X d => z i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : X d →L[ℝ] ℝ).contDiff
  apply ((contDiffOn_const (c := (axis j) i)).sub
    ((hDen.mul hInner.contDiffOn).mul hRead.contDiffOn)).congr
  intro z hz
  simp only [coordinateMatrix_apply,radialReflection_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]

/-- Removing the mixed radial block extends smoothly through the origin
because its coefficient vanishes on a fixed ball. -/
theorem contDiffOn_radializedMetric_entries
    {T : Set (P × X d)} (hT : IsOpen T) {g : P × X d → Mat d}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) T) (i j : I d) :
    ContDiffOn ℝ ∞ (fun q : P × X d => radializedMetric radialCutoff (fun z => g (q.1,z)) q.2 i j) T := by
  let f (q : P × X d) := radializedMetric radialCutoff (fun z => g (q.1,z)) q.2 i j
  intro q hq
  by_cases hq₀ : q.2 = 0
  · have hBall : IsOpen {p : P × X d | ‖p.2‖ < 1/2} :=
      isOpen_lt continuous_snd.norm continuous_const
    have hqBall : q ∈ {p : P × X d | ‖p.2‖ < 1/2} := by simp [hq₀]
    have hEq : f =ᶠ[𝓝 q] fun p => g p i j := by
      filter_upwards [hBall.mem_nhds hqBall] with p hp
      change radializedMetric radialCutoff (fun z => g (p.1,z)) p.2 i j = g p i j
      rw [radializedMetric_eq_at_zeroCutoff (radialCutoff_zero (le_of_lt hp))]
    exact (((hg i j).contDiffAt (hT.mem_nhds hq)).congr_of_eventuallyEq hEq).contDiffWithinAt
  · let O : Set (P × X d) := T ∩ (univ ×ˢ ({0}ᶜ : Set (X d)))
    have hO : IsOpen O := hT.inter (isOpen_univ.prod isClosed_singleton.isOpen_compl)
    have hqO : q ∈ O := ⟨hq,mem_univ _,hq₀⟩
    let R (p : P × X d) := coordinateMatrix (radialReflection p.2)
    have hR (k l : I d) : ContDiffOn ℝ ∞ (fun p => R p k l) O :=
      (contDiffOn_radialReflection_entry k l).comp contDiffOn_snd (fun p hp => hp.2.2)
    have hG (k l : I d) : ContDiffOn ℝ ∞ (fun p => g p k l) O := (hg k l).mono inter_subset_left
    have hχ : ContDiffOn ℝ ∞ (fun p : P × X d => radialCutoff p.2 / 2) O :=
      ((radialCutoff_contDiff.comp contDiff_snd).div_const 2).contDiffOn
    have hLeft : ContDiffOn ℝ ∞ (fun p => (1-radialCutoff p.2/2)*g p i j) O :=
      (contDiffOn_const.sub hχ).mul (hG i j)
    have hRight : ContDiffOn ℝ ∞ (fun p => ((R p)ᵀ * g p * R p) i j) O := by
      simp only [Matrix.mul_apply,Matrix.transpose_apply]
      exact ContDiffOn.sum fun k _ => (ContDiffOn.sum fun l _ => (hR l i).mul (hG l k)).mul (hR k j)
    have hF : ContDiffOn ℝ ∞ f O := hLeft.add (hχ.mul hRight)
    exact (hF.contDiffAt (hO.mem_nhds hqO)).contDiffWithinAt

end CalderonPaper

namespace CalderonPaper
variable {n : ℕ}
local notation "Z" => X (n+1)
local notation "S" => sphere (0 : Z) 1

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

theorem radializedMetric_signedCollar_mixed_zero (g : MetricField (n+1)) (v : ↥S)
    (x : X n) (t : ℝ) (ht : t ≤ 1/4) (j : I n) :
    pullbackMetric (radializedMetric radialCutoff g) (signedSphericalCollar v)
      (signedLayerCoordinates (x,t)) 0 j.succ = 0 := by
  let w := angularPoint v x
  let z := polarCollar (angularPoint v) (x,t)
  let T := fderiv ℝ (angularPoint v) x (axis j)
  have hT : ⟪w,T⟫_ℝ = 0 := sphere_chart_fderiv_inner_eq_zero isOpen_univ
    (angularPoint v) (fun x _ => angularPoint_norm v x) (mem_univ x)
    ((angularPoint_contDiff v).differentiable (by simp) x) (axis j)
  have hz : z = (1-t) • w := rfl
  have hw : ‖w‖ = 1 := angularPoint_norm v x
  have hNorm : ‖z‖ = 1-t := by rw [hz,norm_smul,Real.norm_of_nonneg (by linarith : 0 ≤ 1-t),hw,mul_one]
  have hz₀ : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hNorm]; linarith)
  have hT' : ⟪z,T⟫_ℝ = 0 := by rw [hz,real_inner_smul_left,hT,mul_zero]
  have hZero := radializedMetric_mixed_zero (g := g) (radialCutoff_one (by rw [hNorm]; linarith)) hz₀ hT'
  rw [pullbackMetric_entry_metricPair,← signedLayerCoordinates_axis_normal,← signedLayerCoordinates_axis_tangent,
    signedSphericalCollar_derivative_apply,signedSphericalCollar_derivative_apply,
    signedLayerCoordinates.symm_apply_apply]
  have hA := (angularPoint_contDiff v).differentiable (by simp) x
  change metricPair (radializedMetric radialCutoff g) z
    (fderiv ℝ (polarCollar (angularPoint v)) (x,t) (0,1))
    (fderiv ℝ (polarCollar (angularPoint v)) (x,t) (axis j,0)) = 0
  rw [fderiv_polarCollar _ _ _ hA,fderiv_polarCollar _ _ _ hA]
  simp only [map_zero,smul_zero,add_zero,neg_zero,zero_smul,zero_add]
  rw [metricPair_smul_right,metricPair_smul_left]
  have hM : metricPair (radializedMetric radialCutoff g) z w T = 0 := by
    rw [hz,metricPair_smul_left] at hZero
    exact (mul_eq_zero.mp hZero).resolve_left (by linarith)
  rw [hM]
  ring

end CalderonPaper
