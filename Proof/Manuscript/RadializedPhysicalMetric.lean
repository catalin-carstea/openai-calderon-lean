module


public import Proof.Manuscript.NormalizedConformalGauss
public import Proof.Manuscript.PhysicalRadialAdjoint

public import Proof.Manuscript.MovingTrace.RadializedCollar
public import Proof.Manuscript.MovingTrace.CompactNormalMetricFamily
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section


noncomputable section

open Set Metric CalderonN
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {dim : ℕ} [NeZero dim]

/-- The signed-collar extension used by the boundary parametrix changes
neither the actual normalized metric nor the Poisson equation on the
closed ball. -/
theorem normalizedBallMetric_eqOn_radialized_symmetrized
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g q : ℝ → MetricField dim} {K : ℝ}
    {m : ℕ} {B : Fin (m+1) → ℝ} {e : ℝ → Frame dim} {E : ℝ → X dim × X dim → X dim}
    (lam : ℝ) (hB : Background Ω K B (γ lam) (g lam) (q lam) (e lam))
    (hK : 0 < K) (hg : SmoothMetric univ (g lam)) (hE : ContDiff ℝ ∞ (E lam))
    {R : X dim → ℝ} (hN : NormalCoordinates Y Ω (γ lam) (E lam) R)
    {y : X dim} (hy : y ∈ Y) {s : ℝ} (hs : s ∈ Ico 0 (R y)) :
    EqOn (normalizedBallMetric (g lam) (E lam) (e lam) y s)
      (radializedMetric radialCutoff (fun z => symmetrizedNormalMetric g E e ((lam,y,s),z)))
      (closedBall (0 : X dim) 1) := by
  let raw := normalizedBallMetric (g lam) (E lam) (e lam) y s
  let G (z : X dim) := symmetrizedNormalMetric g E e ((lam,y,s),z)
  have hSym (z : X dim) : (raw z).IsSymm := normalizedBallMetric_isSymm_of_smoothMetric hg _ _ _ _ _
  have hG : G = raw := funext fun z => symmetrizedNormalMetric_eq (hSym z)
  change EqOn raw (radializedMetric radialCutoff G) _
  rw [hG]
  intro z hz
  by_cases hz₀ : z = 0
  · exact (radializedMetric_eq_at_zeroCutoff
      (radialCutoff_zero (by simp [hz₀]))).symm
  · obtain ⟨a,_,ha⟩ := normalizedBallMetric_radial_eigenline_on_closedBall hΩ hB hK hE hN hy hs hz
    exact (radializedMetric_eq_of_gauss hz₀ (hSym z) a ha).symm

/-- Radializing the full metric near the fixed sphere makes its Euclidean
radial line an exact eigenline for arbitrary parameter values. -/
theorem radializedMetric_radial_eigenline_on_sphere
    (g : MetricField dim) {z : X dim} (hz : z ∈ standardSphere dim) (u : X dim) :
    let M := radializedMetric radialCutoff g
    metricPair M z z u = metricPair M z z z * ⟪z,u⟫_ℝ := by
  dsimp only
  let M := radializedMetric radialCutoff g
  let a := ⟪z,u⟫_ℝ
  have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have hz₀ : z ≠ 0 := norm_ne_zero_iff.mp (hn.trans_ne one_ne_zero)
  have hCut : radialCutoff z = 1 := radialCutoff_one (by rw [hn]; norm_num)
  have hTan : ⟪z,u-a • z⟫_ℝ = 0 := by
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
    exact sub_self _
  have hMixed : metricPair M z z (u-a • z) = 0 := radializedMetric_mixed_zero hCut hz₀ hTan
  have hSub : metricPair M z z (u-a • z) = metricPair M z z u - metricPair M z z (a • z) := by
    simp only [metricPair,PiLp.sub_apply,mul_sub,Finset.sum_sub_distrib]
  rw [hSub,metricPair_smul_right] at hMixed
  exact (sub_eq_zero.mp hMixed).trans (mul_comm _ _)

/-- The Gauss radial form holds throughout the positive radialized tube,
including auxiliary parameters outside the physical family. -/
theorem ballConormalVector_radializedMetric_on_sphere
    (g : MetricField dim) {c : ℝ} (hc : c ≠ 0) {z : X dim} (hz : z ∈ standardSphere dim)
    (hPos : (radializedMetric radialCutoff g z).PosDef) :
    let M := radializedMetric radialCutoff g
    ballConormalVector M z = (c * sphereGaussWeight M c z) • z := by
  dsimp only
  have hz₀ : z ≠ 0 := norm_ne_zero_iff.mp ((mem_sphere_zero_iff_norm.mp hz).trans_ne one_ne_zero)
  exact ballConormalVector_eq_sphereGaussWeight_smul hc hz hPos
    (metricPair_pos_of_posDef hPos hz₀).ne' (radializedMetric_radial_eigenline_on_sphere g hz)

end CalderonPaper
