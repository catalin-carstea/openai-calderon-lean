module

public import Proof.CalderonN.NormalJointGeodesicPhase
public import Proof.CalderonN.CoordinateSprayBounds
import Mathlib.Analysis.ODE.Gronwall

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalJointVariationBounds.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Joint first variation, allowing an actual moving center. -/
@[expose] def normalJointVariation (expMap : (X dim) × (X dim) → (X dim)) (y v a b : (X dim)) (t : ℝ) : (X dim) × (X dim) :=
  fderiv ℝ (normalJointPhase expMap) ((y,v),t) ((a,b),0)

lemma NormalCoordinates.joint_variation_zero {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v a b : (X dim)) (hv : metricPair g y v v < (R y)^2) :
    normalJointVariation expMap y v a b 0 = (a,b) := by
  have hPhase := hN.contDiffAt_jointPhase hy v 0 (by simpa only [zero_smul] using zero_mem_disk g y (R y))
  have heq : (fun p : (X dim) × (X dim) => normalJointPhase expMap (p,0)) =ᶠ[𝓝 (y,v)] (fun p => p) := by
    filter_upwards [hN.eventually_joint_disk hY hΩ hg hy hR v hv] with p hp
    exact (hN.jointPhase_eq_phase hp.1 p.2 0 (by simpa only [zero_smul] using zero_mem_disk g p.1 (R p.1))).trans
      (hN.phase_zero hp.1 p.2 hp.2)
  change fderiv ℝ (normalJointPhase expMap) ((y,v),0) ((a,b),0) = (a,b)
  rw [← fderiv_base_slice_of_contDiffAt (normalJointPhase expMap) (y,v) (a,b) 0 hPhase,heq.fderiv_eq]
  exact congrArg (fun L : ((X dim) × (X dim)) →L[ℝ] (X dim) × (X dim) => L (a,b)) (hasFDerivAt_id (y,v)).fderiv

/-- A uniform first-variation estimate for the actual admitted normal-coordinate map,
    derived by Grönwall from the actual variational equation and connection budgets. -/
theorem NormalCoordinates.joint_variation_bound {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v a b : (X dim)) (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖normalJointVariation expMap y v a b t‖ ≤ ‖((a,b):(X dim) × (X dim))‖*Real.exp ((1+2*C*K+D*K^2)*t) := by
  let J : ℝ → (X dim) × (X dim) := normalJointVariation expMap y v a b
  let A : ℝ := 1+2*C*K+D*K^2
  let L : ℝ → ((X dim) × (X dim)) →L[ℝ] (X dim) × (X dim) :=
    fun s => fderiv ℝ (coordinateGeodesicSpray g) (normalJointPhase expMap ((y,v),s))
  have hVar (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt J (L s (J s)) s :=
    hN.hasDerivAt_joint_variation hY hΩ hg hK hy hR v a b hv hs
  have hL (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖L s‖ ≤ A := by
    have hvd : v ∈ disk g y (R y) := hv.le
    have hPos : (normalJointPhase expMap ((y,v),s)).1 ∈ Ω := hN.path_image hy v hvd hs
    have hSpeed : ‖(normalJointPhase expMap ((y,v),s)).2‖ ≤ K := by
      rw [hN.jointPhase_eq_phase hy v s (smul_mem_disk_of_mem g y v (R y) s hvd hs),hN.phase_eq hy v hvd hs]
      exact (hN.geodesic_speed_le hΩ hg hK hy v hvd hs).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hK.le)
    have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
    exact norm_fderiv_coordinateGeodesicSpray_le g _ hdΓ C D K hC hD hK.le (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeed
  have hCont : ContinuousOn J (Icc (0:ℝ) 1) :=
    fun s hs => (hVar s hs).continuousAt.continuousWithinAt
  have hRight (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : HasDerivWithinAt J (L s (J s)) (Ici s) s :=
    (hVar s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt
  have hInitial : ‖J 0‖ ≤ ‖((a,b):(X dim) × (X dim))‖ := by
    rw [show J 0 = (a,b) from hN.joint_variation_zero hY hΩ hg hy hR v a b hv]
  have hGrowth (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : ‖L s (J s)‖ ≤ A*‖J s‖+0 := by
    simpa only [add_zero] using (L s).le_opNorm (J s) |>.trans
      (mul_le_mul_of_nonneg_right (hL s ⟨hs.1,hs.2.le⟩) (norm_nonneg (J s)))
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le hCont hRight hInitial hGrowth t ht
  simpa only [gronwallBound_ε0,sub_zero] using hb

end CalderonN
