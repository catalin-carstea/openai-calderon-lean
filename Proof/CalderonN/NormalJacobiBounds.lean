module

public import Proof.CalderonN.NormalGeodesicVariation
public import Proof.CalderonN.NormalGeodesicBounds
public import Proof.CalderonN.NormalVerticalJacobian
public import Proof.CalderonN.CoordinateSprayBounds
import Mathlib.Analysis.ODE.Gronwall

/-! Port of the named module in the checked Proposition 5.3 release.
All variations refer to the admitted initial-velocity parameter of the same normal map. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- A uniform first-variation estimate for the actual admitted normal-coordinate map,
    derived by Grönwall from the actual variational equation and connection budgets. -/
theorem NormalCoordinates.velocity_variation_bound {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u : (X dim)) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖normalVelocityVariation expMap y v u t‖ ≤ ‖u‖*Real.exp ((1+2*C*K+D*K^2)*t) := by
  let J : ℝ → (X dim) × (X dim) := normalVelocityVariation expMap y v u
  let A : ℝ := 1+2*C*K+D*K^2
  let L : ℝ → ((X dim) × (X dim)) →L[ℝ] (X dim) × (X dim) :=
    fun s => fderiv ℝ (coordinateGeodesicSpray g) (normalGeodesicPhase expMap y (v,s))
  have hVar (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt J (L s (J s)) s :=
    hN.hasDerivAt_phase_variation hΩ hg hK hy v u hv hs
  have hL (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖L s‖ ≤ A := by
    have hvd : v ∈ disk g y (R y) := interior_subset hv
    have hPos : (normalGeodesicPhase expMap y (v,s)).1 ∈ Ω := hN.path_image hy v hvd hs
    have hSpeed : ‖(normalGeodesicPhase expMap y (v,s)).2‖ ≤ K := by
      rw [hN.phase_eq hy v hvd hs]
      exact (hN.geodesic_speed_le hΩ hg hK hy v hvd hs).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hK.le)
    have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
    exact norm_fderiv_coordinateGeodesicSpray_le g _ hdΓ C D K hC hD hK.le (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeed
  have hCont : ContinuousOn J (Icc (0:ℝ) 1) :=
    fun s hs => (hVar s hs).continuousAt.continuousWithinAt
  have hRight (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : HasDerivWithinAt J (L s (J s)) (Ici s) s :=
    (hVar s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt
  have hInitial : ‖J 0‖ ≤ ‖u‖ := by
    change ‖fderiv ℝ (normalGeodesicPhase expMap y) (v,0) (u,0)‖ ≤ ‖u‖
    rw [hN.phase_variation_zero hy v u hv]
    simp
  have hGrowth (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : ‖L s (J s)‖ ≤ A*‖J s‖+0 := by
    simpa only [add_zero] using (L s).le_opNorm (J s) |>.trans
      (mul_le_mul_of_nonneg_right (hL s ⟨hs.1,hs.2.le⟩) (norm_nonneg (J s)))
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le hCont hRight hInitial hGrowth t ht
  simpa only [gronwallBound_ε0,sub_zero] using hb

end CalderonN
