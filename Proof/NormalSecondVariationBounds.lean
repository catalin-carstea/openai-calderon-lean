import Proof.CoordinateSpraySecondBounds
import Proof.NormalSecondVariation
import Proof.UniformSecondConnection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def secondNormalVariationBudget (K C D E : ℝ) : ℝ :=
  (2*C+4*D*K+E*K^2)*Real.exp (1+2*C*K+D*K^2)^3

/-- The genuine second initial-velocity variation has a common bilinear bound,
    obtained from its inhomogeneous variational equation and Grönwall. -/
theorem NormalCoordinates.second_velocity_variation_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D E : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v u k : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖secondParameterVariation (normalGeodesicPhase expMap y) u k (v,t)‖ ≤
      secondNormalVariationBudget K C D E*‖u‖*‖k‖ := by
  let S : ℝ → X × X := fun s => secondParameterVariation (normalGeodesicPhase expMap y) u k (v,s)
  let A : ℝ := 1+2*C*K+D*K^2
  let Q : ℝ := 2*C+4*D*K+E*K^2
  let delta : ℝ := Q*(‖k‖*Real.exp A)*(‖u‖*Real.exp A)
  let L : ℝ → (X × X) →L[ℝ] X × X :=
    fun s => fderiv ℝ (coordinateGeodesicSpray g) (normalGeodesicPhase expMap y (v,s))
  let T : ℝ → X × X := fun s =>
    fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalGeodesicPhase expMap y (v,s))
      (firstParameterVariation (normalGeodesicPhase expMap y) k (v,s))
      (firstParameterVariation (normalGeodesicPhase expMap y) u (v,s))
  have hA : 1 ≤ A := by
    have hh : 0 ≤ 2*C*K+D*K^2 := by positivity
    dsimp only [A]
    linarith
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hDelta : 0 ≤ delta := by dsimp [delta]; positivity
  have hVar (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt S (L s (S s)+T s) s :=
    hN.hasDerivAt_second_phase_variation hΩ hg hK hy v u k hv hs
  have hGeom (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      (normalGeodesicPhase expMap y (v,s)).1 ∈ Ω ∧ ‖(normalGeodesicPhase expMap y (v,s)).2‖ ≤ K := by
    have hvd : v ∈ disk g y (R y) := interior_subset hv
    refine ⟨hN.path_image hy v hvd hs,?_⟩
    rw [hN.phase_eq hy v hvd hs]
    exact (hN.geodesic_speed_le hΩ hg hK hy v hvd hs).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hK.le)
  have hLinear (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖L s‖ ≤ A := by
    obtain ⟨hPos,hSpeed⟩ := hGeom s hs
    have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
    exact norm_fderiv_coordinateGeodesicSpray_le g _ hdΓ C D K hC hD hK.le
      (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeed
  have hFirst (w : X) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖firstParameterVariation (normalGeodesicPhase expMap y) w (v,s)‖ ≤ ‖w‖*Real.exp A := by
    have hb := hN.velocity_variation_bound hΩ hg hK hC hD hΓ0 hΓ1 hy v w hv hv1 hs
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_of_le_one_right hApos.le hs.2)) (norm_nonneg w))
  have hForcing (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖T s‖ ≤ delta := by
    obtain ⟨hPos,hSpeed⟩ := hGeom s hs
    have hb := hg.norm_second_coordinateGeodesicSpray_apply_le hΩ hK
      (normalGeodesicPhase expMap y (v,s))
      (firstParameterVariation (normalGeodesicPhase expMap y) u (v,s))
      (firstParameterVariation (normalGeodesicPhase expMap y) k (v,s)) hPos
      C D E K hC hD hE hK.le (hΓ0 _ hPos) (hΓ1 _ hPos) (hΓ2 _ hPos) hSpeed
    change ‖T s‖ ≤ _ at hb
    have hh : ‖T s‖ ≤ Q*(‖u‖*Real.exp A)*(‖k‖*Real.exp A) := hb.trans (by
      change Q*_ * _ ≤ _
      gcongr
      · exact hFirst u s hs
      · exact hFirst k s hs)
    exact hh.trans_eq (by dsimp only [delta]; ring)
  have hCont : ContinuousOn S (Icc (0:ℝ) 1) := fun s hs => (hVar s hs).continuousAt.continuousWithinAt
  have hRight (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt S (L s (S s)+T s) (Ici s) s :=
    (hVar s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt
  have hInitial : ‖S 0‖ ≤ 0 := by
    rw [show S 0 = 0 from hN.second_phase_variation_zero hy v u k hv,norm_zero]
  have hGrowth (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      ‖L s (S s)+T s‖ ≤ A*‖S s‖+delta := by
    exact (norm_add_le _ _).trans (add_le_add
      (((L s).le_opNorm (S s)).trans (mul_le_mul_of_nonneg_right
        (hLinear s ⟨hs.1,hs.2.le⟩) (norm_nonneg (S s))))
      (hForcing s ⟨hs.1,hs.2.le⟩))
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le hCont hRight hInitial hGrowth t ht
  simp only [gronwallBound_of_K_ne_0 hApos.ne',sub_zero,zero_mul,zero_add] at hb
  have hExp : Real.exp (A*t)-1 ≤ Real.exp A :=
    (sub_le_self _ zero_le_one).trans (Real.exp_le_exp.mpr (mul_le_of_le_one_right hApos.le ht.2))
  have hDiv : delta/A ≤ delta := div_le_self hDelta hA
  have hFinal : ‖S t‖ ≤ delta*Real.exp A := hb.trans
    ((mul_le_mul_of_nonneg_left hExp (div_nonneg hDelta hApos.le)).trans
      (mul_le_mul_of_nonneg_right hDiv (Real.exp_pos A).le))
  exact hFinal.trans_eq (by dsimp only [delta,Q,A,secondNormalVariationBudget]; ring)

def backgroundSecondNormalVariationBudget {m : ℕ} (hm : 3 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  secondNormalVariationBudget K (243*K*|M ⟨1,by omega⟩|)
    (backgroundConnectionDerivativeBudget (by omega) K M) (backgroundSecondConnectionBudget hm K M)

/-- Actual second normal variation, uniformly controlled by the frozen first
    three background jets, with no derivatives of the chosen frame in the budget. -/
theorem Background.normal_second_velocity_variation_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 3 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : X} (hy : y ∈ Y) (v u k : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖secondParameterVariation (normalGeodesicPhase expMap y) u k (v,t)‖ ≤
      backgroundSecondNormalVariationBudget hm K M*‖u‖*‖k‖ := by
  have hC : 0 ≤ 243*K*|M ⟨1,by omega⟩| := by positivity
  have hD : 0 ≤ backgroundConnectionDerivativeBudget (by omega) K M := by
    unfold backgroundConnectionDerivativeBudget
    positivity
  have hE : 0 ≤ backgroundSecondConnectionBudget hm K M := by
    unfold backgroundSecondConnectionBudget secondConnectionBudget
    positivity
  exact hN.second_velocity_variation_bound hΩ h.1 hK hC hD hE
    (fun x hx => h.connection_budget hK (by omega) hx)
    (fun x hx => h.connection_derivative_budget hΩ hK (by omega) hx)
    (fun x hx => h.connection_second_derivative_budget hΩ hK hm hx) hy v u k hv hv1 ht

end ShrinkingSpheres
