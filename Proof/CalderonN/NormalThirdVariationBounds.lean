module

public import Proof.CalderonN.NormalThirdVariation
public import Proof.CalderonN.NormalSecondVariationBounds
public import Proof.CalderonN.CoordinateSprayThirdBounds
public import Proof.CalderonN.UniformThirdConnection

import Mathlib.Analysis.ODE.Gronwall
import Proof.CalderonN.NormalJacobiBounds
import Mathlib.Tactic

/-! Adapted from the third variational equation in the checked Proposition 5.3 release. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

def thirdNormalVariationBudget (K C D E F : ℝ) : ℝ :=
  let A := 1+2*C*K+D*K^2
  let Q := 2*C+4*D*K+E*K^2
  let W := 6*D+6*E*K+F*K^2
  (3*Q*secondNormalVariationBudget K C D E*Real.exp A+W*(Real.exp A)^3)*Real.exp A

/-- Uniform third normal velocity variations from the actual inhomogeneous
    variational equation. No derivatives of a chosen frame enter this estimate. -/
theorem NormalCoordinates.third_velocity_variation_bound {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K C D E F : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    (hΓ3 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) x‖ ≤ F)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R)
    {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (h k l : (X dim))
    (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖thirdParameterVariation (normalGeodesicPhase expMap y) h k l (v,t)‖ ≤
      thirdNormalVariationBudget K C D E F*‖h‖*‖k‖*‖l‖ := by
  let S : ℝ → (X dim) × (X dim) := fun s => thirdParameterVariation (normalGeodesicPhase expMap y) h k l (v,s)
  let P : ℝ → (X dim) × (X dim) := fun s => normalGeodesicPhase expMap y (v,s)
  let J (w : (X dim)) (s : ℝ) := firstParameterVariation (normalGeodesicPhase expMap y) w (v,s)
  let B (w z : (X dim)) (s : ℝ) := secondParameterVariation (normalGeodesicPhase expMap y) w z (v,s)
  let A : ℝ := 1+2*C*K+D*K^2
  let Q : ℝ := 2*C+4*D*K+E*K^2
  let W : ℝ := 6*D+6*E*K+F*K^2
  let Z : ℝ := secondNormalVariationBudget K C D E
  let delta : ℝ := (3*Q*Z*Real.exp A+W*(Real.exp A)^3)*‖h‖*‖k‖*‖l‖
  let L : ℝ → ((X dim) × (X dim)) →L[ℝ] (X dim) × (X dim) := fun s => fderiv ℝ (coordinateGeodesicSpray g) (P s)
  let T : ℝ → (X dim) × (X dim) := fun s =>
    fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (P s) (J l s) (B h k s)+
    fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g))) (P s) (J l s) (J k s) (J h s)+
    fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (P s) (B k l s) (J h s)+
    fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (P s) (J k s) (B h l s)
  have hA : 1 ≤ A := by
    have hh : 0 ≤ 2*C*K+D*K^2 := by positivity
    dsimp only [A]
    linarith
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z,secondNormalVariationBudget]; positivity
  have hDelta : 0 ≤ delta := by dsimp [delta]; positivity
  have hVar (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt S (L s (S s)+T s) s := by
    have hh := hN.hasDerivAt_third_phase_variation hΩ hg hK hy v h k l hv hs
    simpa only [S,L,T,P,J,B,add_assoc] using hh
  have hGeom (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : (P s).1 ∈ Ω ∧ ‖(P s).2‖ ≤ K := by
    have hvd : v ∈ disk g y (R y) := interior_subset hv
    refine ⟨hN.path_image hy v hvd hs,?_⟩
    dsimp only [P]
    rw [hN.phase_eq hy v hvd hs]
    exact (hN.geodesic_speed_le hΩ hg hK hy v hvd hs).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hK.le)
  have hLinear (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖L s‖ ≤ A := by
    obtain ⟨hPos,hSpeed⟩ := hGeom s hs
    have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
    exact norm_fderiv_coordinateGeodesicSpray_le g _ hdΓ C D K hC hD hK.le
      (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeed
  have hFirst (w : (X dim)) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖J w s‖ ≤ ‖w‖*Real.exp A := by
    have hb := hN.velocity_variation_bound hΩ hg hK hC hD hΓ0 hΓ1 hy v w hv hv1 hs
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_of_le_one_right hApos.le hs.2)) (norm_nonneg w))
  have hSecond (w z : (X dim)) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖B w z s‖ ≤ Z*‖w‖*‖z‖ :=
    hN.second_velocity_variation_bound hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy v w z hv hv1 hs
  have hForcing (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖T s‖ ≤ delta := by
    obtain ⟨hPos,hSpeed⟩ := hGeom s hs
    have hTwo (u w : (X dim) × (X dim)) :
        ‖fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (P s) w u‖ ≤ Q*‖u‖*‖w‖ :=
      hg.norm_second_coordinateGeodesicSpray_apply_le hΩ hK (P s) u w hPos
        C D E K hC hD hE hK.le (hΓ0 _ hPos) (hΓ1 _ hPos) (hΓ2 _ hPos) hSpeed
    have h1 : ‖fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (P s) (J l s) (B h k s)‖ ≤
        Q*Z*Real.exp A*‖h‖*‖k‖*‖l‖ := by
      have hh := (hTwo (B h k s) (J l s)).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left (hSecond h k s hs) hQ)
          (hFirst l s hs) (norm_nonneg _) (by positivity))
      exact hh.trans_eq (by ring)
    have h2 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g))) (P s) (J l s) (J k s) (J h s)‖ ≤
        W*(Real.exp A)^3*‖h‖*‖k‖*‖l‖ := by
      have hb := hg.norm_third_coordinateGeodesicSpray_apply_le hΩ hK (P s)
        (J h s) (J k s) (J l s) hPos D E F K hD hE hF hK.le
          (hΓ1 _ hPos) (hΓ2 _ hPos) (hΓ3 _ hPos) hSpeed
      have hh : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g))) (P s) (J l s) (J k s) (J h s)‖ ≤
          W*(‖h‖*Real.exp A)*(‖k‖*Real.exp A)*(‖l‖*Real.exp A) := hb.trans (by
        change W*_ * _ * _ ≤ _
        gcongr
        · exact hFirst h s hs
        · exact hFirst k s hs
        · exact hFirst l s hs)
      exact hh.trans_eq (by ring)
    have h3 : ‖fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (P s) (B k l s) (J h s)‖ ≤
        Q*Z*Real.exp A*‖h‖*‖k‖*‖l‖ := by
      have hh := (hTwo (J h s) (B k l s)).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left (hFirst h s hs) hQ)
          (hSecond k l s hs) (norm_nonneg _) (by positivity))
      exact hh.trans_eq (by ring)
    have h4 : ‖fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (P s) (J k s) (B h l s)‖ ≤
        Q*Z*Real.exp A*‖h‖*‖k‖*‖l‖ := by
      have hh := (hTwo (B h l s) (J k s)).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left (hSecond h l s hs) hQ)
          (hFirst k s hs) (norm_nonneg _) (by positivity))
      exact hh.trans_eq (by ring)
    dsimp only [T]
    refine ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)).trans ?_
    dsimp only [delta]
    linarith only [h1,h2,h3,h4]
  have hCont : ContinuousOn S (Icc (0:ℝ) 1) := fun s hs => (hVar s hs).continuousAt.continuousWithinAt
  have hRight (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt S (L s (S s)+T s) (Ici s) s :=
    (hVar s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt
  have hInitial : ‖S 0‖ ≤ 0 := by
    rw [show S 0 = 0 from hN.third_phase_variation_zero hy v h k l hv,norm_zero]
  have hGrowth (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : ‖L s (S s)+T s‖ ≤ A*‖S s‖+delta := by
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
  exact hFinal.trans_eq (by dsimp only [delta,Q,W,Z,A,thirdNormalVariationBudget]; ring)

end CalderonN
