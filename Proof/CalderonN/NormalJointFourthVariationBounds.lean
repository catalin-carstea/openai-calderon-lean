module

public import Proof.CalderonN.NormalJointFourthVariation
public import Proof.CalderonN.CoordinateSprayFourthBounds
public import Proof.CalderonN.FourthVariationGrowth
public import Proof.CalderonN.NormalJointThirdVariationBounds

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalJointFourthVariationBounds.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def fourthNormalVariationBudget (K C D E F G4 : ℝ) : ℝ :=
  let A := 1+2*C*K+D*K^2
  let B := 2*C+4*D*K+E*K^2
  let C3 := 6*D+6*E*K+F*K^2
  let C4 := G4*K^2+8*F*K+12*E
  fourthVariationForcingBudget B C3 C4 (Real.exp A)
    (secondNormalVariationBudget K C D E) (thirdNormalVariationBudget K C D E F)*Real.exp A

/-- The actual fourth joint normal variation has one uniform quadrilinear
    norm bound from connection jets through four and the true geodesic equation. -/
theorem NormalCoordinates.joint_fourth_variation_bound {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K C D E F G4 : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F) (hG4 : 0 ≤ G4)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    (hΓ3 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) x‖ ≤ F)
    (hΓ4 : ∀ x ∈ Ω,‖iteratedFDeriv ℝ 4 (connectionBilinear g) x‖ ≤ G4)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (hR : ContinuousOn R Y)
    {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (h k l m : (X dim) × (X dim))
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖fourthParameterVariation (normalJointPhase expMap) h k l m ((y,v),t)‖ ≤
      fourthNormalVariationBudget K C D E F G4*‖h‖*‖k‖*‖l‖*‖m‖ := by
  let S := fun s => fourthParameterVariation (normalJointPhase expMap) h k l m ((y,v),s)
  let P := fun s => normalJointPhase expMap ((y,v),s)
  let A := 1+2*C*K+D*K^2
  let B := 2*C+4*D*K+E*K^2
  let C3 := 6*D+6*E*K+F*K^2
  let C4 := G4*K^2+8*F*K+12*E
  let Z := secondNormalVariationBudget K C D E
  let W := thirdNormalVariationBudget K C D E F
  let delta := fourthVariationForcingBudget B C3 C4 (Real.exp A) Z W*‖h‖*‖k‖*‖l‖*‖m‖
  let Rhs := fun s => fourthParameterVariationRhs (normalJointPhase expMap) (coordinateGeodesicSpray g) h k l m ((y,v),s)
  have hA : 1 ≤ A := by dsimp [A];nlinarith [mul_nonneg hC hK.le,mul_nonneg hD (sq_nonneg K)]
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hC3 : 0 ≤ C3 := by dsimp [C3];positivity
  have hC4 : 0 ≤ C4 := by dsimp [C4];positivity
  have hZ : 0 ≤ Z := by dsimp [Z,secondNormalVariationBudget];positivity
  have hW : 0 ≤ W := by dsimp [W,thirdNormalVariationBudget,secondNormalVariationBudget];positivity
  have hDelta : 0 ≤ delta := by dsimp [delta,fourthVariationForcingBudget];positivity
  have hRy := hR.continuousAt (hY.mem_nhds hy)
  have hVar (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt S (Rhs s) s :=
    hN.hasDerivAt_joint_fourth_variation hY hΩ hg hK hR hy v h k l m hv hs
  have hGeom (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : (P s).1 ∈ Ω ∧ ‖(P s).2‖ ≤ K := by
    refine ⟨hN.path_image hy v hv.le hs,?_⟩
    dsimp only [P]
    rw [hN.jointPhase_eq_phase hy v s (smul_mem_disk_of_mem g y v (R y) s hv.le hs),hN.phase_eq hy v hv.le hs]
    exact (hN.geodesic_speed_le hΩ hg hK hy v hv.le hs).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hK.le)
  have hFirst (w : (X dim) × (X dim)) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖firstParameterVariation (normalJointPhase expMap) w ((y,v),s)‖ ≤ Real.exp A*‖w‖ := by
    have hb := hN.joint_variation_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hRy v w.1 w.2 hv hv1 hs
    have hh := hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_of_le_one_right hApos.le hs.2)) (norm_nonneg w))
    exact hh.trans_eq (mul_comm _ _)
  have hSecond (w z : (X dim) × (X dim)) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖secondParameterVariation (normalJointPhase expMap) w z ((y,v),s)‖ ≤ Z*‖w‖*‖z‖ :=
    hN.joint_second_variation_bound hY hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy hRy v w z hv hv1 hs
  have hThird (u w z : (X dim) × (X dim)) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖thirdParameterVariation (normalJointPhase expMap) u w z ((y,v),s)‖ ≤ W*‖u‖*‖w‖*‖z‖ :=
    hN.joint_third_variation_bound hY hΩ hg hK hC hD hE hF hΓ0 hΓ1 hΓ2 hΓ3 hR hy v u w z hv hv1 hs
  have hGrowth (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖Rhs s‖ ≤ A*‖S s‖+delta := by
    obtain ⟨hPos,hSpeed⟩ := hGeom s hs
    have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
    have hLinear : ‖fderiv ℝ (coordinateGeodesicSpray g) (P s)‖ ≤ A :=
      norm_fderiv_coordinateGeodesicSpray_le g _ hdΓ C D K hC hD hK.le (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeed
    have hTwo (u w : (X dim) × (X dim)) : ‖fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (P s) u w‖ ≤ B*‖u‖*‖w‖ := by
      have hh := hg.norm_second_coordinateGeodesicSpray_apply_le hΩ hK (P s) w u hPos C D E K
        hC hD hE hK.le (hΓ0 _ hPos) (hΓ1 _ hPos) (hΓ2 _ hPos) hSpeed
      exact hh.trans_eq (by ring)
    have hThree (u w z : (X dim) × (X dim)) :
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g))) (P s) u w z‖ ≤ C3*‖u‖*‖w‖*‖z‖ := by
      have hh := hg.norm_third_coordinateGeodesicSpray_apply_le hΩ hK (P s) z w u hPos D E F K
        hD hE hF hK.le (hΓ1 _ hPos) (hΓ2 _ hPos) (hΓ3 _ hPos) hSpeed
      exact hh.trans_eq (by ring)
    have hFourNorm : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)))) (P s)‖ ≤ C4 := by
      rw [← norm_iteratedFDeriv_four_eq_nested]
      exact hg.norm_fourth_coordinateGeodesicSpray_le hΩ hK (P s) hPos K E F G4 hK.le hE hF hG4
        (by rw [norm_iteratedFDeriv_two_eq_nested];exact hΓ2 _ hPos)
        (by rw [norm_iteratedFDeriv_three_eq_nested];exact hΓ3 _ hPos) (hΓ4 _ hPos) hSpeed
    let D4 := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)))) (P s)
    have hFour (u w z a : (X dim) × (X dim)) : ‖D4 u w z a‖ ≤ C4*‖u‖*‖w‖*‖z‖*‖a‖ := by
      calc
        _ ≤ ‖D4 u w z‖*‖a‖ := (D4 u w z).le_opNorm a
        _ ≤ (‖D4 u w‖*‖z‖)*‖a‖ := by gcongr;exact (D4 u w).le_opNorm z
        _ ≤ ((‖D4 u‖*‖w‖)*‖z‖)*‖a‖ := by gcongr;exact (D4 u).le_opNorm w
        _ ≤ (((‖D4‖*‖u‖)*‖w‖)*‖z‖)*‖a‖ := by gcongr;exact D4.le_opNorm u
        _ ≤ _ := by gcongr
    exact norm_fourthParameterVariationRhs_le (normalJointPhase expMap) (coordinateGeodesicSpray g)
      ((y,v),s) h k l m A B C3 C4 (Real.exp A) Z W hApos.le hB hC3 hC4 (Real.exp_pos _).le hZ hW
      hLinear hTwo hThree hFour (fun w => hFirst w s hs) (fun u w => hSecond u w s hs) (fun u w z => hThird u w z s hs)
  have hCont : ContinuousOn S (Icc (0:ℝ) 1) := fun s hs => (hVar s hs).continuousAt.continuousWithinAt
  have hRight (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : HasDerivWithinAt S (Rhs s) (Ici s) s :=
    (hVar s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt
  have hInitial : ‖S 0‖ ≤ 0 := by
    rw [show S 0 = 0 from hN.joint_fourth_variation_zero hY hΩ hg hR hy v h k l m hv,norm_zero]
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le hCont hRight hInitial
    (fun s hs => hGrowth s ⟨hs.1,hs.2.le⟩) t ht
  simp only [gronwallBound_of_K_ne_0 hApos.ne',sub_zero,zero_mul,zero_add] at hb
  have hExp : Real.exp (A*t)-1 ≤ Real.exp A :=
    (sub_le_self _ zero_le_one).trans (Real.exp_le_exp.mpr (mul_le_of_le_one_right hApos.le ht.2))
  have hDiv : delta/A ≤ delta := div_le_self hDelta hA
  have hFinal : ‖S t‖ ≤ delta*Real.exp A := hb.trans
    ((mul_le_mul_of_nonneg_left hExp (div_nonneg hDelta hApos.le)).trans
      (mul_le_mul_of_nonneg_right hDiv (Real.exp_pos A).le))
  exact hFinal.trans_eq (by dsimp only [delta,fourthNormalVariationBudget,A,B,C3,C4,Z,W];ring)

end CalderonN
