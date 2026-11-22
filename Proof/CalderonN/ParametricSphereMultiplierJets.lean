module

public import Proof.CalderonN.ParametricBallRotationCoefficientJets
public import Proof.CalderonN.PhysicalChartAngularJetComposition

import Mathlib.Tactic

/-! Angular rotations and ordinary coordinate derivatives of scalar
multipliers preserve joint smoothness and consume one coefficient jet. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

@[expose] def parametricSphereRotation (i j : I dim) (f : P × X dim → ℝ)
    (q : P × X dim) : ℝ :=
  fderiv ℝ f q ((ContinuousLinearMap.inr ℝ P (X dim)) (ballRotationGeneratorL i j q.2))

theorem parametricSphereRotation_eq_slice (i j : I dim) {f : P × X dim → ℝ}
    {p : P} {z : X dim} (hf : ContDiffAt ℝ ∞ f (p,z)) :
    parametricSphereRotation i j f (p,z) = sphereRotationDerivative i j (fun w => f (p,w)) z := by
  have hD : fderiv ℝ (fun w => f (p,w)) z =
      (fderiv ℝ f (p,z)).comp (ContinuousLinearMap.inr ℝ P (X dim)) :=
    (hf.differentiableAt (by simp) |>.hasFDerivAt.comp z (hasFDerivAt_prodMk_right p z)).fderiv
  rw [sphereRotationDerivative,hD]
  rfl

theorem LocalSmoothJetBudget.directional_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {q : E} {N : ℕ} {C : ℝ}
    (h : LocalSmoothJetBudget f q (N+1) C) (L : E →L[ℝ] E)
    (hL : ‖L‖ ≤ 2) (hLz : ‖L q‖ ≤ 2) :
    LocalSmoothJetBudget (fun v => _root_.fderiv ℝ f v (L v)) q N ((2:ℝ)^N*2*C) := by
  let Ev : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ).flip
  have hJ : LocalSmoothJetBudget (⇑L) q N 2 := by
    refine ⟨L.contDiff.contDiffAt,?_⟩
    intro n hn
    cases n with
    | zero => rwa [norm_iteratedFDeriv_zero]
    | succ n =>
      have hn' : 1 ≤ n+1 := by omega
      have hL' := norm_iteratedFDeriv_affine_pos_le L 0 q (n+1) hn'
      simpa only [zero_add] using hL'.trans hL
  have hEv : ‖Ev‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    rw [one_mul]
    exact le_rfl
  have hB := h.fderiv.bilinear hJ Ev
  change LocalSmoothJetBudget (fun v => Ev (_root_.fderiv ℝ f v) (L v)) q N ((2:ℝ)^N*2*C)
  refine hB.enlarge ?_
  calc
    (2:ℝ)^N*‖Ev‖*C*2 ≤ (2:ℝ)^N*1*C*2 := by have := h.nonneg; gcongr
    _ = (2:ℝ)^N*2*C := by ring

theorem localSmoothJetBudget_parametricSphereRotation (i j : I dim)
    {f : P × X dim → ℝ} {q : P × X dim}
    (hz : ‖q.2‖ ≤ 1) {N : ℕ} {C : ℝ} (h : LocalSmoothJetBudget f q (N+1) C) :
    LocalSmoothJetBudget (parametricSphereRotation i j f) q N ((2:ℝ)^N*2*C) := by
  let R := ContinuousLinearMap.inr ℝ P (X dim)
  let J := ballRotationGeneratorL i j
  let L := (R.comp J).comp (ContinuousLinearMap.snd ℝ P (X dim))
  have hL : ‖L‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    change ‖R (J v.2)‖ ≤ 2*‖v‖
    rw [show ‖R (J v.2)‖ = ‖J v.2‖ from by simp [R]]
    exact (J.le_opNorm _).trans (mul_le_mul (norm_ballRotationGeneratorL_le _ _) (norm_snd_le _)
      (norm_nonneg _) (by norm_num))
  have hLz : ‖L q‖ ≤ 2 := by
    change ‖R (J q.2)‖ ≤ 2
    rw [show ‖R (J q.2)‖ = ‖J q.2‖ from by simp [R]]
    exact (J.le_opNorm _).trans
      ((mul_le_mul (norm_ballRotationGeneratorL_le _ _) hz (norm_nonneg _) (by norm_num)).trans_eq (mul_one _))
  exact h.directional_linear L hL hLz

theorem localSmoothJetBudget_sphereRotation (i j : I dim)
    {f : X dim → ℝ} {z : X dim} (hz : ‖z‖ ≤ 1)
    {N : ℕ} {C : ℝ} (h : LocalSmoothJetBudget f z (N+1) C) :
    LocalSmoothJetBudget (sphereRotationDerivative i j f) z N ((2:ℝ)^N*2*C) :=
  h.directional_linear (ballRotationGeneratorL i j) (norm_ballRotationGeneratorL_le _ _)
    (((ballRotationGeneratorL i j).le_opNorm z).trans
      ((mul_le_mul (norm_ballRotationGeneratorL_le _ _) hz (norm_nonneg _) (by norm_num)).trans_eq (mul_one _)))

theorem LocalSmoothJetBudget.base_axis {f : P × X dim → ℝ} {q : P × X dim}
    {N : ℕ} {C : ℝ} (h : LocalSmoothJetBudget f q (N+1) C) (a : P) (ha : ‖a‖ ≤ 1) :
    LocalSmoothJetBudget (fun v => _root_.fderiv ℝ f v (a,0)) q N C := by
  have hh := h.fderiv.linear_postcomp (ContinuousLinearMap.apply ℝ ℝ (a,(0:X dim)))
  have hE : ‖ContinuousLinearMap.apply ℝ ℝ (a,(0:X dim))‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro L
    rw [one_mul]
    change ‖L (a,0)‖ ≤ ‖L‖
    exact (L.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left ha (norm_nonneg L))
  exact hh.enlarge (by simpa using mul_le_mul_of_nonneg_right hE h.nonneg)

end CalderonN
