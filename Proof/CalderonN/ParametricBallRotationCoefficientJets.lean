module

public import Proof.CalderonN.ActualRelativeWeakEnergyJets
public import Proof.CalderonN.BallRotationFlux

import Proof.CalderonN.DoubleAngularCoefficientJets
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! Angular differentiation of the physical coefficient family consumes
a spatial jet while preserving its relative-radius factors. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

@[expose] def parametricBallRotationCoefficient (i j : I dim) (a : P × X dim → Mat dim)
    (q : P × X dim) : Mat dim :=
  ballRotationCoefficient i j (fun z => a (q.1,z)) q.2

private def rotationCoefficientCommL (i j : I dim) : Mat dim →L[ℝ] Mat dim := by
  let B := coordinateMatrix (ballRotationGeneratorL i j)
  exact (⟨⟨fun A => A*B-B*A,fun A C => by rw [add_mul,mul_add]; abel⟩,
    fun c A => by
      change (c • A)*B-B*(c • A) = c • (A*B-B*A)
      rw [smul_mul_assoc,mul_smul_comm,smul_sub]⟩ : Mat dim →ₗ[ℝ] Mat dim).toContinuousLinearMap

omit [Nontrivial (Fin dim)] in
private theorem rotationCoefficient_eq_jet (i j : I dim) {a : P × X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (q : P × X dim) :
    let J := ballRotationGeneratorL i j
    let R : X dim →L[ℝ] P × X dim := ContinuousLinearMap.inr ℝ P (X dim)
    parametricBallRotationCoefficient i j a q = fderiv ℝ a q (R (J q.2))+rotationCoefficientCommL i j (a q) := by
  dsimp only
  have hD : fderiv ℝ (fun z => a (q.1,z)) q.2 =
      (fderiv ℝ a q).comp (ContinuousLinearMap.inr ℝ P (X dim)) :=
    ((ha.differentiable (by simp) q).hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)).fderiv
  rw [parametricBallRotationCoefficient,ballRotationCoefficient,hD,ContinuousLinearMap.comp_apply]
  change _ = _ + (a q*coordinateMatrix (ballRotationGeneratorL i j)-
    coordinateMatrix (ballRotationGeneratorL i j)*a q)
  abel

theorem contDiff_parametricBallRotationCoefficient (i j : I dim) {a : P × X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (parametricBallRotationCoefficient i j a) := by
  rw [show parametricBallRotationCoefficient i j a = (fun q =>
    fderiv ℝ a q ((ContinuousLinearMap.inr ℝ P (X dim)) (ballRotationGeneratorL i j q.2))+
      rotationCoefficientCommL i j (a q)) from funext (rotationCoefficient_eq_jet i j ha)]
  exact (((ha.fderiv_right (m:=∞) (by simp)).clm_apply
    ((ContinuousLinearMap.inr ℝ P (X dim)).contDiff.comp
      ((ballRotationGeneratorL i j).contDiff.comp contDiff_snd))).add
        ((rotationCoefficientCommL i j).contDiff.comp ha))

omit [Nontrivial (Fin dim)] in
theorem parametricBallRotationCoefficient_support (i j : I dim) {a : P × X dim → Mat dim}
    {J : Set (X dim)} (hJ : IsClosed J) (hSupp : ∀ p z,z ∉ J → a (p,z) = 0) (p : P)
    {z : X dim} (hz : z ∉ J) :
    parametricBallRotationCoefficient i j a (p,z) = 0 := by
  have hE : (fun z => a (p,z)) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [hJ.isOpen_compl.mem_nhds hz] with w hw using hSupp p w hw
  simp only [parametricBallRotationCoefficient,ballRotationCoefficient,hE.fderiv_eq,hSupp p z hz,
    fderiv_fun_const,Pi.zero_apply,zero_apply,zero_mul,mul_zero,add_zero,sub_zero]

theorem uniform_parametricBallRotationCoefficient_jet_budget (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : I dim) (a : P × X dim → Mat dim), ContDiff ℝ ∞ a →
      ∀ p : P,∀ z ∈ closedBall (0:X dim) 1,∀ B : ℝ,
        LocalSmoothJetBudget a (p,z) (N+1) B →
        LocalSmoothJetBudget (parametricBallRotationCoefficient i j a) (p,z) N (C*B) := by
  let R := ContinuousLinearMap.inr ℝ P (X dim)
  let Ev : ((P × X dim) →L[ℝ] Mat dim) →L[ℝ] (P × X dim) →L[ℝ] Mat dim :=
    (ContinuousLinearMap.apply ℝ (Mat dim)).flip
  let S := ∑ i : I dim,∑ j : I dim,‖rotationCoefficientCommL i j‖
  let C := (2:ℝ)^N*‖Ev‖*2+S
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro i j a ha p z hz B hB
  let J := ballRotationGeneratorL i j
  let L := (R.comp J).comp (ContinuousLinearMap.snd ℝ P (X dim))
  have hL : ‖L‖ ≤ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro q
    change ‖R (J q.2)‖ ≤ 2*‖q‖
    rw [show ‖R (J q.2)‖ = ‖J q.2‖ from by simp [R]]
    exact (J.le_opNorm _).trans (mul_le_mul (norm_ballRotationGeneratorL_le _ _) (norm_snd_le _)
      (norm_nonneg _) (by norm_num))
  have hLz : ‖L (p,z)‖ ≤ 2 := by
    change ‖R (J z)‖ ≤ 2
    rw [show ‖R (J z)‖ = ‖J z‖ from by simp [R]]
    exact (J.le_opNorm _).trans ((mul_le_mul (norm_ballRotationGeneratorL_le _ _)
      (mem_closedBall_zero_iff.mp hz) (norm_nonneg _) (by norm_num)).trans_eq (mul_one _))
  have hJ : LocalSmoothJetBudget (⇑L) (p,z) N 2 := by
    refine ⟨L.contDiff.contDiffAt,?_⟩
    intro n hn
    cases n with
    | zero => rwa [norm_iteratedFDeriv_zero]
    | succ n =>
      rw [← norm_iteratedFDeriv_fderiv,
        show fderiv ℝ (⇑L) = fun _ => L from funext fun _ => L.fderiv]
      cases n with
      | zero => rwa [norm_iteratedFDeriv_zero]
      | succ n => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; norm_num
  have hA : ‖rotationCoefficientCommL i j‖ ≤ S :=
    (Finset.single_le_sum (fun k _ => norm_nonneg (rotationCoefficientCommL i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg (rotationCoefficientCommL k l))
        (Finset.mem_univ i))
  have h := (hB.fderiv.bilinear hJ Ev).add
    ((((hB.mono_order (Nat.le_succ _)).linear_postcomp (rotationCoefficientCommL i j)).enlarge
      (mul_le_mul_of_nonneg_right hA hB.nonneg)))
  have hEq : parametricBallRotationCoefficient i j a =
      (fun q => Ev (fderiv ℝ a q) (L q)+(rotationCoefficientCommL i j ∘ a) q) :=
    funext (rotationCoefficient_eq_jet i j ha)
  rw [hEq]
  exact h.enlarge (by dsimp only [C]; ring_nf; rfl)

end CalderonN
