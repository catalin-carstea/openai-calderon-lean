module

public import Proof.CalderonN.FixedBallSmoothFlux

import Mathlib.Tactic

public section

noncomputable section

open Set MeasureTheory Metric CalderonN CalderonN.BallDirichlet
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]

private theorem coordinateFluxDivergence_smul_local {u : X n → ℝ} {F : X n → X n}
    (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) (x : X n) :
    coordinateFluxDivergence (fun z => u z • F z) x =
      u x * coordinateFluxDivergence F x + ∑ i, coordDeriv i u x * F x i := by
  have hP (i : I n) : coordDeriv i (fun z => (u z • F z) i) x =
      u x * coordDeriv i (fun z => F z i) x + coordDeriv i u x * F x i := by
    have hf : DifferentiableAt ℝ (fun z => F z i) x :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF).differentiable (by simp) x
    change coordDeriv i (fun z => u z * F z i) x = _
    simp only [coordDeriv, fderiv_fun_mul (hu.differentiable (by simp) x) hf,
      add_apply, smul_apply, smul_eq_mul]
    ring
  unfold coordinateFluxDivergence
  simp_rw [hP, Finset.sum_add_distrib, Finset.mul_sum]

private theorem coordinateFluxDivergence_sub_local {F G : X n → X n}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (x : X n) :
    coordinateFluxDivergence (fun z => F z - G z) x =
      coordinateFluxDivergence F x - coordinateFluxDivergence G x := by
  have hEq (i : I n) : coordDeriv i (fun z => (F z - G z) i) x =
      coordDeriv i (fun z => F z i) x - coordDeriv i (fun z => G z i) x := by
    have hf : DifferentiableAt ℝ (fun z => F z i) x :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF).differentiable (by simp) x
    have hg : DifferentiableAt ℝ (fun z => G z i) x :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hG).differentiable (by simp) x
    change coordDeriv i (fun z => F z i - G z i) x = _
    rw [coordDeriv, fderiv_fun_sub hf hg]
    rfl
  unfold coordinateFluxDivergence
  simp_rw [hEq, Finset.sum_sub_distrib]

/-- The second Green identity with the Euclidean volume and the literal
normalized-ball flux, for arbitrary smooth divergence-form fields. -/
theorem integral_sub_ballGreenFlux
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a)
    (hSym : ∀ x ∈ ball (0 : X n) 1, ∀ i j, a x i j = a x j i) (u v : SmoothData n) :
    (∫ x in ball (0 : X n) 1, v.1 x * negativeBallDivergence a u.1 x -
      u.1 x * negativeBallDivergence a v.1 x) =
      unitSphereFlux (fun x => u.1 x • smoothBallFlux a v.1 x - v.1 x • smoothBallFlux a u.1 x) := by
  let F := smoothBallFlux a v.1
  let G := smoothBallFlux a u.1
  have hF : ContDiff ℝ ∞ F := contDiff_smoothBallFlux ha v
  have hG : ContDiff ℝ ∞ G := contDiff_smoothBallFlux ha u
  let W : X n → X n := fun x => u.1 x • F x - v.1 x • G x
  have hW : ContDiff ℝ ∞ W := (u.2.smul hF).sub (v.2.smul hG)
  change _ = unitSphereFlux W
  rw [← integral_unitBall_coordinateFluxDivergence W hW]
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro x hx
  change _ = coordinateFluxDivergence (fun x => u.1 x • F x - v.1 x • G x) x
  have hDivF : coordinateFluxDivergence F x = -negativeBallDivergence a v.1 x :=
    coordinateFluxDivergence_smoothBallFlux a v.1 x
  have hDivG : coordinateFluxDivergence G x = -negativeBallDivergence a u.1 x :=
    coordinateFluxDivergence_smoothBallFlux a u.1 x
  rw [coordinateFluxDivergence_sub_local (F := fun z => u.1 z • F z) (G := fun z => v.1 z • G z)
    (u.2.smul hF) (v.2.smul hG), coordinateFluxDivergence_smul_local u.2 hF,
    coordinateFluxDivergence_smul_local v.2 hG,hDivF,hDivG]
  have hCross : (∑ i, coordDeriv i u.1 x * F x i) = ∑ i, coordDeriv i v.1 x * G x i := by
    simp only [F,G,smoothBallFlux_apply,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hSym x hx j i]
    ring
  rw [hCross]
  ring

end CalderonPaper.LowerGreen

end
