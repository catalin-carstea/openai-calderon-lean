module

public import Proof.CalderonN.AngularPoissonEquation

import Proof.CalderonN.AngularRadialWeight
import Mathlib.Tactic

/-! The nested angular commutator solves the differentiated Poisson
equation and has the corresponding differentiated conormal flux. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem eqOn_zero_angularBallCorrection_of_trace (i j : Fin dim) (u b f : SmoothData dim)
    (hu : EqOn u.1 f.1 (standardSphere dim))
    (hb : EqOn b.1 (sphereRotationDerivative i j f.1) (standardSphere dim)) :
    EqOn (angularBallCorrection i j u b).1 0 (standardSphere dim) := by
  intro z hz
  change sphereRotationDerivative i j u.1 z-b.1 z = 0
  exact sub_eq_zero.mpr ((EqOn.sphereRotationDerivative hu u.2 f.2 i j hz).trans (hb hz).symm)

theorem negativeBallDivergence_doubleAngularBallCorrection (i j k l : Fin dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (b b₁ b₂ b₁₂ : SmoothData dim)
    (hb : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1))
    (hb₁ : EqOn (negativeBallDivergence A b₁.1) 0 (ball (0 : X dim) 1))
    (hb₂ : EqOn (negativeBallDivergence A b₂.1) 0 (ball (0 : X dim) 1))
    (hb₁₂ : EqOn (negativeBallDivergence A b₁₂.1) 0 (ball (0 : X dim) 1)) :
    let w₁ := angularBallCorrection i j b b₁
    let w₂ := angularBallCorrection k l b b₂
    let w₁₂ := angularBallCorrection i j b₂ b₁₂
    let w := angularBallCorrection k l w₁ w₁₂
    let A₁ := ballRotationCoefficient i j A
    let A₂ := ballRotationCoefficient k l A
    let A₁₂ := ballRotationCoefficient k l A₁
    EqOn (negativeBallDivergence A w.1)
      (fun z => -negativeBallDivergence A₁₂ b.1 z-negativeBallDivergence A₁ w₂.1 z-
        negativeBallDivergence A₂ w₁.1 z) (ball (0 : X dim) 1) := by
  dsimp only
  let w₁ := angularBallCorrection i j b b₁
  let w₂ := angularBallCorrection k l b b₂
  let w₁₂ := angularBallCorrection i j b₂ b₁₂
  let w := angularBallCorrection k l w₁ w₁₂
  let A₁ := ballRotationCoefficient i j A
  let A₂ := ballRotationCoefficient k l A
  let A₁₂ := ballRotationCoefficient k l A₁
  let hA₁ := contDiff_ballRotationCoefficient i j hA
  intro z hz
  have hw₁ := negativeBallDivergence_angularBallCorrection i j hA b b₁ hb hb₁
  have hw₁₂ := negativeBallDivergence_angularBallCorrection i j hA b₂ b₁₂ hb₂ hb₁₂
  have hG : negativeBallDivergence A w₁.1 =ᶠ[𝓝 z] -negativeBallDivergence A₁ b.1 := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hw₁ hx
  have hRot : sphereRotationDerivative k l (negativeBallDivergence A w₁.1) z =
      -sphereRotationDerivative k l (negativeBallDivergence A₁ b.1) z := by
    rw [sphereRotationDerivative,hG.fderiv_eq,fderiv_neg,ContinuousLinearMap.neg_apply,
      sphereRotationDerivative]
  have h₁ := sphereRotationDerivative_negativeBallDivergence k l hA w₁ z
  have h₂ := sphereRotationDerivative_negativeBallDivergence k l hA₁ b z
  rw [h₁,h₂] at hRot
  let w' : SmoothData dim := ⟨sphereRotationDerivative k l w₁.1,contDiff_sphereRotationDerivative k l w₁.1 w₁.2⟩
  let b' : SmoothData dim := ⟨sphereRotationDerivative k l b.1,contDiff_sphereRotationDerivative k l b.1 b.2⟩
  change negativeBallDivergence A (w'.1-w₁₂.1) z =
      -negativeBallDivergence A₁₂ b.1 z-negativeBallDivergence A₁ (b'.1-b₂.1) z-
        negativeBallDivergence A₂ w₁.1 z
  rw [negativeBallDivergence_sub_solution hA w' w₁₂,negativeBallDivergence_sub_solution hA₁ b' b₂]
  have hh : negativeBallDivergence A w₁₂.1 z = -negativeBallDivergence A₁ b₂.1 z := hw₁₂ hz
  linarith only [hRot,hh]

theorem smoothBallConormal_sub_solution (a : X dim → Mat dim) (u v : SmoothData dim) :
    smoothBallConormal a (u.1-v.1) = smoothBallConormal a u.1-smoothBallConormal a v.1 := by
  funext z
  unfold smoothBallConormal
  rw [smoothBallFlux_sub_solution a (u.2.differentiable (by simp)) (v.2.differentiable (by simp)),
    inner_sub_right,Pi.sub_apply]

theorem conormal_angularBallCorrection (i j : Fin dim) {a : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (u b : SmoothData dim) :
    sphereRotationDerivative i j (smoothBallConormal a u.1)-smoothBallConormal a b.1 =
      smoothBallConormal a (angularBallCorrection i j u b).1+
        smoothBallConormal (ballRotationCoefficient i j a) u.1 := by
  let U : SmoothData dim := ⟨sphereRotationDerivative i j u.1,contDiff_sphereRotationDerivative i j u.1 u.2⟩
  funext z
  have h := congrFun (smoothBallConormal_sub_solution a U b) z
  change smoothBallConormal a (angularBallCorrection i j u b).1 z =
    smoothBallConormal a U.1 z-smoothBallConormal a b.1 z at h
  rw [Pi.sub_apply,Pi.add_apply,sphereRotationDerivative_smoothBallConormal i j ha u z,
    inner_add_right,h]
  change smoothBallConormal a U.1 z+smoothBallConormal (ballRotationCoefficient i j a) u.1 z-
      smoothBallConormal a b.1 z = _
  ring

theorem conormal_doubleAngularBallCorrection (i j k l : Fin dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (b b₁ b₂ b₁₂ : SmoothData dim) :
    let w₁ := angularBallCorrection i j b b₁
    let w₂ := angularBallCorrection k l b b₂
    let w₁₂ := angularBallCorrection i j b₂ b₁₂
    let w := angularBallCorrection k l w₁ w₁₂
    let A₁ := ballRotationCoefficient i j A
    let A₂ := ballRotationCoefficient k l A
    let A₁₂ := ballRotationCoefficient k l A₁
    sphereRotationDerivative k l
      (sphereRotationDerivative i j (smoothBallConormal A b.1)-smoothBallConormal A b₁.1)-
      (sphereRotationDerivative i j (smoothBallConormal A b₂.1)-smoothBallConormal A b₁₂.1) =
      smoothBallConormal A w.1+smoothBallConormal A₂ w₁.1+
        smoothBallConormal A₁ w₂.1+smoothBallConormal A₁₂ b.1 := by
  dsimp only
  let w₁ := angularBallCorrection i j b b₁
  let w₁₂ := angularBallCorrection i j b₂ b₁₂
  let A₁ := ballRotationCoefficient i j A
  let hA₁ := contDiff_ballRotationCoefficient i j hA
  rw [conormal_angularBallCorrection i j hA b b₁,conormal_angularBallCorrection i j hA b₂ b₁₂]
  change sphereRotationDerivative k l (smoothBallConormal A w₁.1+smoothBallConormal A₁ b.1)-
    (smoothBallConormal A w₁₂.1+smoothBallConormal A₁ b₂.1) = _
  have hAdd : sphereRotationDerivative k l (smoothBallConormal A w₁.1+smoothBallConormal A₁ b.1) =
      sphereRotationDerivative k l (smoothBallConormal A w₁.1)+sphereRotationDerivative k l (smoothBallConormal A₁ b.1) := by
    funext z
    unfold sphereRotationDerivative
    rw [fderiv_add ((contDiff_smoothBallConormal hA w₁).differentiable (by simp) z)
      ((contDiff_smoothBallConormal hA₁ b).differentiable (by simp) z),Pi.add_apply,add_apply]
  rw [hAdd,show ∀ x y z w : X dim → ℝ, (x+y)-(z+w) = (x-z)+(y-w) by intros; abel,
    conormal_angularBallCorrection k l hA w₁ w₁₂,conormal_angularBallCorrection k l hA₁ b b₂]
  abel

end CalderonN
