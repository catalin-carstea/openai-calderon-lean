module

public import Proof.CalderonN.DoubleAngularPoissonEquation

import Mathlib.Tactic

/-! Subtracting the flat double variation makes every forcing term
quadratic in the coefficient or in its response. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem negativeBallDivergence_harmonic_lift_difference {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (b u : SmoothData dim)
    (hb : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1))
    (hu : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) u.1) 0 (ball (0 : X dim) 1)) :
    EqOn (negativeBallDivergence A (b.1-u.1))
      (-negativeBallDivergence (A- (fun _ => (1 : Mat dim))) u.1) (ball (0 : X dim) 1) := by
  intro z hz
  change negativeBallDivergence A (b.1-u.1) z =
    -negativeBallDivergence (A-(fun _ => (1 : Mat dim))) u.1 z
  rw [negativeBallDivergence_sub_solution hA b u,negativeBallDivergence_sub_coefficient hA contDiff_const u z,
    hb hz,hu hz,Pi.zero_apply,zero_sub,sub_zero]

theorem negativeBallDivergence_doubleAngularTaylorRemainder (i j k l : Fin dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (b b₁ b₂ b₁₂ u q : SmoothData dim)
    (hb : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1))
    (hb₁ : EqOn (negativeBallDivergence A b₁.1) 0 (ball (0 : X dim) 1))
    (hb₂ : EqOn (negativeBallDivergence A b₂.1) 0 (ball (0 : X dim) 1))
    (hb₁₂ : EqOn (negativeBallDivergence A b₁₂.1) 0 (ball (0 : X dim) 1))
    (ell₂ : X dim →L[ℝ] ℝ)
    (hq : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) q.1)
      (-negativeBallDivergence (fun z => ell₂ z • (1 : Mat dim)) u.1) (ball (0 : X dim) 1)) (r : ℝ) :
    let w₁ := angularBallCorrection i j b b₁
    let w₂ := angularBallCorrection k l b b₂
    let w₁₂ := angularBallCorrection i j b₂ b₁₂
    let w := angularBallCorrection k l w₁ w₁₂
    let A₁ := ballRotationCoefficient i j A
    let A₂ := ballRotationCoefficient k l A
    let A₁₂ := ballRotationCoefficient k l A₁
    let R₁₂ := A₁₂-r • (fun z => ell₂ z • (1 : Mat dim))
    let D := A- (fun _ => (1 : Mat dim))
    EqOn (negativeBallDivergence A (w.1-r • q.1))
      (fun z => -negativeBallDivergence A₁₂ (b.1-u.1) z-negativeBallDivergence R₁₂ u.1 z-
        negativeBallDivergence A₁ w₂.1 z-negativeBallDivergence A₂ w₁.1 z-
        negativeBallDivergence (r • D) q.1 z) (ball (0 : X dim) 1) := by
  dsimp only
  let A₁ := ballRotationCoefficient i j A
  let A₂ := ballRotationCoefficient k l A
  let A₁₂ := ballRotationCoefficient k l A₁
  let L := fun z => ell₂ z • (1 : Mat dim)
  let D := A- (fun _ => (1 : Mat dim))
  let w₁ := angularBallCorrection i j b b₁
  let w₂ := angularBallCorrection k l b b₂
  let w₁₂ := angularBallCorrection i j b₂ b₁₂
  let w := angularBallCorrection k l w₁ w₁₂
  let rq : SmoothData dim := ⟨r • q.1,q.2.const_smul r⟩
  have hA₁ := contDiff_ballRotationCoefficient i j hA
  have hA₁₂ := contDiff_ballRotationCoefficient k l hA₁
  have hL : ContDiff ℝ ∞ L := ell₂.contDiff.smul contDiff_const
  have hD : ContDiff ℝ ∞ D := hA.sub contDiff_const
  intro z hz
  have hw : negativeBallDivergence A w.1 z =
      -negativeBallDivergence A₁₂ b.1 z-negativeBallDivergence A₁ w₂.1 z-
        negativeBallDivergence A₂ w₁.1 z :=
    negativeBallDivergence_doubleAngularBallCorrection i j k l hA b b₁ b₂ b₁₂ hb hb₁ hb₂ hb₁₂ hz
  have hq₀ : negativeBallDivergence (fun _ => (1 : Mat dim)) q.1 z = -negativeBallDivergence L u.1 z := hq hz
  change negativeBallDivergence A (w.1-rq.1) z =
      -negativeBallDivergence A₁₂ (b.1-u.1) z-negativeBallDivergence (A₁₂-r • L) u.1 z-
        negativeBallDivergence A₁ w₂.1 z-negativeBallDivergence A₂ w₁.1 z-
        negativeBallDivergence (r • D) q.1 z
  change negativeBallDivergence A (w.1-r • q.1) z = _
  rw [negativeBallDivergence_sub_solution hA w rq]
  change negativeBallDivergence A w.1 z-negativeBallDivergence A (r • q.1) z = _
  have hRHS := negativeBallDivergence_sub_coefficient (a:=A₁₂) (b:=r • L) hA₁₂ (hL.const_smul r) u z
  have hDHS := negativeBallDivergence_sub_coefficient (b:=fun _ => (1 : Mat dim)) hA contDiff_const q z
  change negativeBallDivergence D q.1 z = _ at hDHS
  rw [negativeBallDivergence_const_smul_solution hA q,hw,negativeBallDivergence_sub_solution hA₁₂,
    hRHS,negativeBallDivergence_const_smul_coefficient L u.1 r,
    negativeBallDivergence_const_smul_coefficient D q.1 r,hDHS,hq₀]
  ring

end CalderonN
