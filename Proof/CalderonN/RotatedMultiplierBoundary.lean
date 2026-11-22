module

public import Proof.CalderonN.RotatedConormalBoundary
public import Proof.CalderonN.MultiplierConormalHalfBound
public import Proof.CalderonN.SmoothMultiplierCommutatorCompletion

import Mathlib.Tactic

/-! Each term in the boundary multiplication commutator contains either a
quadratic bulk remainder or two first-order factors. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Gradient Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def rotatedConormalRemainderData (i j : I dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) {ell : X dim →L[ℝ] ℝ}
    (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f) (r : ℝ)
    (f : SmoothData dim) : SmoothData dim :=
  smoothSubtractData (smoothRotationData i j ((S f).remainder hA r))
    ((S (smoothRotationData i j f)).remainder hA r)

theorem rotated_conormal_multiplier_boundary (i j : I dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (W : SmoothData dim)
    (hW : ∀ v : SmoothData dim, EqOn (smoothBallConormal A v.1)
      (fun z => W.1 z*fderiv ℝ v.1 z z) (standardSphere dim))
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (m f : SmoothData dim) (r : ℝ) :
    let g := smoothDataMul m f
    let U := S f
    let V := S g
    let U' := S (smoothRotationData i j f)
    let V' := S (smoothRotationData i j g)
    let p := angularBallCorrection i j U.actual U'.actual
    let p' := angularBallCorrection i j V.actual V'.actual
    let q := angularBallCorrection i j U.first U'.first
    let q' := angularBallCorrection i j V.first V'.first
    let w := smoothMultiplierDefect m U.actual V.actual
    let w₀ := smoothMultiplierDefect m U.flat V.flat
    let t := smoothMultiplierDefect m p p'
    let t₁ := smoothMultiplierDefect m q q'
    let d := smoothSubtractData w w₀
    let e := smoothSubtractData t ⟨r • t₁.1,t₁.2.const_smul r⟩
    let R := rotatedConormalRemainderData i j hA S r
    let W' := smoothRotationData i j W
    let ell' := ell.comp (ballRotationGeneratorL i j)
    EqOn (fun z => (R g).1 z-m.1 z*(R f).1 z)
      (fun z => W.1 z*fderiv ℝ e.1 z z+r*(W.1 z-1)*fderiv ℝ t₁.1 z z+
        W'.1 z*fderiv ℝ d.1 z z+(W'.1 z-r*ell' z)*fderiv ℝ w₀.1 z z+
        (W'.1 z-r*ell' z)*(fderiv ℝ m.1 z z*f.1 z)) (standardSphere dim) := by
  dsimp only
  let g := smoothDataMul m f
  let U := S f
  let V := S g
  let U' := S (smoothRotationData i j f)
  let V' := S (smoothRotationData i j g)
  let p := angularBallCorrection i j U.actual U'.actual
  let p' := angularBallCorrection i j V.actual V'.actual
  let q := angularBallCorrection i j U.first U'.first
  let q' := angularBallCorrection i j V.first V'.first
  let w := smoothMultiplierDefect m U.actual V.actual
  let w₀ := smoothMultiplierDefect m U.flat V.flat
  let t := smoothMultiplierDefect m p p'
  let t₁ := smoothMultiplierDefect m q q'
  let d := smoothSubtractData w w₀
  let t₁r : SmoothData dim := ⟨r • t₁.1,t₁.2.const_smul r⟩
  let e := smoothSubtractData t t₁r
  let K := smoothRotationData i j W
  let ell' := ell.comp (ballRotationGeneratorL i j)
  let R := rotatedConormalRemainderData i j hA S r
  intro z hz
  change (R g).1 z-m.1 z*(R f).1 z = W.1 z*fderiv ℝ e.1 z z+r*(W.1 z-1)*fderiv ℝ t₁.1 z z+
    K.1 z*fderiv ℝ d.1 z z+(K.1 z-r*ell' z)*fderiv ℝ w₀.1 z z+
    (K.1 z-r*ell' z)*(fderiv ℝ m.1 z z*f.1 z)
  have hU : (R f).1 z = W.1 z*fderiv ℝ p.1 z z+K.1 z*fderiv ℝ U.actual.1 z z-
      r*(ell' z*fderiv ℝ U.flat.1 z z+fderiv ℝ q.1 z z) :=
    rotated_conormal_remainder_boundary i j hA W hW U U' r hz
  have hV : (R g).1 z = W.1 z*fderiv ℝ p'.1 z z+K.1 z*fderiv ℝ V.actual.1 z z-
      r*(ell' z*fderiv ℝ V.flat.1 z z+fderiv ℝ q'.1 z z) :=
    rotated_conormal_remainder_boundary i j hA W hW V V' r hz
  have hP : p.1 z = 0 := angularBallCorrection_trace_zero i j U.actual U'.actual f U.actualTrace U'.actualTrace hz
  have hQ : q.1 z = 0 := (rotated_affine_solution_equation i j U U').2.1 hz
  have hd : fderiv ℝ d.1 z z = fderiv ℝ w.1 z z - fderiv ℝ w₀.1 z z := by
    change fderiv ℝ (w.1-w₀.1) z z = _
    rw [fderiv_sub (w.2.differentiable (by simp) z) (w₀.2.differentiable (by simp) z),sub_apply]
  have he : fderiv ℝ e.1 z z = fderiv ℝ t.1 z z-r*fderiv ℝ t₁.1 z z := by
    change fderiv ℝ (t.1-t₁r.1) z z = _
    rw [fderiv_sub (t.2.differentiable (by simp) z) (t₁r.2.differentiable (by simp) z),sub_apply]
    change _-fderiv ℝ (r • t₁.1) z z = _
    rw [fderiv_const_smul (t₁.2.differentiable (by simp) z),smul_apply,smul_eq_mul]
  rw [hU,hV,hd,he,show fderiv ℝ w.1 z z = _ from radial_smoothMultiplierDefect m U.actual V.actual z,
    show fderiv ℝ w₀.1 z z = _ from radial_smoothMultiplierDefect m U.flat V.flat z,
    show fderiv ℝ t.1 z z = _ from radial_smoothMultiplierDefect m p p' z,
    show fderiv ℝ t₁.1 z z = _ from radial_smoothMultiplierDefect m q q' z,
    hP,hQ,show U.actual.1 z = f.1 z from U.actualTrace hz,show U.flat.1 z = f.1 z from U.flatTrace hz]
  ring

end CalderonN
