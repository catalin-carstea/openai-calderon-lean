module

public import Proof.CalderonN.ActualSupportedGaussFiber
public import Proof.CalderonN.FlatTraceTranslationDirection

import Mathlib.Tactic

/-! Separate the affine and quadratic terms of the actual Gauss operators
on the smooth sphere core, before lifting them to base sections. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {d : Data dim} {x : X dim}

namespace ActualGaussFiberData

variable (D : ActualGaussFiberData d x)

abbrev flatDegree := smoothTraceFlatDegree D.smoothCoefficient D.ellipticCoefficient D.solve

@[expose] def normalResponse : Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceMul D.weight *
    ((LinearMap.fst ℝ _ _).comp
      (smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve)) *
    smoothSphereTraceMul D.reciprocal

@[expose] def affineDensityMul (d : Data dim) (x : X dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceMul ⟨firstDensityCenterLinear d x,(firstDensityCenterLinear d x).contDiff⟩

@[expose] def affineCorrection : Module.End ℝ (SmoothSphereTrace dim) :=
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    (smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve))
  Q-(D.flatDegree*affineDensityMul d x-affineDensityMul d x*D.flatDegree)

@[expose] def responseRemainder : Module.End ℝ (SmoothSphereTrace dim) :=
  ((d.radius x)^2)⁻¹ • (D.normalResponse-D.flatDegree-d.radius x • D.affineCorrection)

@[expose] def centerCorrection (i : I dim) : SmoothBallVelocity dim :=
  let a := frameCoordinatesL d.γ x (d.frame x) (axis i)
  let b := fderiv ℝ d.radius x (axis i)
  ⟨fun z => ((d.radius x)^2)⁻¹ • ((D.velocity i).1 z-a-b • z),
    (((D.velocity i).2.sub contDiff_const).sub (contDiff_id.const_smul b)).const_smul _⟩

@[expose] def translationMultiplier (d : Data dim) (x : X dim) (i : I dim) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceMul (smoothVelocityNormal (smoothConstantVelocity
    (frameCoordinatesL d.γ x (d.frame x) (axis i))))

@[expose] def velocityRemainder (i : I dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  D.responseRemainder*(translationMultiplier d x i+fderiv ℝ d.radius x (axis i) • 1)+
  D.normalResponse*smoothSphereTraceMul (smoothVelocityNormal (D.centerCorrection i))-
    smoothSphereVelocityTangent (D.centerCorrection i)

theorem adjoint_affine_eq (hr : d.radius x ≠ 0) (i : I dim) :
    let r := d.radius x
    let b := fderiv ℝ d.radius x (axis i)
    let a := frameCoordinatesL d.γ x (d.frame x) (axis i)
    r • D.adjoint i =
      (∑ k : I dim,a k • smoothTraceRaising D.flatDegree k)+b • D.flatDegree+
        r • (D.affineCorrection*translationMultiplier d x i+b • D.affineCorrection)+
        r^2 • D.velocityRemainder i := by
  dsimp only
  let r := d.radius x
  let b := fderiv ℝ d.radius x (axis i)
  let a := frameCoordinatesL d.γ x (d.frame x) (axis i)
  let U := D.centerCorrection i
  let V := D.velocity i
  let N := D.normalResponse
  let B := D.flatDegree
  let F := D.affineCorrection
  let G := D.responseRemainder
  have hr₂ : r^2 ≠ 0 := pow_ne_zero 2 hr
  have hN : N = B+r • F+r^2 • G := by
    change N = B+r • F+r^2 • ((r^2)⁻¹ • (N-B-r • F))
    rw [smul_smul,mul_inv_cancel₀ hr₂,one_smul]
    abel
  have hV : V = smoothAffineVelocity a b (r^2) U := by
    apply Subtype.ext
    funext z
    change V.1 z = a+b • z+r^2 • ((r^2)⁻¹ • (V.1 z-a-b • z))
    rw [smul_smul,mul_inv_cancel₀ hr₂,one_smul]
    abel
  have hG : smoothSphereGaussAdjoint N V =
      (∑ k : I dim,a k • smoothTraceRaising B k)+b • B+
        r • (F*translationMultiplier d x i+b • F)+r^2 • D.velocityRemainder i := by
    conv_lhs => rw [hV,smoothSphereGaussAdjoint,smoothSphereVelocityNormal_affine,
      smoothSphereVelocityTangent_affine]
    rw [← smoothTraceRaising_const_eq_sum]
    exact moving_adjoint_affine_expansion N B F G (translationMultiplier d x i)
      (smoothSphereTraceMul (smoothVelocityNormal U)) (smoothSphereVelocityTangent (smoothConstantVelocity a))
      (smoothSphereVelocityTangent U) r b hN
  change r • (r⁻¹ • smoothSphereGaussAdjoint N V) = _
  rw [smul_smul,mul_inv_cancel₀ hr,one_smul]
  exact hG

end ActualGaussFiberData

end CalderonN
