module

public import Proof.CalderonN.ActualGaussOperatorExpansion
public import Proof.CalderonN.TraceCoordinateModel

import Proof.CalderonN.MovingRadius
import Mathlib.Tactic

/-! Lift the actual fiber expansion to the common base domain. The
radius-gained remainder inherits smoothness from the expansion itself. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {d : Data dim}

@[expose] def actualGaussFiberFamily (F : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim)
    (x : X dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  if hx : x ∈ Y then (F x hx).adjoint i else 0

@[expose] def actualGaussAffineFamily (F : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim)
    (x : X dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  if hx : x ∈ Y then
    (F x hx).affineCorrection*ActualGaussFiberData.translationMultiplier d x i+
      fderiv ℝ d.radius x (axis i) • (F x hx).affineCorrection
    else 0

variable (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
  (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
  (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
variable (F : ∀ x ∈ Y,ActualGaussFiberData d x)
  (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
  (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))

abbrev actualSupportedAffine (i : I dim) :=
  smoothSupportedTraceFiberAction hY (actualGaussAffineFamily F i) (hF i)

@[expose] def actualSupportedGaussRemainder (i : I dim) : Module.End ℝ (SmoothSupportedTraceSection Y) :=
  let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S i
  let B := supportedFlatDegree hA hEll S hY
  let L := smoothSupportedTraceBaseMul hY (traceCoordinateLogGradient d.radius i)
      (contDiffOn_traceCoordinateLogGradient hY hlog i)
  smoothSupportedTraceFiberAction hY (actualGaussFiberFamily F i) (hC i)-V-L*B-
    actualSupportedAffine hY F hF i

theorem actualSupportedTraceDerivative_expand (i : I dim) :
    supportedTraceDerivative hY hg hK he (actualGaussFiberFamily F) hC i =
      supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S i+
      supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S i+
      actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF i+
      actualSupportedAffine hY F hF i := by
  unfold supportedTraceDerivative supportedCoordinateModelDerivative actualSupportedGaussRemainder
  dsimp only
  abel

theorem actualSupportedGaussRemainder_fiber (hn : 3 ≤ dim) {x : X dim} (hx : x ∈ Y)
    (i : I dim) (u : SmoothSupportedTraceSection Y) :
    smoothSupportedTraceFiberL x
      (actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF i u) =
      d.radius x • (F x hx).velocityRemainder i (smoothSupportedTraceFiberL x u) := by
  let p := F x hx
  let r := d.radius x
  let b := fderiv ℝ d.radius x (axis i)
  let a := frameCoordinatesL d.γ x (d.frame x) (axis i)
  let v := smoothSupportedTraceFiberL x u
  let B := smoothTraceFlatDegree hA hEll S
  let Q := p.affineCorrection*ActualGaussFiberData.translationMultiplier d x i+b • p.affineCorrection
  have hB : p.flatDegree = B := smoothTraceFlatDegree_eq hn
    p.smoothCoefficient hA p.ellipticCoefficient hEll p.solve S
  have hrx : r ≠ 0 := hr₀ x hx
  have hD : traceCoordinateLogGradient d.radius i x = r⁻¹*b :=
    logRadius_derivative d.radius x (axis i) ((hr.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)) hrx
  have hOp := p.adjoint_affine_eq hrx i
  dsimp only at hOp
  change r • p.adjoint i = (∑ k : I dim,a k • smoothTraceRaising p.flatDegree k)+b • p.flatDegree+
    r • Q+r^2 • p.velocityRemainder i at hOp
  rw [hB] at hOp
  have hU := congrArg (fun T : Module.End ℝ (SmoothSphereTrace dim) => T v) hOp
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply] at hU
  have hSol := congrArg (fun U : SmoothSphereTrace dim => r⁻¹ • U) hU
  simp only [smul_add,smul_smul,inv_mul_cancel₀ hrx,one_smul,
    show r⁻¹*r^2 = r by field_simp [hrx]] at hSol
  simp only [actualSupportedGaussRemainder,LinearMap.sub_apply,map_sub,Module.End.mul_apply,
    smoothSupportedTraceFiberAction_fiber,smoothSupportedTraceFiberL_leadingVelocity hY hg he hr hr₀ hA hEll S hx,
    smoothSupportedTraceBaseMul_fiber,actualGaussFiberFamily,actualSupportedAffine,actualGaussAffineFamily,
    dite_eq_left hx,hD]
  change p.adjoint i v-r⁻¹ • (∑ k : I dim,a k • smoothTraceRaising B k v)-(r⁻¹*b) • B v-Q v =
    r • p.velocityRemainder i v
  rw [hSol]
  abel

end CalderonN
