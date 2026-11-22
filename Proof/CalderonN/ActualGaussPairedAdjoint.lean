module

public import Proof.CalderonN.ActualSupportedGaussMultipliers
public import Proof.CalderonN.ActualSupportedGaussExpansion
public import Proof.CalderonN.SmoothSupportedTraceAdjointCalculus

import Mathlib.Tactic

/-! Reverse the conormal and multiplier factors of the physical Gauss
adjoint, and use the opposite sign of the sphere rotations. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem pairedAdjoint_actualSupportedGauss
    (hn : 3 ≤ dim) (hY : IsOpen Y) (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
    (D : ∀ x ∈ Y, ActualGaussFiberData d x) (i : I dim)
    (hA : SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily D i))
    (hC : SmoothSupportedTraceFiberRegular Y (actualGaussConormalFamily D))
    (hSym : ∀ x (hx : x ∈ Y),∀ z ∈ Metric.ball (0:X dim) 1,((D x hx).coefficient z).IsSymm)
    (hW : SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => (D x hx).reciprocal)))
    (hV : SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => smoothVelocityNormal ((D x hx).velocity i))))
    (hM : ∀ a b : I dim,SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => smoothVelocityAngular ((D x hx).velocity i) a b)))
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0) :
    let C := smoothSupportedTraceFiberAction hY (actualGaussConormalFamily D) hC
    let W := smoothSupportedTraceFiberAction hY _ hW
    let V := smoothSupportedTraceFiberAction hY _ hV
    let M := fun a b => smoothSupportedTraceFiberAction hY _ (hM a b)
    let R := supportedRotation hY
    let H := smoothSupportedTraceBaseMul hY (fun x => (d.radius x)⁻¹) (hr.inv hr₀)
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (smoothSupportedTraceFiberAction hY (actualGaussFiberFamily D i) hA)
      ((V*(W*C)+(∑ a : I dim,∑ b : I dim,M a b*R a b))*H) := by
  dsimp only
  let B := smoothSupportedTracePairingL hn hY μ hμ
  let C := smoothSupportedTraceFiberAction hY (actualGaussConormalFamily D) hC
  let W := smoothSupportedTraceFiberAction hY _ hW
  let V := smoothSupportedTraceFiberAction hY _ hV
  let M := fun a b => smoothSupportedTraceFiberAction hY _ (hM a b)
  let R := supportedRotation hY
  let H := smoothSupportedTraceBaseMul hY (fun x => (d.radius x)⁻¹) (hr.inv hr₀)
  have hC' : PairedAdjoint B C C := pairedAdjoint_supportedFiber hn hY μ hμ _ _ hC hC
    (fun x hx => by simpa only [actualGaussConormalFamily,dite_eq_left hx]
      using (D x hx).conormal_symmetric hn (hSym x hx))
  have hW' : PairedAdjoint B W W := pairedAdjoint_supportedFiber hn hY μ hμ _ _ hW hW
    (fun x hx => supportedSphereMultiplierFamily_selfAdjoint hn _ x hx)
  have hV' : PairedAdjoint B V V := pairedAdjoint_supportedFiber hn hY μ hμ _ _ hV hV
    (fun x hx => supportedSphereMultiplierFamily_selfAdjoint hn _ x hx)
  have hM' (a b : I dim) : PairedAdjoint B (M a b) (M a b) :=
    pairedAdjoint_supportedFiber hn hY μ hμ _ _ (hM a b) (hM a b)
      (fun x hx => supportedSphereMultiplierFamily_selfAdjoint hn _ x hx)
  have hR' (a b : I dim) : PairedAdjoint B (R a b) (-R a b) :=
    pairedAdjoint_supportedRotation hn hY μ hμ a b
  have hH : PairedAdjoint B H H := pairedAdjoint_supportedBaseMul hn hY μ hμ _ _
  have hAng : PairedAdjoint B (∑ a : I dim,∑ b : I dim,R a b*M a b)
      (∑ a : I dim,∑ b : I dim,M a b*(-R a b)) :=
    PairedAdjoint.sum Finset.univ _ _ (fun a _ => PairedAdjoint.sum Finset.univ _ _
      (fun b _ => (hR' a b).mul (hM' a b)))
  have hAngEq : (∑ a : I dim,∑ b : I dim,M a b*(-R a b)) =
      -(∑ a : I dim,∑ b : I dim,M a b*R a b) := by
    simp only [mul_neg,Finset.sum_neg_distrib]
  rw [hAngEq] at hAng
  have hEq : smoothSupportedTraceFiberAction hY (actualGaussFiberFamily D i) hA =
      H*(C*W*V-(∑ a : I dim,∑ b : I dim,R a b*M a b)) := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    simp only [H,C,W,V,M,R,LinearMap.sub_apply,LinearMap.sum_apply,Module.End.mul_apply,
      smoothSupportedTraceBaseMul_fiber,map_sub,map_sum,smoothSupportedTraceFiberAction_fiber,
      actualGaussFiberFamily,actualGaussConormalFamily,supportedSphereMultiplierFamily,dite_eq_left hx]
    simp only [ActualGaussFiberData.adjoint,ActualGaussFiberData.conormal,smoothSphereGaussAdjoint,
      smoothSphereVelocityTangent,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,
      LinearMap.sum_apply,smul_sub,Finset.smul_sum]
  change PairedAdjoint B (smoothSupportedTraceFiberAction hY (actualGaussFiberFamily D i) hA)
    ((V*(W*C)+(∑ a : I dim,∑ b : I dim,M a b*R a b))*H)
  rw [hEq,← sub_neg_eq_add]
  exact hH.mul (((hC'.mul hW').mul hV').sub hAng)

end CalderonN
