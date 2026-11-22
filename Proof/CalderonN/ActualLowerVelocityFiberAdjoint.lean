module

public import Proof.CalderonN.ActualSupportedLowerOrderVelocity
public import Proof.CalderonN.ActualGaussPairedAdjoint

import Proof.CalderonN.MovingRadius
import Mathlib.Tactic

/-! Take the angular transpose of the actual Gauss correction on
each fiber while retaining smooth dependence on the base. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem actualGaussFiberFamily_regular_from_factors
    (hY : IsOpen Y) (F : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim)
    (hC : SmoothSupportedTraceFiberRegular Y (actualGaussConormalFamily F))
    (hW : SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => (F x hx).reciprocal)))
    (hV : SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => smoothVelocityNormal ((F x hx).velocity i))))
    (hM : ∀ a b : I dim,SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => smoothVelocityAngular ((F x hx).velocity i) a b)))
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0) :
    SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i) := by
  let C := actualGaussConormalFamily F
  let W := supportedSphereMultiplierFamily (fun x hx => (F x hx).reciprocal)
  let V := supportedSphereMultiplierFamily (fun x hx => smoothVelocityNormal ((F x hx).velocity i))
  let M (a b : I dim) := supportedSphereMultiplierFamily (fun x hx => smoothVelocityAngular ((F x hx).velocity i) a b)
  let R := smoothSphereTraceRotation (dim:=dim)
  have hSum : SmoothSupportedTraceFiberRegular Y (fun x => ∑ a : I dim,∑ b : I dim,R a b*M a b x) :=
    SmoothSupportedTraceFiberRegular.sum Finset.univ _ (fun a _ =>
      SmoothSupportedTraceFiberRegular.sum Finset.univ _ (fun b _ =>
        (smoothSupportedTraceFiberRegular_rotation a b).mul hY (hM a b)))
  have h := (((hC.mul hY hW).mul hY hV).sub hSum).base_smul hY (hr.inv hr₀)
  apply h.congrOn
  intro x hx
  simp only [C,W,V,M,R,actualGaussFiberFamily,actualGaussConormalFamily,supportedSphereMultiplierFamily,
    dite_eq_left hx]
  rfl

theorem actualGaussLowerVelocityFiber_exists_adjoint (hn : 3 ≤ dim)
    (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim)
    (hC : SmoothSupportedTraceFiberRegular Y (actualGaussConormalFamily F))
    (hSym : ∀ x (hx : x ∈ Y),∀ z ∈ ball (0:X dim) 1,((F x hx).coefficient z).IsSymm)
    (hW : SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => (F x hx).reciprocal)))
    (hV : SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => smoothVelocityNormal ((F x hx).velocity i))))
    (hM : ∀ a b : I dim,SmoothSupportedTraceFiberRegular Y
      (supportedSphereMultiplierFamily (fun x hx => smoothVelocityAngular ((F x hx).velocity i) a b))) :
    ∃ G : X dim → Module.End ℝ (SmoothSphereTrace dim),SmoothSupportedTraceFiberRegular Y G ∧
      ∀ x ∈ Y,SmoothTraceAdjoint hn (actualGaussLowerVelocityFamily F i x) (G x) := by
  let B := smoothTraceFlatDegree hA hEll S
  let C := actualGaussConormalFamily F
  let W := supportedSphereMultiplierFamily (fun x hx => (F x hx).reciprocal)
  let V := supportedSphereMultiplierFamily (fun x hx => smoothVelocityNormal ((F x hx).velocity i))
  let M (a b : I dim) := supportedSphereMultiplierFamily (fun x hx => smoothVelocityAngular ((F x hx).velocity i) a b)
  let R := smoothSphereTraceRotation (dim:=dim)
  let k (x : X dim) := (d.radius x)⁻¹
  let l (x : X dim) := traceCoordinateLogGradient d.radius i x
  let a (j : I dim) (x : X dim) := traceFrameCoordinate d.γ d.frame j i x
  let F₀ (x : X dim) := k x • (V x*(W x*C x)-∑ a : I dim,∑ b : I dim,M a b x*(-R a b))
  let F₁ (x : X dim) := k x • (∑ j : I dim,a j x • smoothTraceLowering B j)
  let G (x : X dim) := F₀ x-F₁ x-l x • B
  have hF₀ : SmoothSupportedTraceFiberRegular Y F₀ := by
    have hSum (a : I dim) : SmoothSupportedTraceFiberRegular Y (fun x => ∑ b : I dim,M a b x*(-R a b)) :=
      SmoothSupportedTraceFiberRegular.sum Finset.univ _ (fun b _ => (hM a b).mul hY
        ((smoothSupportedTraceFiberRegular_rotation (Y:=Y) a b).neg))
    have hRes := ((hV.mul hY (hW.mul hY hC)).sub (SmoothSupportedTraceFiberRegular.sum Finset.univ _
      (fun a _ => hSum a))).base_smul hY (hr.inv hr₀)
    exact hRes
  have hF₁ : SmoothSupportedTraceFiberRegular Y F₁ := by
    have hSum := SmoothSupportedTraceFiberRegular.sum Finset.univ
      (fun j : I dim => fun x => a j x • smoothTraceLowering B j) (fun j _ =>
        (smoothSupportedTraceFiberRegular_lowering hA hEll S hY j).base_smul hY
          (contDiffOn_traceFrameCoordinate hg he j i))
    exact hSum.base_smul hY (hr.inv hr₀)
  have hF₂ : SmoothSupportedTraceFiberRegular Y (fun x => l x • B) :=
    (smoothSupportedTraceFiberRegular_flatDegree hA hEll S Y).base_smul hY
      (contDiffOn_traceCoordinateLogGradient hY hlog i)
  refine ⟨G,(hF₀.sub hF₁).sub hF₂,?_⟩
  intro x hx
  let P := F x hx
  have hCC : SmoothTraceAdjoint hn (C x) (C x) := by
    simpa only [C,actualGaussConormalFamily,dite_eq_left hx] using P.conormal_symmetric hn (hSym x hx)
  have hWW : SmoothTraceAdjoint hn (W x) (W x) := supportedSphereMultiplierFamily_selfAdjoint hn _ x hx
  have hVV : SmoothTraceAdjoint hn (V x) (V x) := supportedSphereMultiplierFamily_selfAdjoint hn _ x hx
  have hMM (a b : I dim) : SmoothTraceAdjoint hn (M a b x) (M a b x) :=
    supportedSphereMultiplierFamily_selfAdjoint hn _ x hx
  have hSum : SmoothTraceAdjoint hn (∑ a : I dim,∑ b : I dim,R a b*M a b x)
      (∑ a : I dim,∑ b : I dim,M a b x*(-R a b)) :=
    SmoothTraceAdjoint.sum Finset.univ _ _ (fun a _ => SmoothTraceAdjoint.sum Finset.univ _ _ (fun b _ =>
      (smoothTraceRotation_skew hn a b).mul (hMM a b)))
  have hGauss : SmoothTraceAdjoint hn (P.adjoint i) (F₀ x) := by
    have hEq : P.adjoint i = k x • (C x*W x*V x-(∑ a : I dim,∑ b : I dim,R a b*M a b x)) := by
      simp only [C,W,V,M,R,k,actualGaussConormalFamily,supportedSphereMultiplierFamily,dite_eq_left hx]
      rfl
    rw [hEq]
    exact ((((hCC.mul hWW).mul hVV).sub hSum).const_smul _)
  have hBS := smoothTraceFlatDegree_symmetric hn hA hEll S
  have hR : SmoothTraceAdjoint hn (k x • ∑ j : I dim,a j x • smoothTraceRaising B j) (F₁ x) :=
    (SmoothTraceAdjoint.sum Finset.univ _ _ (fun j _ => (smoothTraceRaising_adjoint hn B hBS j).const_smul _)).const_smul _
  have hEq : actualGaussLowerVelocityFamily F i x =
      P.adjoint i-k x • (∑ j : I dim,a j x • smoothTraceRaising B j)-l x • B := by
    have hB : P.flatDegree = B :=
      smoothTraceFlatDegree_eq hn P.smoothCoefficient hA P.ellipticCoefficient hEll P.solve S
    have hA := P.adjoint_affine_eq (hr₀ x hx) i
    dsimp only at hA
    rw [hB] at hA
    have hD : l x = k x*fderiv ℝ d.radius x (axis i) :=
      logRadius_derivative d.radius x (axis i) ((hr.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)) (hr₀ x hx)
    have hh := congrArg (fun T : Module.End ℝ (SmoothSphereTrace dim) => k x • T) hA
    simp only [k,smul_add,smul_smul,inv_mul_cancel₀ (hr₀ x hx),one_smul,
      show (d.radius x)⁻¹*(d.radius x)^2 = d.radius x by field_simp [hr₀ x hx]] at hh
    rw [← mul_assoc,inv_mul_cancel₀ (hr₀ x hx),one_mul] at hh
    simp only [actualGaussLowerVelocityFamily,dite_eq_left hx]
    rw [hh,hD]
    have hEq' : P.affineCorrection*(ActualGaussFiberData.translationMultiplier d x i+fderiv ℝ d.radius x (axis i) • 1) =
        P.affineCorrection*ActualGaussFiberData.translationMultiplier d x i+
          fderiv ℝ d.radius x (axis i) • P.affineCorrection := by
      rw [mul_add,mul_smul_comm,mul_one]
    rw [hEq']
    simp only [k,a,traceFrameCoordinate]
    abel
  rw [hEq]
  exact (hGauss.sub hR).sub (hBS.const_smul _)

end CalderonN
