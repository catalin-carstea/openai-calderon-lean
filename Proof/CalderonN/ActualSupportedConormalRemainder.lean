module

public import Proof.CalderonN.ActualSupportedConormal
public import Proof.CalderonN.ActualSupportedAffineRegular
public import Proof.CalderonN.SupportedSphereMultiplierFamily

import Proof.CalderonN.SmoothTraceLinearAdjunction
import Mathlib.Tactic

/-! The scaled quadratic conormal remainder is a regular symmetric
family on the same compactly supported smooth trace domain. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem ActualGaussFiberData.conormalRemainder_eq_affine_symmetric
    (hn : 3 ≤ dim) {x : X dim} (D : ActualGaussFiberData d x)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    let B := smoothTraceFlatDegree hA hEll S
    let L := ActualGaussFiberData.affineDensityMul d x
    D.conormalRemainder = D.conormal-B-(d.radius x) • ((1/2:ℝ) • (L*B+B*L-L)) := by
  dsimp only
  let B := D.flatDegree
  let L := ActualGaussFiberData.affineDensityMul d x
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
    (smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve))
  have hB : B = smoothTraceFlatDegree hA hEll S := smoothTraceFlatDegree_eq hn D.smoothCoefficient
    hA D.ellipticCoefficient hEll D.solve S
  rw [← hB]
  change D.conormal-B-d.radius x • (L*B+Q) = D.conormal-B-d.radius x • ((1/2:ℝ) • (L*B+B*L-L))
  have hQ := D.affineCorrection_eq hn D.smoothCoefficient D.ellipticCoefficient D.solve
  change Q-(B*L-L*B) = (-(1/2:ℝ)) • (L+(B*L-L*B)) at hQ
  rw [sub_eq_iff_eq_add] at hQ
  rw [hQ]
  congr 2
  module

@[expose] def actualGaussScaledConormalFamily (D : ∀ x ∈ Y,ActualGaussFiberData d x)
    (x : X dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  if hx : x ∈ Y then ((d.radius x)^2)⁻¹ • (D x hx).conormalRemainder else 0

theorem actualGaussScaledConormalFamily_regular
    (hn : 3 ≤ dim) (hY : IsOpen Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (D : ∀ x ∈ Y,ActualGaussFiberData d x) (hC : SmoothSupportedTraceFiberRegular Y (actualGaussConormalFamily D))
    (hDensity : ContDiffOn ℝ ∞ (firstDensityCenterLinear d) Y)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0) :
    SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily D) := by
  let B := smoothTraceFlatDegree hA hEll S
  let L₀ (x : X dim) (_ : x ∈ Y) : SmoothData dim :=
    ⟨firstDensityCenterLinear d x,(firstDensityCenterLinear d x).contDiff⟩
  let L := supportedSphereMultiplierFamily L₀
  let R (x : X dim) := (1/2:ℝ) • (L x*B+B*L x-L x)
  have hL : SmoothSupportedTraceFiberRegular Y L := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    refine ⟨Y,fun p => firstDensityCenterLinear d p.1 p.2,hY,hx,Subset.rfl,?_,fun _ _ _ _ _ => rfl⟩
    exact (hDensity.comp contDiff_fst.contDiffOn (fun _ h => h.1)).clm_apply contDiff_snd.contDiffOn
  have hB : SmoothSupportedTraceFiberRegular Y (fun _ => B) :=
    smoothSupportedTraceFiberRegular_flatDegree hA hEll S Y
  have hR : SmoothSupportedTraceFiberRegular Y R :=
    (((hL.mul hY hB).add (hB.mul hY hL)).sub hL).base_smul hY contDiffOn_const
  have h := ((hC.sub hB).sub (hR.base_smul hY hr)).base_smul hY
    ((hr.pow 2).inv (fun x hx => pow_ne_zero 2 (hr₀ x hx)))
  apply h.congrOn
  intro x hx
  simp only [actualGaussScaledConormalFamily,actualGaussConormalFamily,dite_eq_left hx]
  rw [(D x hx).conormalRemainder_eq_affine_symmetric hn hA hEll S]
  simp only [R,L,supportedSphereMultiplierFamily,dite_eq_left hx]
  rfl

theorem actualGaussScaledConormalFamily_symmetric
    (hn : 3 ≤ dim) (D : ∀ x ∈ Y,ActualGaussFiberData d x) {x : X dim} (hx : x ∈ Y)
    (hSym : ∀ z ∈ ball (0:X dim) 1,((D x hx).coefficient z).IsSymm) :
    SmoothTraceAdjoint hn (actualGaussScaledConormalFamily D x) (actualGaussScaledConormalFamily D x) := by
  intro u v
  rw [actualGaussScaledConormalFamily,dite_eq_left hx]
  have h : SmoothTraceAdjoint hn (D x hx).conormalRemainder (D x hx).conormalRemainder :=
    smoothSphereTrace_remainder_symmetric hn (D x hx).smoothCoefficient (D x hx).ellipticCoefficient
      hSym (D x hx).solve (D x hx).weight (D x hx).weightConormal (d.radius x)
  simp only [LinearMap.smul_apply,map_smul,real_inner_smul_left,real_inner_smul_right,h u v]

end CalderonN
