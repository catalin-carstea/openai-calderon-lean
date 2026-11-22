module

public import Proof.CalderonN.ActualSupportedGaussExpansion
public import Proof.CalderonN.AffineDensityVariationIdentity

import Proof.CalderonN.AffineNormalizedCenterJets
import Mathlib.Tactic

/-! The first affine response is a multiplier and a commutator with
flat degree. This realizes its base regularity on the same trace core. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise Classical InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem ActualGaussFiberData.affineCorrection_eq (hn : 3 ≤ dim)
    {x : X dim} (D : ActualGaussFiberData d x)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    let B := smoothTraceFlatDegree hA hEll S
    let L := ActualGaussFiberData.affineDensityMul d x
    D.affineCorrection = (-(1/2:ℝ)) • (L+(B*L-L*B)) := by
  dsimp only
  let L := ActualGaussFiberData.affineDensityMul d x
  let B := D.flatDegree
  rw [← smoothTraceFlatDegree_eq hn D.smoothCoefficient hA D.ellipticCoefficient hEll D.solve S]
  apply LinearMap.ext
  intro u
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let v : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  have hR := smoothTrace_affine_density_radial_formula
    D.smoothCoefficient D.ellipticCoefficient D.solve v
  change smoothSphereTrace (smoothBallRadialDerivative (D.solve v).first) =
    (1/2:ℝ) • (B (L (smoothSphereTrace v))-L (B (smoothSphereTrace v))-L (smoothSphereTrace v)) at hR
  change D.affineCorrection (smoothSphereTrace v) =
    (-(1/2:ℝ)) • (L (smoothSphereTrace v)+(B (L (smoothSphereTrace v))-L (B (smoothSphereTrace v))))
  have hQ : (((LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
      (smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve)))
      (smoothSphereTrace v)) =
    smoothSphereTrace (smoothBallRadialDerivative (D.solve v).first) := by
    simp only [LinearMap.comp_apply,LinearMap.snd_apply,smoothSphereTaylorResponses_apply]
  change _ - (B (L (smoothSphereTrace v))-L (B (smoothSphereTrace v))) = _
  rw [hQ,hR]
  module

namespace SmoothSupportedTraceFiberRegular

theorem congrOn {A B : X dim → Module.End ℝ (SmoothSphereTrace dim)}
    (hA : SmoothSupportedTraceFiberRegular Y A) (hAB : EqOn A B Y) :
    SmoothSupportedTraceFiberRegular Y B := by
  intro u
  obtain ⟨U,F,hU,hYU,hF,hEq⟩ := hA u
  exact ⟨U,F,hU,hYU,hF,fun x hx z => by rw [← hAB hx]; exact hEq x hx z⟩

theorem base_smul {A : X dim → Module.End ℝ (SmoothSphereTrace dim)} {c : X dim → ℝ}
    (hY : IsOpen Y) (hA : SmoothSupportedTraceFiberRegular Y A) (hc : ContDiffOn ℝ ∞ c Y) :
    SmoothSupportedTraceFiberRegular Y (fun x => c x • A x) := by
  intro u
  obtain ⟨U,F,hU,hYU,hF,hEq⟩ := hA u
  let V := U ∩ Prod.fst ⁻¹' Y
  have hV : IsOpen V := hU.inter (hY.preimage continuous_fst)
  have hc' := hc.comp contDiff_fst.contDiffOn (show MapsTo Prod.fst V Y from fun _ h => h.2)
  refine ⟨V,fun p => c p.1*F p,hV,fun _ h => ⟨hYU h,h.1⟩,hc'.mul (hF.mono inter_subset_left),?_⟩
  intro x hx z
  change c x*F (x,z) = _
  rw [hEq x hx z]
  rfl

end SmoothSupportedTraceFiberRegular

private theorem smoothSupportedTraceFiberRegular_familyMultiplier (hY : IsOpen Y)
    (f : X dim → SmoothData dim) (hf : ContDiffOn ℝ ∞ (fun p : X dim × X dim => (f p.1).1 p.2) (Y ×ˢ univ)) :
    SmoothSupportedTraceFiberRegular Y (fun x => smoothSphereTraceMul (f x)) := by
  intro u
  obtain ⟨G,hG,hEq⟩ := smoothSupportedTraceSection_repr u
  refine ⟨Y ×ˢ univ,fun p => (f p.1).1 p.2*G p,hY.prod isOpen_univ,
    prod_mono_right (subset_univ _),hf.mul hG.contDiffOn,?_⟩
  intro x hx z
  rw [smoothSphereTraceMul_apply,smoothSupportedTraceFiberL_apply,hEq x z]

theorem contDiffOn_actualFirstDensityCenterLinear {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} (hK : 0 < K)
    (hd : Background Ω K M d.γ d.g₁ d.g₂ d.frame) :
    ContDiffOn ℝ ∞ (firstDensityCenterLinear d) Ω := by
  have hFrameS : ContDiffOn ℝ ∞ (frameVectorLinear d.frame) Ω := by
    unfold frameVectorLinear
    exact ContDiffOn.sum (fun i _ => ((ContinuousLinearMap.smulRightL ℝ (X dim) (X dim))
      (EuclideanSpace.proj i)).contDiff.comp_contDiffOn (hd.2.2.2.2.2.2.1 i))
  change ContDiffOn ℝ ∞ (fun y => centerInverseDensity d y •
    (fderiv ℝ (firstMetricDensityFactor d.γ d.g₁) y).comp (frameVectorLinear d.frame y)) Ω
  exact (hd.contDiffOn_centerInverseDensity hK).smul
    (((hd.firstMetricDensityFactor_smooth hK).fderiv_of_isOpen (m:=∞) hΩ (by simp)).clm_comp hFrameS)

theorem actualGaussAffineFamily_regular
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y) (hr : ContDiffOn ℝ ∞ d.radius Y)
    (hDensity : ContDiffOn ℝ ∞ (firstDensityCenterLinear d) Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim) :
    SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i) := by
  let B := smoothTraceFlatDegree hA hEll S
  let L := ActualGaussFiberData.affineDensityMul d
  let Q (x : X dim) := (-(1/2:ℝ)) • (L x+(B*L x-L x*B))
  let M (x : X dim) := ActualGaussFiberData.translationMultiplier d x i
  let b (x : X dim) := fderiv ℝ d.radius x (axis i)
  have hL : SmoothSupportedTraceFiberRegular Y L := by
    apply smoothSupportedTraceFiberRegular_familyMultiplier hY
    exact (hDensity.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)).clm_apply contDiff_snd.contDiffOn
  have hB : SmoothSupportedTraceFiberRegular Y (fun _ => B) :=
    smoothSupportedTraceFiberRegular_flatDegree hA hEll S Y
  have hQ : SmoothSupportedTraceFiberRegular Y Q :=
    (hL.add ((hB.mul hY hL).sub (hL.mul hY hB))).base_smul hY contDiffOn_const
  have hM : SmoothSupportedTraceFiberRegular Y M := by
    apply smoothSupportedTraceFiberRegular_familyMultiplier hY
    have hEq (p : X dim × X dim) : (smoothVelocityNormal (smoothConstantVelocity
        (frameCoordinatesL d.γ p.1 (d.frame p.1) (axis i)))).1 p.2 =
        ∑ k : I dim,p.2 k*traceFrameCoordinate d.γ d.frame k i p.1 := by
      change ⟪p.2,frameCoordinatesL d.γ p.1 (d.frame p.1) (axis i)⟫_ℝ = _
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct,star_trivial,traceFrameCoordinate]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    simp_rw [hEq]
    exact ContDiffOn.sum fun j _ => ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp
      contDiff_snd).contDiffOn.mul ((contDiffOn_traceFrameCoordinate hg he j i).comp
        contDiff_fst.contDiffOn (fun _ hx => hx.1))
  have hb : ContDiffOn ℝ ∞ b Y :=
    (hr.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
  apply ((hQ.mul hY hM).add (hQ.base_smul hY hb)).congrOn
  intro x hx
  simp only [actualGaussAffineFamily,dite_eq_left hx,ActualGaussFiberData.affineCorrection_eq hn _ hA hEll S]
  rfl

end CalderonN
