import Proof.NativeRelativeFullAdjointJets
import Proof.ClosedBoundaryGradientAdjoint
import Proof.RelativeInverseRadiusFactorJets
import Proof.RelativeCenterErrorCoefficientFamily
import Proof.NativeRelativePhysicalRadialIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def NativeRelativeHorizontalTaylorData.centerGradientAdjointFamily
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (d.radius y)⁻¹ • (normalFrameRelativeInverseRadiusFactor p •
    closedBoundaryGradientAdjoint (fun j => (C j).closed p) (s.response.fullAdjoint p))

theorem NativeRelativeHorizontalTaylorData.centerGradientAdjointFamily_actual
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH) :
    s.centerGradientAdjointFamily C ((y,frameVectorLinear d.frame y),0) =
      (d.radius y)⁻¹ • boundaryGradientAdjointL (fun j => (C j).pointCoefficient) s.radialAdjointL := by
  change (d.radius y)⁻¹ • ((1+(0:ℝ))⁻¹ •
    closedBoundaryGradientAdjoint (fun j => (C j).closed ((y,frameVectorLinear d.frame y),0)) s.radialAdjointL) = _
  simp only [add_zero,inv_one,one_smul]
  exact congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => (d.radius y)⁻¹ • T)
    (closedBoundaryGradientAdjoint_on_smooth
      (fun j => commonSupportCoefficientFamily 3 (C j).scalar (C j).smooth (C j).support (C j).compact (C j).supported
        ((y,frameVectorLinear d.frame y),0)) s.radialAdjointL)

/-- Common ordinary and actual horizontal three-jets of the radius-rescaled
    physical Jacobi boundary-gradient adjoint. Its size is linear in radius. -/
theorem uniform_relative_center_gradient_adjoint_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K)
    (CQ CA CC : ℝ) (hCQ : 0 ≤ CQ) (hCA : 0 ≤ CA) (hCC : 0 ≤ CC) :
    ∃ CG CGH : ℝ,0 ≤ CG ∧ 0 ≤ CGH ∧ ∀ d : Data,Background Ω K M d.γ d.g₁ d.g₂ d.frame →
      ∀ floor c₀,1 ≤ floor → Profile Y d.γ d.frame d.radius floor c₀ Cj → ∀ y ∈ Y,d.radius y ≤ 1 →
      ∀ (F0 : SmoothCoefficientMatrix 2) (CI CW CF CM CH : ℝ),
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ a : X,∀ C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH,
      ContDiffAt ℝ ∞ (s.centerGradientAdjointFamily C) ((y,frameVectorLinear d.frame y),0) ∧
      (∀ n : ℕ,n ≤ 3 → ‖iteratedFDeriv ℝ n (s.centerGradientAdjointFamily C)
        ((y,frameVectorLinear d.frame y),0)‖ ≤ CG*‖a‖*d.radius y) ∧
      ∀ b : ℕ → X,(∀ j,‖b j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
        ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
          (s.centerGradientAdjointFamily C) n ((y,frameVectorLinear d.frame y),0)‖ ≤
          CGH*‖a‖*d.radius y*(beta d.γ d.radius y)^n := by
  obtain ⟨CR,hCR,hReciprocal⟩ := exists_relative_inverse_radius_factor_jet_bound 3
  obtain ⟨CX,hCX,hHorizontal⟩ := uniform_normalFrame_horizontal_third_jets hY hΩ hSub hm K M Cj hK
  let CD := ‖sphereSobolevDegreeL‖+6*CQ+CA
  let B := 73*boundaryTangentialAdjointBudget+2^3*CD*(73*oneSphereCoordinateMultiplierBudget)
  let CG := (2^3*CR*B)*CC
  let CGH := CX*CG
  have hCR0 : 0 ≤ CR := zero_le_one.trans hCR
  have hCD : 0 ≤ CD := by dsimp only [CD];positivity
  have hCoord : 0 ≤ oneSphereCoordinateMultiplierBudget := by unfold oneSphereCoordinateMultiplierBudget;positivity
  have hB : 0 ≤ B := by have ht := boundaryTangentialAdjointBudget_nonneg;dsimp only [B];positivity
  have hCG : 0 ≤ CG := by dsimp only [CG];positivity
  have hCGH : 0 ≤ CGH := by dsimp only [CGH];positivity
  refine ⟨CG,CGH,hCG,hCGH,?_⟩
  intro d hd floor c₀ hf hp y hy hr1 F0 CI CW CF CM CH s a C
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := fun j => (C j).closed
  let A := s.response.fullAdjoint
  let G := fun p => closedBoundaryGradientAdjoint (fun j => Q j p) (A p)
  let R := normalFrameRelativeInverseRadiusFactor
  let H := fun p => R p • G p
  have hr : 0 < d.radius y := (hp.2 y hy).1
  have hQ (j : I) : ContDiffAt ℝ ∞ (Q j) p0 :=
    (contDiff_commonSupportClosedCoefficientFamily 3 (C j).scalar (C j).smooth (C j).support (C j).compact (C j).supported).contDiffAt
  obtain ⟨hA,hAJ⟩ := s.response.full_adjoint_jet_bound 3 (by norm_num) hCQ hCA hr.le hr1 s.adjointJoint
  have hG : ContDiffAt ℝ ∞ G p0 := contDiffAt_closedBoundaryGradientAdjoint Q A p0 hQ hA
  have hGJ (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n G p0‖ ≤ B*(CC*‖a‖*(d.radius y)^2) :=
    norm_iteratedFDeriv_closedBoundaryGradientAdjoint_le Q A p0 hQ hA 3 (CC*‖a‖*(d.radius y)^2) CD
      (by positivity) hCD (fun j k hk => (C j).joint k hk) hAJ n hn
  obtain ⟨hR,hRJ⟩ := hReciprocal y (frameVectorLinear d.frame y)
  have hR' : ContDiffAt ℝ ∞ R p0 := hR
  have hRJ' (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n R p0‖ ≤ CR := hRJ n hn
  have hH : ContDiffAt ℝ ∞ H p0 := hR'.smul hG
  have hHS : ContDiffAt ℝ ∞ (s.centerGradientAdjointFamily C) p0 := hH.const_smul (d.radius y)⁻¹
  have hHJ (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n H p0‖ ≤ (2^3*CR*B)*(CC*‖a‖*(d.radius y)^2) := by
    have hh := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.lsmul ℝ ℝ (E:=SphereSobolev 1 →L[ℝ] SphereSobolev 0))
      R G p0 hR' hG 3 CR (B*(CC*‖a‖*(d.radius y)^2)) hCR0 (by positivity) hRJ' hGJ n hn
    exact hh.trans (by
      calc
        _ = ‖(ContinuousLinearMap.lsmul ℝ ℝ (E:=SphereSobolev 1 →L[ℝ] SphereSobolev 0))‖*
          ((2^3*CR*B)*(CC*‖a‖*(d.radius y)^2)) := by ring
        _ ≤ 1*((2^3*CR*B)*(CC*‖a‖*(d.radius y)^2)) :=
          mul_le_mul_of_nonneg_right ContinuousLinearMap.opNorm_lsmul_le (by positivity)
        _ = _ := one_mul _)
  have hJets (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n (s.centerGradientAdjointFamily C) p0‖ ≤ CG*‖a‖*d.radius y := by
    change ‖iteratedFDeriv ℝ n (fun p => (d.radius y)⁻¹ • H p) p0‖ ≤ _
    rw [norm_iteratedFDeriv_const_smul_at H p0 hH (d.radius y)⁻¹ n,abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left (hHJ n hn) (inv_nonneg.mpr hr.le)).trans_eq (by dsimp only [CG];field_simp)
  refine ⟨hHS,hJets,?_⟩
  have hJs (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n (s.centerGradientAdjointFamily C) p0‖ ≤
      (CG*‖a‖/(d.radius y))*(d.radius y)^2 := (hJets n hn).trans_eq (by field_simp)
  have hh := hHorizontal d hd floor c₀ hf hp y hy (SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (s.centerGradientAdjointFamily C) hHS (CG*‖a‖/(d.radius y)) (d.radius y) (by positivity) hJs
  intro b hb n hn
  exact (hh b hb n hn).trans_eq (by dsimp only [CGH];field_simp)

end ShrinkingSpheres
