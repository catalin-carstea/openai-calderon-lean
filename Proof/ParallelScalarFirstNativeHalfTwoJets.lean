import Proof.ParallelScalarFirstHalfSecondGraph
import Proof.NativeActualFirstErrorSecondCovariant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Native three-jet data for the SAME error family determine the smooth
strong first half-jet and its actual compatible second half-jet. -/
theorem native_first_error_strong_half_two_jet_graph
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (V : s.response.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K ρ c₀ floor ε : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (hy : y ∈ Y)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x))
    (b c : X) (S : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hS : ∀ x ∈ Y,CoarseCovariantRotationGraph d x b (actualFirstAdjointErrorFamily d a A G) (S x))
    (hL : ∀ x ∈ Y,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S x)=
        (L x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) :
    ContDiffAt ℝ ∞ L y ∧
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let B := normalFrameRelativeHorizontalField d.γ d.radius b
    let v := normalFrameRelativeHorizontalField d.γ d.radius c p
    let T := fderiv ℝ (fun q => fderiv ℝ (s.firstAdjointErrorFamily C) q (B q)) p v
    let N := fderiv ℝ (fun q => fderiv ℝ (s.firstAdjointHalfErrorFamily C) q (B q)) p v
    CoarseCovariantRotationGraph d y c S T ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
        N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let D : Set NormalFrameRelativeParameter := s.centerDegreeDomain V ∩ ⋂ k : I,(C k).domain
  have hD : IsOpen D := (s.centerDegreeDomain_open V).inter
    (isOpen_iInter_of_finite (fun k => (C k).isOpen))
  have hDsub : D ⊆ normalFrameRelativePositiveDomain Ω := by
    intro p hp
    exact s.coefficients.positive (s.response.sub (V.sub hp.1.1))
  have hF : ContDiffOn ℝ ∞ (s.firstAdjointErrorFamily C) D := by
    intro p hp
    have hSmooth := (s.firstErrorAngularFields_smoothAt C V hY hΩ hd.1.1 hK hd.2.2.2.2.1 p hp.1).operator
    have hOp : (fun q => (s.firstErrorAngularFields C q).operator)=s.firstAdjointErrorFamily C := by
      funext q
      exact s.firstErrorAngularFields_operator C q
    rw [hOp] at hSmooth
    exact hSmooth.contDiffWithinAt
  have hHalf : ContDiffOn ℝ ∞ (s.firstAdjointHalfErrorFamily C) D :=
    (s.contDiffOn_firstAdjointHalfErrorFamily C V hY hΩ hd.1.1 hK hd.2.2.2.2.1).mono inter_subset_left
  have hr := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hp : normalFrameRelativeActualParameter d (d.radius y) y ∈ D := by
    rw [normalFrameRelativeActualParameter_point d y hr]
    exact ⟨s.centerDegreeDomain_pointMem V,mem_iInter.mpr (fun k => (C k).point)⟩
  have hGerm := s.actual_first_adjoint_error_germ V hY hΩ hSub hd.1 hK hy hr
    hd.2.2.2.2.1.1 C R A G hR hA hG
  have hCall := strong_half_native_covariant_smooth_and_second hY hΩ hSub hd hK
    (d.radius y) hy b c (actualFirstAdjointErrorFamily d a A G) S L
    (s.firstAdjointErrorFamily C) (s.firstAdjointHalfErrorFamily C) hD hDsub hp hF hHalf hGerm hS hL
    (fun q hq => s.firstAdjointHalfErrorFamily_coarse_compatible C V hF0 q hq.1.1)
    (fun q hq hqe i j u => s.firstError_normalized_rotation_graph C V hY hΩ hd.1.1 hK
      hd.2.2.2.2.1 q hq.1 (fun k => mem_iInter.mp hq.2 k) hqe i j u)
  simpa only [normalFrameRelativeActualParameter_point d y hr] using hCall

end ShrinkingSpheres.ParallelEnergy
