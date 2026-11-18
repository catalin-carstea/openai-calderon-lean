import Proof.NativeFirstCovariantHalfLift
import Proof.UniformActualStrongHalfCovariantDerivative
import Proof.StrongHalfCovariantAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma halfOperator_fderiv_adjoint_apply
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (R : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (p v : P) (hR : DifferentiableAt ℝ R p) :
    fderiv ℝ (fun q => (R q).adjoint) p v=(fderiv ℝ R p v).adjoint := by
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have h := (Adj.hasFDerivAt.comp p hR.hasFDerivAt).fderiv
  exact DFunLike.congr_fun h v

theorem NativeRelativeHorizontalTaylorData.true_adjoint_covariant_higher_transfer
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y a : X} (hy : y ∈ Y) {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hAS : ContDiffOn ℝ ∞ A Y) (hGS : ContDiffOn ℝ ∞ G Y)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x))
    (Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hLS : ContDiffAt ℝ ∞ Lo y)
    (hLow : ∀ x ∈ Y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d a A G x)=(Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hHigh : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi y)=
      (actualFirstAdjointErrorFamily d a A G y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hAdj : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH y)=
      (Lo y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (b : X) (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hH : let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
      let v := normalFrameRelativeHorizontalField d.γ d.radius b p
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
        (fderiv ℝ (fun q => (s.firstAdjointHalfErrorFamily C q).adjoint) p v).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    halfOperatorCovariantDerivativeL d (fun x => (Lo x).adjoint) AH y b=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let v := normalFrameRelativeHorizontalField d.γ d.radius b p
  let S := fderiv ℝ (s.firstAdjointErrorFamily C) p v
  let L := fderiv ℝ (s.firstAdjointHalfErrorFamily C) p v
  have hCompat := s.first_covariant_half_derivative_compatible C V hY hΩ hd.1.1
    hK hd.2.2.2.2.1 hF0 v
  have hGraph := s.actual_first_error_covariant_graph C V hY hΩ hSub hd
    hK hy R A G hAS hGS hR hA hG b
  have hHS := contDiffOn_actualFirstAdjointErrorFamily a hY hΩ hSub hd.1
    hK hd.2.2.2.2.1.1
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A G hAS hGS
  have hLowGerm : ∀ᶠ x in 𝓝 y,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x)=
      (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hLow x hx
  have hEq := halfOperatorCovariantDerivativeL_eq_strong_extension
    (actualFirstAdjointErrorFamily d a A G) Lo Hi S L
    ((hHS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    (hLS.differentiableAt (by simp)) hLowGerm hHigh hGraph hCompat
  have hSmooth := (s.contDiffOn_firstAdjointHalfErrorFamily C V hY hΩ hd.1.1
    hK hd.2.2.2.2.1).contDiffAt
      ((s.centerDegreeDomain_open V).mem_nhds (s.centerDegreeDomain_pointMem V))
  have hDf := halfOperator_fderiv_adjoint_apply (s.firstAdjointHalfErrorFamily C) p v
    (hSmooth.differentiableAt (by simp))
  have hPair := balanced_endpoint_pair_of_coarse _ _ _ (hLow y hy) hHigh
  have hActual := half_covariant_adjoint_strong_extension d Lo Hi AH
    hLS b hPair hAdj L hEq
  have hEqH : halfOperatorCovariantDerivativeL d (fun x => (Lo x).adjoint) AH y b=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H := by
    change (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
      (fderiv ℝ (fun q => (s.firstAdjointHalfErrorFamily C q).adjoint) p v).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) at hH
    rw [hDf] at hH
    exact hActual.trans hH.symm
  exact hEqH

end ShrinkingSpheres
