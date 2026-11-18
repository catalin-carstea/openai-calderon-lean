import Proof.LowScalarGeneratorCommutator
import Proof.HalfScalarTransposeCompatibility
import Proof.NativeClosedScalarCommutator
import Proof.ClosedNegativeDegreeScalarCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma balanced_low_scalar_commutator_of_negative_coarse
    (E : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (C : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (Q : ClosedCoefficientJets 3)
    (hLo : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp E=
      Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hC : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (E.comp (closedOneBoundaryScalarMultiplierL Q)-(closedThreeJetCoarseScalarMultiplierL Q).comp E)=
      C.comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) :
    Lo.comp (closedThreeJetHalfBoundaryScalarMultiplierL Q)-(closedThreeJetNegativeScalarMultiplierL Q).comp Lo=
      C.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  have hL (v : SphereSobolev 1) : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (E v)=
      Lo (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v) := DFunLike.congr_fun hLo v
  change Lo (closedThreeJetHalfBoundaryScalarMultiplierL Q (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))-
    closedThreeJetNegativeScalarMultiplierL Q (Lo (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))=_
  rw [← closedThreeJet_scalar_multiplier_one_half,← hL (closedOneBoundaryScalarMultiplierL Q u),← hL u,
    ← closedThreeJet_negative_scalar_multiplier_coarse]
  have hh := DFunLike.congr_fun hC u
  simpa only [ContinuousLinearMap.comp_apply,_root_.sub_apply,map_sub,sphereSobolevInclusionL_trans_apply] using hh

variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}

def nativeNegativeScalarGeneratorCommutator
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (p : NormalFrameRelativeParameter) :
    TaylorGeneratorIndex → ClosedCoefficientJets 3 → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  | .taylor,Q => -(s.coefficients.scalarMultiplierKernel F0 Q p).adjoint
  | .degree,Q => closedNegativeDegreeScalarCommutatorL F0 ha0 Q
  | .rotation i j,Q => (closedCoefficientAngularHalfL i j Q).adjoint

lemma NativeTaylorGeneratorBounds.generator_negative_scalar_commutator
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (a : TaylorGeneratorIndex) (Q : ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp (closedThreeJetHalfBoundaryScalarMultiplierL Q)-
      (closedThreeJetNegativeScalarMultiplierL Q).comp (taylorGeneratorLow (s.response.adjointHalfTaylor p) a)=
      (nativeNegativeScalarGeneratorCommutator s ha0 p a Q).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  cases a
  · exact balanced_low_scalar_commutator_of_negative_coarse _ _ _ Q
      (A.domain.adjointHalfTaylor_coarse_compatible (by norm_num) F0 hF0 p A.domain.pointMem)
      (s.response.adjointTaylor_closed_scalar_commutator_graph A.domain (by norm_num) F0 hF0 Q p A.domain.pointMem)
  · exact balanced_low_scalar_commutator_of_negative_coarse _ _ _ Q
      (ContinuousLinearMap.ext sphereSobolevDegreeL_half) (degree_closed_scalar_negative_graph F0 ha0 hFlat hInv0 Q)
  · rename_i i j
    let T := (closedCoefficientAngularCoarseL i j Q).comp (sphereSobolevInclusionL 1 0 (by norm_num))
    have hC : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        ((closedCoefficientAngularHalfL i j Q).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=T := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply,closedCoefficientAngularHalfL_coarse,sphereSobolevInclusionL_trans_apply,T]
    have hPair (u v : SphereSobolev 1) : ⟪T u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,T v⟫_ℝ :=
      closedCoefficientAngularCoarseL_symmetric i j Q _ _
    have hCompat := half_scalar_transpose_compatible T T (closedCoefficientAngularHalfL i j Q)
      (closedCoefficientAngularHalfL i j Q) hPair hC hC
    exact (A.generator_low_scalar_commutator hF0 ha0 hFlat hInv0 (.rotation i j) Q).trans hCompat
end ShrinkingSpheres
