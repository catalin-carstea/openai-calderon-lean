import Proof.SmoothMultiplierDomainCompatibility
import Proof.OrderOneCoefficientAlgebra
import Proof.Archive.NativeHarmonicHalfCoarseDualPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

/-- The forward gained scalar commutator determines the true L2 adjoint
commutator as its negative dual adjoint, on the full H1 domain. -/
theorem adjoint_multiplier_gain_graph
    (R Ra : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (Q : SmoothCoefficientJets 3)
    (hAdj : ∀ u v : SphereSobolev 1,
      ⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ)
    (hG : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (G.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) =
      R.comp (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q))-
      (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))).comp R) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (Ra.comp (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q))-
        (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))).comp Ra) =
    (-realHalfOperatorAdjointL G).comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  let M1 := oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q)
  let M0 := coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let Ih := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let J0 := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let In := sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)
  let Jn := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let Ga := -realHalfOperatorAdjointL G
  let Ca := Ra.comp M1-M0.comp Ra
  have hM (u : SphereSobolev 1) : I0 (M1 u) = M0 (I0 u) := by
    have h := oneBoundaryCoefficientMulL_coarse (smoothMultiplierLowerJets Q) u
    have hm : coefficientSmoothData (smoothMultiplierLowerJets Q) = nativeH2CoefficientSmoothData Q :=
      Subtype.ext (coefficientValue_smoothMultiplierLowerJets Q)
    rw [hm] at h
    exact h
  have hIh (u : SphereSobolev 1) : J0 (Ih u) = I0 u :=
    congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A u)
      (sphereSobolevInclusionL_trans 1 (1/2:ℝ) 0 (by norm_num) (by norm_num))
  have hIn (u : SphereSobolev 1) : Jn (I0 u) = In u :=
    congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u)
      (sphereSobolevInclusionL_trans 1 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  have hSkew (u v : SphereSobolev 1) : ⟪R (M1 u)-M0 (R u),I0 v⟫_ℝ = -⟪I0 u,Ca v⟫_ℝ := by
    change ⟪R (M1 u)-M0 (R u),I0 v⟫_ℝ = -⟪I0 u,Ra (M1 v)-M0 (Ra v)⟫_ℝ
    rw [inner_sub_left,inner_sub_right,hAdj (M1 u) v,
      coarseSphereScalarMulL_symmetric _ (R u) (I0 v),← hM v,hAdj u (M1 v),hM u,
      coarseSphereScalarMulL_symmetric _ (I0 u) (Ra v)]
    ring
  have hGraph (u : SphereSobolev 1) : J0 (G (Ih u)) = R (M1 u)-M0 (R u) :=
    congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A u) hG
  have hTest (u v : SphereSobolev 1) :
      sphereSobolevDualPairing (1/2:ℝ) (Ih u) (Jn (Ca v)) =
      sphereSobolevDualPairing (1/2:ℝ) (Ih u) (Ga (In v)) := by
    have hLeft : sphereSobolevDualPairing (1/2:ℝ) (Ih u) (Jn (Ca v)) = ⟪I0 u,Ca v⟫_ℝ := by
      have h := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) (Ih u) (Ca v)
      exact h.trans (congrArg (fun w : SphereSobolev 0 => ⟪w,Ca v⟫_ℝ) (hIh u))
    have hRight : sphereSobolevDualPairing (1/2:ℝ) (G (Ih u)) (In v) = ⟪J0 (G (Ih u)),I0 v⟫_ℝ := by
      have h := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) (G (Ih u)) (I0 v)
      exact (congrArg (fun w => sphereSobolevDualPairing (1/2:ℝ) (G (Ih u)) w) (hIn v)).symm.trans h
    have hDual : sphereSobolevDualPairing (1/2:ℝ) (Ih u) (Ga (In v)) =
        -sphereSobolevDualPairing (1/2:ℝ) (G (Ih u)) (In v) := by
      change ⟪Ih u,-(ContinuousLinearMap.adjoint G (In v))⟫_ℝ = -⟪G (Ih u),In v⟫_ℝ
      rw [inner_neg_right,ContinuousLinearMap.adjoint_inner_right]
    rw [hLeft,hDual,hRight,hGraph]
    linarith [hSkew u v]
  apply ContinuousLinearMap.ext
  intro v
  have hContL : Continuous (fun u : SphereSobolev (1/2:ℝ) => sphereSobolevDualPairing (1/2:ℝ) u (Jn (Ca v))) :=
    continuous_id.inner continuous_const
  have hContR : Continuous (fun u : SphereSobolev (1/2:ℝ) => sphereSobolevDualPairing (1/2:ℝ) u (Ga (In v))) :=
    continuous_id.inner continuous_const
  have hEq := (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).equalizer hContL hContR
    (funext (fun u => hTest u v))
  apply ext_inner_left ℝ
  intro u
  exact congrFun hEq u

end ShrinkingSpheres
