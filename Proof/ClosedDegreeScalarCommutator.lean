import Proof.ClosedHalfRadialScalarCommutator
import Proof.FlatHarmonicBoundaryGradient
import Proof.SmoothMultiplierDomainCompatibility
import Proof.AdjointMultiplierGainGraph
import Proof.CoarseAngularProductPackets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

lemma degree_smooth_scalar_commutator_half_graph (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : SmoothCoefficientJets 3) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((halfRadialMultiplierCommutatorL F0 ha0 Q).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) =
      sphereSobolevDegreeL.comp (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q))-
        (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))).comp sphereSobolevDegreeL := by
  let K := halfRadialMultiplierCommutatorL F0 ha0 Q
  let Ih := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
  let J1 := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let M1 := oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q)
  let M0 := coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
  let Mh := halfBoundaryCoefficientMulL (smoothMultiplierLowerJets Q)
  let M3 := nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace Q
  have hTrace (f : SphereSobolev (3/2:ℝ)) : Ih (fixedHalfOutwardTraceL (fixedHarmonicLiftL f))=sphereSobolevDegreeL (I1 f) :=
    (OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.sphereSobolevInclusionL_nativeHalfOutwardTraceL
      sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus fixedUnitBallValueTrace
      (fixedHarmonicLiftL f)).trans (sphereSobolevDegreeL_harmonicLift f).symm
  let L := Ih.comp (K.comp J1)
  let R := sphereSobolevDegreeL.comp M1-M0.comp sphereSobolevDegreeL
  have hEq : (fun u : SphereSobolev 1 => L u)=(fun u => R u) :=
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).equalizer L.continuous R.continuous (by
    funext f
    have hGraph := halfRadialMultiplierCommutatorL_high F0 ha0 (flat_compact_coefficient_energy_coercive F0 ha0 hFlat) hInv0 Q f
    rw [strongPoissonL_flat_coefficient F0 hFlat] at hGraph
    have hI : J1 (I1 f)=sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f :=
      congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A f)
        (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
    change Ih (K (J1 (I1 f)))=sphereSobolevDegreeL (M1 (I1 f))-M0 (sphereSobolevDegreeL (I1 f))
    rw [hI,hGraph,map_sub,halfBoundaryCoefficientMul_coarse Q,hTrace,hTrace,oneBoundaryCoefficientMulL_third_high])
  exact ContinuousLinearMap.ext (congrFun hEq)

lemma degree_closed_scalar_commutator_half_graph (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible) (Q : ClosedCoefficientJets 3) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((closedHalfRadialScalarCommutatorL F0 ha0 Q).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) =
      sphereSobolevDegreeL.comp (closedOneBoundaryScalarMultiplierL Q)-
        (closedThreeJetCoarseScalarMultiplierL Q).comp sphereSobolevDegreeL := by
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        ((closedHalfRadialScalarCommutatorL F0 ha0 Q).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) =
        sphereSobolevDegreeL.comp (closedOneBoundaryScalarMultiplierL Q)-
          (closedThreeJetCoarseScalarMultiplierL Q).comp sphereSobolevDegreeL := by
    rintro _ ⟨Q,rfl⟩
    rw [closedHalfRadialScalarCommutatorL_on_smooth,closedOneBoundaryScalarMultiplierL_on_smooth,
      closedThreeJetCoarseScalarMultiplierL_on_smooth]
    exact degree_smooth_scalar_commutator_half_graph F0 ha0 hFlat hInv0 Q
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q
end ShrinkingSpheres
