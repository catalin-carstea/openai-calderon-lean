import Proof.FixedHigherScalarJets
import Proof.DenseOperatorRestrictionUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma closedHalfRadialScalarCommutator_unit (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    closedHalfRadialScalarCommutatorL F0 ha0 (closedUnitCoefficient Q0)=0 := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  have hh := degree_closed_scalar_commutator_higher_graph F0 ha0 hFlat hInv0 (closedUnitCoefficient Q0)
  rw [closedUnitCoefficient_higher Q0 hQ0,closedUnitCoefficient_half Q0 hQ0,
    ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp,sub_self] at hh
  exact hh.symm.trans (ContinuousLinearMap.zero_comp _).symm

/-- Linearity of the genuine higher degree commutator is proved through
    the actual inclusion; angular representatives may differ off the sphere. -/
lemma closedHigherDegreeScalarFromRotationData_unit_add_smul
    (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (Q Q1 Q2 : ClosedCoefficientJets 3) (R R1 R2 : I × I → ClosedCoefficientJets 3) (r : ℝ)
    (hQ : Q=closedUnitCoefficient Q0+r • Q1+Q2)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j))=closedCoefficientAngularHalfL i j Q)
    (hR1 : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R1 (i,j))=closedCoefficientAngularHalfL i j Q1)
    (hR2 : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R2 (i,j))=closedCoefficientAngularHalfL i j Q2) :
    closedHigherDegreeScalarFromRotationData F0 ha0 Q R=
      r • closedHigherDegreeScalarFromRotationData F0 ha0 Q1 R1+
        closedHigherDegreeScalarFromRotationData F0 ha0 Q2 R2 := by
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let C := closedHalfRadialScalarCommutatorL F0 ha0
  have hUnit : C (closedUnitCoefficient Q0)=0 :=
    closedHalfRadialScalarCommutator_unit F0 ha0 hFlat hInv0 Q0 hQ0
  have hC : C Q=r • C Q1+C Q2 := by
    have hMap : C (closedUnitCoefficient Q0+r • Q1+Q2)=
        (C (closedUnitCoefficient Q0)+C (r • Q1))+C Q2 :=
      (C.map_add _ _).trans (congrArg
        (fun V : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => V+C Q2) (C.map_add _ _))
    have hScaled : C (r • Q1)=r • C Q1 := C.map_smul r Q1
    exact (congrArg C hQ).trans (hMap.trans (by rw [hUnit,hScaled,zero_add]))
  have hOne := closedHigherDegreeScalarFromRotationData_compatible F0 ha0 hFlat hInv0 Q R hR
  have hTwo := closedHigherDegreeScalarFromRotationData_compatible F0 ha0 hFlat hInv0 Q1 R1 hR1
  have hThree := closedHigherDegreeScalarFromRotationData_compatible F0 ha0 hFlat hInv0 Q2 R2 hR2
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have h1 := DFunLike.congr_fun hOne u
  have h2 := DFunLike.congr_fun hTwo u
  have h3 := DFunLike.congr_fun hThree u
  change I1 (closedHigherDegreeScalarFromRotationData F0 ha0 Q R u)=_ at h1
  change I1 (closedHigherDegreeScalarFromRotationData F0 ha0 Q1 R1 u)=_ at h2
  change I1 (closedHigherDegreeScalarFromRotationData F0 ha0 Q2 R2 u)=_ at h3
  change I1 (closedHigherDegreeScalarFromRotationData F0 ha0 Q R u)=
    I1 (r • closedHigherDegreeScalarFromRotationData F0 ha0 Q1 R1 u+
      closedHigherDegreeScalarFromRotationData F0 ha0 Q2 R2 u)
  calc
    _ = C Q (I1 u) := h1
    _ = r • C Q1 (I1 u)+C Q2 (I1 u) := DFunLike.congr_fun hC (I1 u)
    _ = r • I1 (closedHigherDegreeScalarFromRotationData F0 ha0 Q1 R1 u)+
        I1 (closedHigherDegreeScalarFromRotationData F0 ha0 Q2 R2 u) :=
      congrArg₂ (fun x z : SphereSobolev (1/2:ℝ) => r • x+z) h2.symm h3.symm
    _ = _ := ((I1.map_add _ _).trans (congrArg
      (fun x : SphereSobolev (1/2:ℝ) => x+I1 (closedHigherDegreeScalarFromRotationData F0 ha0 Q2 R2 u))
      (I1.map_smul r _))).symm
end ShrinkingSpheres
