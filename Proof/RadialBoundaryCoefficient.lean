import Proof.CoarseOneBoundaryAffine
import Proof.BoundaryScalarGeneratorDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

lemma boundaryNormalCoefficient_of_radial_row (F : SmoothCoefficientMatrix 2) (q : UnitSphere → ℝ)
    (hRow : ∀ w : UnitSphere,∀ j : I,∑ i : I,w.val i*coefficientValue 2 (F i j) w.val=q w*w.val j)
    (w : UnitSphere) : (boundaryNormalCoefficientData F).1 w.val=q w := by
  calc
    _ = ∑ j : I,(∑ i : I,w.val i*coefficientValue 2 (F i j) w.val)*w.val j :=
      (sum_boundary_normal_coefficients F w.val).symm
    _ = ∑ j : I,q w*(w.val j)^2 := Finset.sum_congr rfl (fun j _ => by rw [hRow w j];ring)
    _ = q w*(∑ j : I,(w.val j)^2) := (Finset.mul_sum _ _ _).symm
    _ = q w := by rw [unitSphere_sum_sq,mul_one]

lemma boundaryTangentCoefficient_of_radial_row (F : SmoothCoefficientMatrix 2) (q : UnitSphere → ℝ)
    (hRow : ∀ w : UnitSphere,∀ j : I,∑ i : I,w.val i*coefficientValue 2 (F i j) w.val=q w*w.val j)
    (w : UnitSphere) (j : I) : (boundaryTangentCoefficientData F j).1 w.val=0 := by
  change (∑ i : I,w.val i*coefficientValue 2 (F i j) w.val)-(boundaryNormalCoefficientData F).1 w.val*w.val j=0
  rw [hRow,boundaryNormalCoefficient_of_radial_row F q hRow,sub_self]

lemma radial_row_tangent_multipliers_zero (F : SmoothCoefficientMatrix 2) (q : UnitSphere → ℝ)
    (hRow : ∀ w : UnitSphere,∀ j : I,∑ i : I,w.val i*coefficientValue 2 (F i j) w.val=q w*w.val j) :
    (∀ j : I,coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (tangentCoefficientJet F j)))=0) ∧
      (∀ j : I,oneBoundaryCoefficientMulL (tangentCoefficientJet F j)=0) := by
  have hVal (j : I) (w : UnitSphere) : coefficientValue 2 (tangentCoefficientJet F j) w.val=0 := by
    rw [coefficientValue_tangentCoefficientJet]
    exact boundaryTangentCoefficient_of_radial_row F q hRow w j
  constructor
  · intro j
    have hFun : smoothSphereValue (coefficientSmoothData (tangentCoefficientJet F j))=0 := by
      apply ContinuousMap.ext
      intro w
      exact hVal j w
    rw [hFun]
    exact coarseScalarMultiplierMapL.map_zero
  · intro j
    exact (oneBoundaryCoefficientMulL_congr_sphere _ (0:SmoothCoefficientJets 2)
      (fun w => by
        have hZero : coefficientValue 2 (0:SmoothCoefficientJets 2) w.val=0 := by
          have hh := congrFun (coefficientValue_smul 2 (0:ℝ) (0:SmoothCoefficientJets 2)) w.val
          simpa only [zero_smul,Pi.smul_apply,smul_eq_mul,zero_mul] using hh
        exact (hVal j w).trans hZero.symm)).trans oneBoundaryCoefficientMulL_zero

lemma radial_row_tangential_operators_zero (F : SmoothCoefficientMatrix 2) (q : UnitSphere → ℝ)
    (hRow : ∀ w : UnitSphere,∀ j : I,∑ i : I,w.val i*coefficientValue 2 (F i j) w.val=q w*w.val j) :
    coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)=0 ∧
      adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)=0 := by
  obtain ⟨h0,h1⟩ := radial_row_tangent_multipliers_zero F q hRow
  constructor
  · simp only [coarseBoundaryTangentialL,h0,ContinuousLinearMap.zero_comp,Finset.sum_const_zero]
  · simp only [adjointBoundaryTangentialL,h1,ContinuousLinearMap.comp_zero,neg_zero,Finset.sum_const_zero]
end ShrinkingSpheres
