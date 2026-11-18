import Proof.NativeTaylorGeneratorSystem
import Proof.ClosedCoordinateCoefficientProduct
import Proof.NativeFirstErrorGeneratorForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def taylorGeneratorIndexEquiv : TaylorGeneratorIndex ≃ Unit ⊕ (Unit ⊕ (I×I)) where
  toFun
    | .taylor => .inl ()
    | .degree => .inr (.inl ())
    | .rotation i j => .inr (.inr (i,j))
  invFun
    | .inl _ => .taylor
    | .inr (.inl _) => .degree
    | .inr (.inr ij) => .rotation ij.1 ij.2
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨⟨⟩⟩ | ⟨⟨⟨⟩⟩ | ⟨i,j⟩⟩ <;> rfl

lemma taylorGeneratorIndex_sum {E : Type*} [AddCommMonoid E] (f : TaylorGeneratorIndex → E) :
    ∑ a,f a=f .taylor+f .degree+∑ i : I,∑ j : I,f (.rotation i j) := by
  calc
    _ = ∑ a : Unit ⊕ (Unit ⊕ (I×I)),f (taylorGeneratorIndexEquiv.symm a) :=
      Fintype.sum_equiv taylorGeneratorIndexEquiv _ _ (fun a => by rw [Equiv.symm_apply_apply])
    _ = _ := by
      simp only [Fintype.sum_sum_type,Fintype.sum_unique,Fintype.sum_prod_type,taylorGeneratorIndexEquiv]
      exact (add_assoc _ _ _).symm

def firstErrorScalarCoefficients (Q0 : SmoothCoefficientJets 2) (α b : ℝ) (v : I → ℝ)
    (Q : I → ClosedCoefficientJets 3) : TaylorGeneratorIndex → ClosedCoefficientJets 3
  | .taylor => α • (∑ j : I,v j • smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j))+
      b • closedUnitCoefficient Q0+α • (∑ j : I,closedCoordinateCoefficientProductL Q0 j (Q j))
  | .degree => α • (∑ j : I,closedCoordinateCoefficientProductL Q0 j (Q j))
  | .rotation i j => (-α) • closedCoordinateCoefficientProductL Q0 i (Q j)

def taylorGeneratorCoarse (P : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    TaylorGeneratorIndex → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  | .taylor => P
  | .degree => sphereSobolevDegreeL
  | .rotation i j => sphereSobolevRotationL 1 i j

lemma closedVectorNormalMultiplier_coordinate_product (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (Q : I → ClosedCoefficientJets 3) :
    closedOneBoundaryScalarMultiplierL (∑ j : I,closedCoordinateCoefficientProductL Q0 j (Q j))=
      closedVectorNormalMultiplier Q := by
  have hSum := map_sum closedOneBoundaryScalarMultiplierL.toLinearMap.toAddMonoidHom
    (fun j : I => closedCoordinateCoefficientProductL Q0 j (Q j)) Finset.univ
  change closedOneBoundaryScalarMultiplierL (∑ j : I,closedCoordinateCoefficientProductL Q0 j (Q j))=
    ∑ j : I,closedOneBoundaryScalarMultiplierL (closedCoordinateCoefficientProductL Q0 j (Q j)) at hSum
  rw [hSum]
  simp only [closedCoordinateCoefficientProduct_one Q0 hQ0,closedVectorNormalMultiplier]
  rfl

lemma firstErrorScalarCoefficients_coarse_form (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (P : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (α b : ℝ) (v : I → ℝ)
    (Q : I → ClosedCoefficientJets 3) :
    (∑ a,(taylorGeneratorCoarse P a).comp
      (closedOneBoundaryScalarMultiplierL (firstErrorScalarCoefficients Q0 α b v Q a)))=
      P.comp (α • (∑ j : I,v j • coordinateMultiplierSobolevL 1 j)+
        b • ContinuousLinearMap.id ℝ (SphereSobolev 1)+α • closedVectorNormalMultiplier Q)+
      α • (closedVectorTangentialAdjoint Q+sphereSobolevDegreeL.comp (closedVectorNormalMultiplier Q)) := by
  rw [taylorGeneratorIndex_sum]
  have hCoord (j : I) : closedOneBoundaryScalarMultiplierL
      (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j))=coordinateMultiplierSobolevL 1 j := by
    rw [closedOneBoundaryScalarMultiplierL_on_smooth]
    simpa only [one_smul] using coordinateScalarSmoothJet_one_multiplier Q0 hQ0 j 1
  simp only [firstErrorScalarCoefficients,taylorGeneratorCoarse,map_add,map_smul,map_sum,hCoord,
    closedUnitCoefficient_one Q0 hQ0,closedVectorNormalMultiplier_coordinate_product Q0 hQ0,
    closedCoordinateCoefficientProduct_one Q0 hQ0]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.smul_apply,_root_.sum_apply,
    map_add,map_smul,map_sum,closedVectorTangentialAdjoint,_root_.neg_apply]
  simp only [← Finset.smul_sum,smul_add]
  simp only [oneSphereCoordinateMulL,coordinateMultiplierSobolevL,axis,Finset.sum_neg_distrib,smul_neg,neg_smul]
  rw [Finset.sum_comm]
  module
end ShrinkingSpheres
