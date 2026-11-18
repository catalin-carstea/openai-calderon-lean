import Proof.ParallelNormAssemblyReservedModelLeadingIdentity
import Proof.ParallelNormAssemblyReservedModelCoreSplit
import Proof.ParallelNormAssemblyReservedModelPairTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

variable {Y : Set X} {d : Data} {CF CT CG CK : ℝ}

def modelPotentialCubicCoreDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ := by
  classical
  exact if hy : y ∈ Y then metricDensity d.γ y*∑ i : I,
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfSectionCovariantDerivativeL d U y (d.frame y i)))
      (cubicWordAdjointCommutatorValue P (W y hy) (.inr (.inl i)) (PhysicalPrincipalData.potentialWordCoefficient d y)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))) else 0

/-- Exact actual model-leading identity, with ALL frame contraction done
before the coordinate Green formula. The transposed cubic source uses
only the H1/2 horizontal endpoint needed by the frozen energy. -/
theorem model_potential_leading_core_weak_identity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    modelPotentialLeadingCoreDensity P W U y=
      4*((∑ k : I,∑ c : I,quadraticHigherPairDensity d (modelPotentialLeadingWeight d k c)
        (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inl c))) P.potentialQuadraticHalfL U (axis k) y)-
        modelPotentialCubicCoreDensity P W U y) := by
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let C := P.potentialQuadraticHalfL y
  let A := fun i : I => sphereSobolevDualPairing (1/2:ℝ)
    (flatThreeHalfRaisingL i (fiveHalfSectionCovariantDerivativeL d U y (d.frame y i))) (C u)+
    sphereSobolevDualPairing (1/2:ℝ) (flatThreeHalfRaisingL i u)
      (C (fiveHalfSectionCovariantDerivativeL d U y (d.frame y i)))
  let B := fun i : I => sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfSectionCovariantDerivativeL d U y (d.frame y i)))
    (cubicWordAdjointCommutatorValue P (W y hy) (.inr (.inl i)) (PhysicalPrincipalData.potentialWordCoefficient d y) u)
  have hFlat (i : I) :
      ⟪flatRaisingSobolevL 1 i (highSectionCovariantDerivative d (fiveHalfToTwoSection U) y (d.frame y i)),
        P.potentialQuadraticCoreL (W y hy) (U y)⟫_ℝ+
      ⟪flatLoweringSobolevL 1 i (highSectionCovariantDerivative d (fiveHalfToTwoSection U) y (d.frame y i)),
        P.potentialQuadraticAdjointCoreL (W y hy) (U y)⟫_ℝ=A i-B i := by
    have hh := flat_model_potential_leading_pair P hy (W y hy) Q hQ i (U y)
      (fiveHalfCovariantDerivative d U (d.frame y i) y)
    rw [fiveHalfCovariantDerivative_inclusion d U y (d.frame y i) hU] at hh
    simpa only [five_half_covariant_derivative_reserved_eq,u,A,B,C] using hh
  have hTrace := model_potential_paired_frame_trace d y hFrame C u (scalarModelFirstDerivativeLinear d U y)
  simp only [scalarModelFirstDerivativeLinear_apply,five_half_covariant_derivative_reserved_eq] at hTrace
  have hMain : metricDensity d.γ y*(∑ i : I,A i)=
      ∑ k : I,∑ c : I,quadraticHigherPairDensity d (modelPotentialLeadingWeight d k c)
        (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inl c))) P.potentialQuadraticHalfL U (axis k) y := by
    rw [show (∑ i : I,A i)=_ from hTrace]
    simp only [Finset.mul_sum,quadraticHigherPairDensity,modelPotentialLeadingWeight,
      normalizedPotentialGeneratorHigh,potentialGeneratorWeight,potentialCoordinateGeneratorHigh,inv_one,one_smul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro c _
    dsimp only [u,C]
    ring
  simp only [modelPotentialLeadingCoreDensity,PhysicalPrincipalData.potentialQuadraticCoreSection,
    PhysicalPrincipalData.potentialQuadraticAdjointCoreSection,dite_eq_left hy,hFlat,
    Finset.sum_sub_distrib,modelPotentialCubicCoreDensity]
  change 4*metricDensity d.γ y*((∑ i : I,A i)-(∑ i : I,B i))=
    4*((∑ k : I,∑ c : I,quadraticHigherPairDensity d (modelPotentialLeadingWeight d k c)
      (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inl c))) P.potentialQuadraticHalfL U (axis k) y)-
      metricDensity d.γ y*(∑ i : I,B i))
  rw [←hMain]
  ring

end ShrinkingSpheres.ParallelEnergy
