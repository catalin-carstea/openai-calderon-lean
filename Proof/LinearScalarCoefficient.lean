import Proof.CoordinateScalarSmoothJets
import Proof.FrameDuality
import Proof.Archive.ClosedCoefficientJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

def linearScalarSmoothCoefficient (Q : SmoothCoefficientJets 2) (ell : X →L[ℝ] ℝ) : SmoothCoefficientJets 3 :=
  ∑ i : I,ell (axis i) • coordinateScalarSmoothJet Q i

def linearScalarClosedCoefficientL (Q : SmoothCoefficientJets 2) :
    (X →L[ℝ] ℝ) →L[ℝ] ClosedCoefficientJets 3 :=
  ∑ i : I,(ContinuousLinearMap.apply ℝ ℝ (axis i)).smulRight
    (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q i))

lemma linearScalarClosedCoefficientL_eq_closure (Q : SmoothCoefficientJets 2) (ell : X →L[ℝ] ℝ) :
    linearScalarClosedCoefficientL Q ell=smoothCoefficientClosureInclusionL 3 (linearScalarSmoothCoefficient Q ell) := by
  simp only [linearScalarClosedCoefficientL,linearScalarSmoothCoefficient,_root_.sum_apply,
    ContinuousLinearMap.smulRight_apply,map_sum,map_smul]
  rfl

lemma linearScalarSmoothCoefficient_value (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (ell : X →L[ℝ] ℝ) (w : UnitSphere) : coefficientValue 3 (linearScalarSmoothCoefficient Q ell) w.val=ell w.val := by
  have hAxis := linear_axis_expansion ell w.val
  simp only [I,Fin.sum_univ_three] at hAxis
  simp only [linearScalarSmoothCoefficient,I,Fin.sum_univ_three,coefficientValue_add,Pi.add_apply,
    coefficientValue_smul,Pi.smul_apply,smul_eq_mul,coordinateScalarSmoothJet_value Q hQ]
  nlinarith only [hAxis]
end ShrinkingSpheres
