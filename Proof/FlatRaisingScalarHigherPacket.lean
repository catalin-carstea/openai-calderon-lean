import Proof.NativeScalarBoundedHigherData
import Proof.FlatRaisingScalarPacket
import Proof.FirstErrorScalarAngularBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def flatRaisingScalarAngularCoefficients (Q0 : SmoothCoefficientJets 2) (k : I) :
    TaylorGeneratorIndex → I × I → ClosedCoefficientJets 3
  | .taylor,_ => 0
  | .degree,ij => coordinateScalarAngularTemplate Q0 k ij.1 ij.2
  | .rotation a b,ij => if b=k then -(coordinateScalarAngularTemplate Q0 a ij.1 ij.2) else 0

lemma flatRaisingScalarAngularCoefficients_half (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (k : I) (a : TaylorGeneratorIndex) (i j : I) :
    closedThreeJetHalfBoundaryScalarMultiplierL (flatRaisingScalarAngularCoefficients Q0 k a (i,j))=
      closedCoefficientAngularHalfL i j (flatRaisingScalarCoefficients Q0 k a) := by
  cases a with
  | taylor => simp only [flatRaisingScalarAngularCoefficients,flatRaisingScalarCoefficients,ContinuousLinearMap.map_zero]
  | degree => exact coordinateScalarAngularTemplate_half Q0 hQ0 k i j
  | rotation a b =>
    by_cases hb : b=k
    · simp only [flatRaisingScalarAngularCoefficients,flatRaisingScalarCoefficients,hb,ite_true,ContinuousLinearMap.map_neg,
        coordinateScalarAngularTemplate_half Q0 hQ0]
    · simp only [flatRaisingScalarAngularCoefficients,flatRaisingScalarCoefficients,hb,ite_false,ContinuousLinearMap.map_zero]

lemma flatRaisingScalarAngularCoefficients_weighted_bound (Q0 : SmoothCoefficientJets 2)
    (k i j : I) (r : ℝ) :
    (∑ a,taylorGeneratorWeight r a*‖flatRaisingScalarAngularCoefficients Q0 k a (i,j)‖) ≤
      8*firstErrorScalarFixedBudget Q0 := by
  let J := firstErrorScalarFixedBudget Q0
  have hEq : (∑ a,taylorGeneratorWeight r a*‖flatRaisingScalarAngularCoefficients Q0 k a (i,j)‖)=
      ‖coordinateScalarAngularTemplate Q0 k i j‖+∑ a : I,‖coordinateScalarAngularTemplate Q0 a i j‖ := by
    rw [taylorGeneratorIndex_sum]
    simp only [flatRaisingScalarAngularCoefficients,taylorGeneratorWeight,norm_zero,mul_zero,zero_add,one_mul,
      apply_ite,norm_neg,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [hEq]
  have hSum : (∑ a : I,‖coordinateScalarAngularTemplate Q0 a i j‖) ≤ 6*J := by
    calc
      _ ≤ ∑ _a : I,2*J := Finset.sum_le_sum (fun a _ => norm_coordinateScalarAngularTemplate_le Q0 a i j)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  exact (add_le_add (norm_coordinateScalarAngularTemplate_le Q0 k i j) hSum).trans_eq (by ring)

lemma flatRaisingScalarCoefficients_augmented_bound (Q0 : SmoothCoefficientJets 2) (k : I) (r : ℝ) :
    (∑ a,taylorGeneratorWeight r a*(‖flatRaisingScalarCoefficients Q0 k a‖+
      ∑ ij : I × I,‖flatRaisingScalarAngularCoefficients Q0 k a ij‖)) ≤
      76*firstErrorScalarFixedBudget Q0 := by
  let J := firstErrorScalarFixedBudget Q0
  calc
    _ = (∑ a,taylorGeneratorWeight r a*‖flatRaisingScalarCoefficients Q0 k a‖)+
      ∑ ij : I × I,∑ a,taylorGeneratorWeight r a*‖flatRaisingScalarAngularCoefficients Q0 k a ij‖ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    _ ≤ 4*J+∑ _ij : I × I,8*J := add_le_add (flatRaisingScalarCoefficients_weighted_bound Q0 k r)
      (Finset.sum_le_sum (fun ij _ => flatRaisingScalarAngularCoefficients_weighted_bound Q0 k ij.1 ij.2 r))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul];ring

/-- Flat raising has explicit actual angular coefficients and zero genuine
bounded remainders at the higher grade. -/
def NativeTaylorGeneratorBounds.flat_raising_scalar_higher_packet
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (T : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (k : I) :
    NativeScalarBoundedHigherData (T.flat_raising_scalar_packet hF0 Q0 hQ0 k)
      (76*firstErrorScalarFixedBudget Q0) := by
  refine { angular := flatRaisingScalarAngularCoefficients Q0 k
           angular_half := fun a i j => flatRaisingScalarAngularCoefficients_half Q0 hQ0 k a i j
           augmented_bound := ?_
           boundedHigher := 0
           boundedAdjointHigher := 0
           boundedHigher_pair := ?_
           boundedAdjointHigher_pair := ?_
           higher_bounds := ?_ }
  · simpa only [flat_raising_scalar_packet,mul_one] using flatRaisingScalarCoefficients_augmented_bound Q0 k (d.radius y)
  · simp only [flat_raising_scalar_packet,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  · simp only [flat_raising_scalar_packet,LinearIsometryEquiv.map_zero,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  · simp only [norm_zero,zero_mul,le_refl,and_self]
end ShrinkingSpheres
