import Proof.FirstAdjointCorrectionHorizontal
import Proof.FlatNormalizedAngularOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.BoundedAngularShift

lemma norm_coordinateBoundaryGradientAdjointL_le_two (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (i : I) :
    ‖boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hEq := coordinateBoundaryGradientAdjointL_normalized Q hQ i u
  calc
    _ = ‖Z.symm (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u)‖ :=
      (Z.symm.norm_map _).symm
    _ = ‖normalizedRaising sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
        (Z.symm (sphereSobolevBesselEquiv 1 1 u))‖ := congrArg norm hEq
    _ ≤ 2*‖Z.symm (sphereSobolevBesselEquiv 1 1 u)‖ :=
      ((normalizedRaising sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_normalizedRaising_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i) (norm_nonneg _))
    _ = 2*‖u‖ := by rw [Z.symm.norm_map,LinearIsometryEquiv.norm_map]

/-- Precisely the two cross terms between the leading r-inverse raising
    operator and the bounded first radial correction. The high and coarse
    corrections are the genuine compatible realizations of the SAME family. -/
def firstCorrectionCrossRemainderL (Q : SmoothCoefficientJets 2) (d : Data) (y : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,((boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL).comp
    (firstFrameAdjointCorrectionSobolevL d y i)+(firstFrameAdjointCorrectionL d y i).comp
      (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL))

lemma Admissible.norm_firstCorrectionCrossRemainderL_le {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {y : X} (hy : y ∈ Y) :
    ‖firstCorrectionCrossRemainderL Q d y‖ ≤ 576*K^2*|M ⟨1,by omega⟩| := by
  let C := K^2*|M ⟨1,by omega⟩|
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hEach (i : I) :
      ‖(boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL).comp
          (firstFrameAdjointCorrectionSobolevL d y i)+(firstFrameAdjointCorrectionL d y i).comp
          (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL)‖ ≤ 192*C := by
    have hA := norm_coordinateBoundaryGradientAdjointL_le_two Q hQ i
    have hF1 := hd.norm_firstFrameAdjointCorrectionSobolevL_le hΩ hm hK hf hε hε1 hy i
    have hF0 := hd.norm_firstFrameAdjointCorrectionL_le hΩ hm hK hf hε hε1 hy i
    calc
      _ ≤ ‖(boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL).comp
            (firstFrameAdjointCorrectionSobolevL d y i)‖+
          ‖(firstFrameAdjointCorrectionL d y i).comp
            (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL)‖ := norm_add_le _ _
      _ ≤ ‖boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL‖*
            ‖firstFrameAdjointCorrectionSobolevL d y i‖+
          ‖firstFrameAdjointCorrectionL d y i‖*
            ‖boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ 2*(84*K^2*|M ⟨1,by omega⟩|)+(12*K^2*|M ⟨1,by omega⟩|)*2 := by gcongr
      _ = _ := by dsimp only [C];ring
  calc
    _ ≤ ∑ i : I,‖(boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL).comp
          (firstFrameAdjointCorrectionSobolevL d y i)+(firstFrameAdjointCorrectionL d y i).comp
          (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I,192*C := Finset.sum_le_sum (fun i _ => hEach i)
    _ = _ := by simp only [Fin.sum_univ_three];dsimp only [C];ring
end ShrinkingSpheres
