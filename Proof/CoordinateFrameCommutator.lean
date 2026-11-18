import Proof.FirstAdjointCorrectionDegreeCommutator
import Proof.RadialCorrectionFrameCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem frameAngularLinear_axis_component (A : I → I → ℝ) (j i : I) :
    frameAngularLinear A (axis j) i = -A j i := by
  simp [frameAngularLinear_apply,frameAngularVector,axis,Pi.single_apply]

theorem projection_frameAngularLinear (A : I → I → ℝ) (hA : ∀ i j,A i j = -A j i) (i : I) :
    (EuclideanSpace.proj (𝕜:=ℝ) i).comp (frameAngularLinear A) =
      ∑ j : I,A i j • EuclideanSpace.proj (𝕜:=ℝ) j := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,PiLp.proj_apply,smul_eq_mul]
  have h := linear_axis_expansion ((EuclideanSpace.proj (𝕜:=ℝ) i).comp (frameAngularLinear A)) z
  simp only [ContinuousLinearMap.comp_apply,PiLp.proj_apply,frameAngularLinear_axis_component] at h
  apply h.trans
  apply Finset.sum_congr rfl
  intro j _
  have hRow : -A j i = A i j := by linarith only [hA j i]
  rw [hRow]
  ring

theorem coordinateMultiplier_frame_row (A : I → I → ℝ) (hA : ∀ i j,A i j = -A j i) (i : I) :
    -radialCorrectionCovectorL ((EuclideanSpace.proj (𝕜:=ℝ) i).comp (frameAngularLinear A))-
      (radialCorrectionCovectorL ((EuclideanSpace.proj (𝕜:=ℝ) i).comp (frameAngularLinear A))).adjoint =
        ∑ j : I,A i j • coordinateMultiplierSobolevL 0 j := by
  have hF := congrArg radialCorrectionCovectorL (projection_frameAngularLinear A hA i)
  simp only [map_sum,map_smul] at hF
  let Adj : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
      (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap
  have hAdj := congrArg Adj hF
  simp only [map_sum,map_smul] at hAdj
  have hBoth := congrArg₂ (fun x y : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => -x-y) hF hAdj
  apply hBoth.trans
  simp only [coordinateMultiplierSobolevL_radial,radialCorrectionSobolevL_zero,
    radialCorrectionAdjointSobolevL_zero,smul_sub,smul_neg,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  rfl

/-- Coordinate multiplication transforms as a frame vector under the actual
    angular connection. Its size is unrestricted and cancels covariantly. -/
theorem angularConnection_coordinateMultiplier_commutator
    (A : I → I → ℝ) (hA : ∀ i j,A i j = -A j i) (i : I) :
    (angularConnectionL A).comp (coordinateMultiplierSobolevL 1 i)-
      (coordinateMultiplierSobolevL 0 i).comp (angularConnectionL A) =
        (∑ j : I,A i j • coordinateMultiplierSobolevL 0 j).comp
          (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  let q := EuclideanSpace.proj (𝕜:=ℝ) i
  let L := angularConnectionL A
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hR := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
    (angularConnection_radialCorrection_commutator A hA q)
  have hB := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
    (angularConnection_radialCorrectionAdjoint_commutator A hA q)
  change L (radialCorrectionSobolevL 1 q u)-radialCorrectionCovectorL q (L u) =
    radialCorrectionCovectorL (q.comp (frameAngularLinear A)) (I0 u) at hR
  change L (radialCorrectionAdjointSobolevL 1 q u)-(radialCorrectionCovectorL q).adjoint (L u) =
    (radialCorrectionCovectorL (q.comp (frameAngularLinear A))).adjoint (I0 u) at hB
  have hR' := sub_eq_iff_eq_add.mp hR
  have hB' := sub_eq_iff_eq_add.mp hB
  have hM1 : coordinateMultiplierSobolevL 1 i u =
      -(radialCorrectionSobolevL 1 q u)-radialCorrectionAdjointSobolevL 1 q u := by
    simp only [coordinateMultiplierSobolevL_radial,_root_.sub_apply,_root_.neg_apply,q]
  have hM0 : coordinateMultiplierSobolevL 0 i (L u) =
      -(radialCorrectionCovectorL q (L u))-(radialCorrectionCovectorL q).adjoint (L u) := by
    simp only [coordinateMultiplierSobolevL_radial,radialCorrectionSobolevL_zero,
      radialCorrectionAdjointSobolevL_zero,_root_.sub_apply,_root_.neg_apply,q]
  have hL : L (coordinateMultiplierSobolevL 1 i u) =
      -(L (radialCorrectionSobolevL 1 q u))-L (radialCorrectionAdjointSobolevL 1 q u) :=
    (congrArg L hM1).trans (by simp only [map_sub,map_neg])
  have hLeft := congrArg₂ (fun x y : SphereSobolev 0 => x-y) hL hM0
  have hSub := congrArg₂ (fun x y : SphereSobolev 0 => -x-y-
    (-(radialCorrectionCovectorL q (L u))-(radialCorrectionCovectorL q).adjoint (L u))) hR' hB'
  have hMiddle : -(L (radialCorrectionSobolevL 1 q u))-L (radialCorrectionAdjointSobolevL 1 q u)-
      (-(radialCorrectionCovectorL q (L u))-(radialCorrectionCovectorL q).adjoint (L u)) =
      -(radialCorrectionCovectorL (q.comp (frameAngularLinear A)) (I0 u))-
        (radialCorrectionCovectorL (q.comp (frameAngularLinear A))).adjoint (I0 u) :=
    hSub.trans (by abel)
  have hRow := congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T (I0 u))
    (coordinateMultiplier_frame_row A hA i)
  simp only [_root_.sub_apply,_root_.neg_apply] at hRow
  exact hLeft.trans (hMiddle.trans hRow)

end ShrinkingSpheres
