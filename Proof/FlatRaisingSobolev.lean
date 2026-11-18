import Proof.FirstAdjointCorrectionDegreeCommutator
import Proof.FlatRaisingCancellation
import Proof.Archive.SphereSobolevShiftedPhysicalDegree
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.HarmonicDerivativeOperator

/-- Raising on every Sobolev level is obtained from the genuine adjoint
    radial drift and the physical degree operator, with its actual order loss. -/
def flatRaisingSobolevL (s : ℝ) (i : I) : SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  ((-2:ℝ) • sphereSobolevShiftedDegreeL s-sphereSobolevInclusionL s (s-1) (by linarith)).comp
    (radialCorrectionAdjointSobolevL s (EuclideanSpace.proj (𝕜:=ℝ) i))

lemma radialDriftAdjointBlock_axis (i : I) (k : ℕ) (a : harmonicSphereSubspace k) :
    radialDriftAdjointBlockL sphereFischerInner (axis i) k a=
      (-(2*((k+1:ℕ):ℝ)+1)⁻¹) • harmonicDerivativeAdjoint sphereFischerInner k i a := by
  rw [radialDriftAdjointBlockL_eq]
  simp [axis,PiLp.single_apply,eq_comm]

lemma flatRaisingSobolevL_single (s : ℝ) (i : I) (k : ℕ) (a : harmonicSphereSubspace k) :
    flatRaisingSobolevL s i (sphereSobolevSingleL s k a)=
      sphereSobolevSingleL (s-1) (k+1) (harmonicDerivativeAdjoint sphereFischerInner k i a) := by
  simp only [flatRaisingSobolevL,ContinuousLinearMap.comp_apply,_root_.sub_apply,_root_.smul_apply,
    radialCorrectionAdjointSobolevL_single,radialCorrectionVector_proj,radialDriftAdjointBlock_axis,
    map_smul,sphereSobolevShiftedDegreeL_single,sphereSobolevInclusionL_single,smul_smul]
  have hPos : (2*((k+1:ℕ):ℝ)+1) ≠ 0 := by positivity
  have hSub (a : ℝ) (v : SphereSobolev (s-1)) : a • v-v=(a-1) • v := by
    rw [sub_smul,one_smul]
  rw [hSub,smul_smul]
  have hScalar : (-(2*((k+1:ℕ):ℝ)+1)⁻¹)*((-2:ℝ)*((k+1:ℕ):ℝ)-1)=1 := by
    field_simp
    ring
  rw [hScalar,one_smul]

lemma flatRaisingSobolevL_inclusion (s t : ℝ) (hts : t ≤ s) (i : I) :
    (flatRaisingSobolevL t i).comp (sphereSobolevInclusionL s t hts)=
      (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (flatRaisingSobolevL s i) := by
  apply sphereSobolev_clm_eq_of_single s
  intro k a
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single,flatRaisingSobolevL_single]

lemma flatRaisingSobolevL_one (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (i : I) :
    flatRaisingSobolevL 1 i=boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k a
  have hNative := flatRaisingSobolevL_single 1 i k a
  have hOrder : sphereSobolevSingleL ((1:ℝ)-1) (k+1) (harmonicDerivativeAdjoint sphereFischerInner k i a)=
      sphereSobolevSingleL 0 (k+1) (harmonicDerivativeAdjoint sphereFischerInner k i a) := by
    unfold sphereSobolevSingleL
    congr 2
    norm_num
  exact hNative.trans (hOrder.trans (coordinateBoundaryGradientAdjointL_single Q hQ i k a).symm)

/-- The manuscript degree shift holds as an actual graded operator identity
    on every Sobolev level, not only on individual harmonic polynomials. -/
lemma degree_flatRaisingSobolev_commutator (s : ℝ) (i : I) :
    (sphereSobolevShiftedDegreeL (s-1)).comp (flatRaisingSobolevL s i)-
      (flatRaisingSobolevL (s-1) i).comp (sphereSobolevShiftedDegreeL s)=
    (sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)).comp (flatRaisingSobolevL s i) := by
  apply sphereSobolev_clm_eq_of_single s
  intro k a
  simp only [_root_.sub_apply,ContinuousLinearMap.comp_apply,flatRaisingSobolevL_single,
    sphereSobolevShiftedDegreeL_single,map_smul,sphereSobolevInclusionL_single,Nat.cast_add,Nat.cast_one]
  rw [add_smul,one_smul]
  abel
end ShrinkingSpheres
