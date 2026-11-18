import Proof.FlatRaisingSobolev
import Proof.Archive.SphereSobolevBesselOrderCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.HarmonicDerivativeOperator
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma norm_sphereSobolevShiftedDegreeL_le_two (s : ℝ) : ‖sphereSobolevShiftedDegreeL s‖ ≤ 2 := by
  have hB : ‖(sphereSobolevBesselEquiv s 1).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    change ‖sphereSobolevBesselEquiv s 1 u‖ ≤ 1*‖u‖
    rw [LinearIsometryEquiv.norm_map,one_mul]
  exact (norm_sub_le _ _).trans ((add_le_add hB (norm_sphereSobolevInclusionL_le s (s-1) (by linarith))).trans_eq (by norm_num))

lemma norm_flatRaisingSobolevL_le (s : ℝ) (i : I) :
    ‖flatRaisingSobolevL s i‖ ≤ 10*radialDriftSobolevBound (-s) := by
  have hD := norm_sphereSobolevShiftedDegreeL_le_two s
  have hI := norm_sphereSobolevInclusionL_le s (s-1) (by linarith)
  have hA : ‖(-2:ℝ) • sphereSobolevShiftedDegreeL s-sphereSobolevInclusionL s (s-1) (by linarith)‖ ≤ 5 := by
    exact (norm_sub_le _ _).trans (by rw [norm_smul];norm_num;linarith)
  have hB : ‖radialCorrectionAdjointSobolevL s (EuclideanSpace.proj (𝕜:=ℝ) i)‖ ≤ 2*radialDriftSobolevBound (-s) := by
    have hSum : (∑ j : I,|axis i j|)=1 := by
      have hAbs (j : I) : |axis i j|=if i=j then 1 else 0 := by
        by_cases hij : i=j <;> simp [axis,hij,eq_comm]
      simp_rw [hAbs]
      simp
    have hh := norm_sphereSobolevRadialDriftAdjointL_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics s (axis i)
    change ‖OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRadialDriftAdjointL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics s (radialCorrectionVector (EuclideanSpace.proj (𝕜:=ℝ) i))‖ ≤ _
    rw [radialCorrectionVector_proj]
    simpa only [hSum,mul_one] using hh
  have hR : 0 ≤ radialDriftSobolevBound (-s) := (zero_le_one.trans (le_max_left _ _))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hA hB (norm_nonneg _) (by norm_num)).trans_eq (by ring))

/-- Pure double raising cancels on the full Sobolev core at every order. -/
lemma flatRaisingSobolevL_contracted_double_zero (s : ℝ) :
    (∑ i : I,(flatRaisingSobolevL (s-1) i).comp (flatRaisingSobolevL s i))=0 := by
  apply sphereSobolev_clm_eq_of_single s
  intro k a
  simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,flatRaisingSobolevL_single,_root_.zero_apply]
  have hZero : (∑ i : I,harmonicDerivativeAdjoint sphereFischerInner (k+1) i
      (harmonicDerivativeAdjoint sphereFischerInner k i a))=0 := by
    apply Subtype.val_injective
    simpa only [Submodule.coe_sum,Submodule.coe_zero] using sum_double_harmonicDerivativeAdjoint_zero k a
  have hh := congrArg (sphereSobolevSingleL ((s-1)-1) ((k+1)+1)) hZero
  simpa only [map_sum,map_zero] using hh
end ShrinkingSpheres
