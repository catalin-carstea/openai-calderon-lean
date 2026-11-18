import Proof.FlatRaisingSobolev

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.HarmonicDerivativeOperator

/-- Genuine lowering at every Sobolev index, constructed from the
supplied harmonic radial drift rather than equality of carrier types. -/
def flatLoweringSobolevL (s : ℝ) (i : I) : SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  ((-2:ℝ) • sphereSobolevShiftedDegreeL s-(3:ℝ) • sphereSobolevInclusionL s (s-1) (by linarith)).comp
    (radialCorrectionSobolevL s (EuclideanSpace.proj (𝕜:=ℝ) i))

lemma radialDriftBlock_axis (i : I) (k : ℕ) (a : harmonicSphereSubspace (k+1)) :
    radialDriftBlockL sphereFischerInner (axis i) k a=
      (-(2*((k+1:ℕ):ℝ)+1)⁻¹) • harmonicDerivative sphereFischerInner k i a := by
  simp [radialDriftBlockL,axis,PiLp.single_apply,eq_comm]

lemma flatLoweringSobolevL_single_succ (s : ℝ) (i : I) (k : ℕ) (a : harmonicSphereSubspace (k+1)) :
    flatLoweringSobolevL s i (sphereSobolevSingleL s (k+1) a)=
      sphereSobolevSingleL (s-1) k (harmonicDerivative sphereFischerInner k i a) := by
  simp only [flatLoweringSobolevL,ContinuousLinearMap.comp_apply,_root_.sub_apply,_root_.smul_apply,
    radialCorrectionSobolevL_single,radialCorrectionVector_proj,radialDriftBlock_axis,map_smul,
    sphereSobolevShiftedDegreeL_single,sphereSobolevInclusionL_single,smul_smul]
  have hPos : (2*((k+1:ℕ):ℝ)+1) ≠ 0 := by positivity
  rw [←sub_smul,smul_smul]
  have hScalar : (-(2*((k+1:ℕ):ℝ)+1)⁻¹)*((-2:ℝ)*(k:ℝ)-3)=1 := by
    push_cast
    field_simp
    ring
  rw [hScalar,one_smul]

lemma flatLoweringSobolevL_single_zero (s : ℝ) (i : I) (a : harmonicSphereSubspace 0) :
    flatLoweringSobolevL s i (sphereSobolevSingleL s 0 a)=0 := by
  simp only [flatLoweringSobolevL,ContinuousLinearMap.comp_apply,radialCorrectionSobolevL_constant,map_zero]

lemma flatLoweringSobolevL_inclusion (s t : ℝ) (hts : t ≤ s) (i : I) :
    (flatLoweringSobolevL t i).comp (sphereSobolevInclusionL s t hts)=
      (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (flatLoweringSobolevL s i) := by
  apply sphereSobolev_clm_eq_of_single s
  intro k a
  cases k with
  | zero => simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single,
      flatLoweringSobolevL_single_zero,map_zero]
  | succ k => simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single,flatLoweringSobolevL_single_succ]

lemma flatLoweringSobolevL_one (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (i : I) :
    flatLoweringSobolevL 1 i=boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k a
  cases k with
  | zero => rw [flatLoweringSobolevL_single_zero,coordinateBoundaryGradientL_single_zero Q hQ]
  | succ k =>
    rw [flatLoweringSobolevL_single_succ,coordinateBoundaryGradientL_single_succ Q hQ,zeroEquiv_harmonic_subtype]
    unfold sphereSobolevSingleL
    congr 2
    norm_num

lemma flat_raising_lowering_inner (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (u v : SphereSobolev 1) :
    ⟪flatRaisingSobolevL 1 i u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,flatLoweringSobolevL 1 i v⟫_ℝ := by
  rw [flatRaisingSobolevL_one Q hQ,flatLoweringSobolevL_one Q hQ]
  have hh := boundaryGradientL_adjoint (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL
    sphereSobolevDegreeL sphereSobolevDegreeL_symmetric v u
  calc
    _ = ⟪sphereSobolevInclusionL 1 0 (by norm_num) v,
        boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u⟫_ℝ := real_inner_comm _ _
    _ = ⟪boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL v,
        sphereSobolevInclusionL 1 0 (by norm_num) u⟫_ℝ := hh.symm
    _ = _ := real_inner_comm _ _

/-- The exact opposite degree shift of lowering, on its genuine graded
common domain. -/
lemma degree_flatLoweringSobolev_commutator (s : ℝ) (i : I) :
    (sphereSobolevShiftedDegreeL (s-1)).comp (flatLoweringSobolevL s i)-
      (flatLoweringSobolevL (s-1) i).comp (sphereSobolevShiftedDegreeL s)=
    -(sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)).comp (flatLoweringSobolevL s i) := by
  apply sphereSobolev_clm_eq_of_single s
  intro k a
  cases k with
  | zero => simp only [_root_.sub_apply,ContinuousLinearMap.comp_apply,flatLoweringSobolevL_single_zero,
      sphereSobolevShiftedDegreeL_single,Nat.cast_zero,zero_smul,map_zero,sub_zero,_root_.neg_apply,neg_zero]
  | succ k =>
    simp only [_root_.sub_apply,ContinuousLinearMap.comp_apply,flatLoweringSobolevL_single_succ,
      sphereSobolevShiftedDegreeL_single,map_smul,sphereSobolevInclusionL_single,Nat.cast_add,Nat.cast_one,
      _root_.neg_apply]
    rw [add_smul,one_smul]
    abel

end ShrinkingSpheres
