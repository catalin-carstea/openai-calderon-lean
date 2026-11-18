import Proof.ParallelModelFirstRaisingBudget
import Proof.ParallelNormAssemblyReservedHigherGreen

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.PrincipalCommutator

def modelFirstShiftedDegreeLow : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  degreeHalfL-sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)

def modelFirstShiftedDegreeHigh : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  degreeHigherL-sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)

lemma modelFirstShiftedDegree_balanced :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp modelFirstShiftedDegreeHigh=
      modelFirstShiftedDegreeLow.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [modelFirstShiftedDegreeHigh,modelFirstShiftedDegreeLow,ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp,degreeHalf_balanced]

lemma modelFirstShiftedDegree_lift (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (scalarModelShiftedDegreeSection (fun _ : X => u) 0)=
      modelFirstShiftedDegreeHigh (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  simp only [scalarModelShiftedDegreeSection,map_sub,scalarModelDegreeSection_half_inclusion,
    modelFirstShiftedDegreeHigh,_root_.sub_apply,sphereSobolevInclusionL_trans_apply]

lemma model_first_inclusion_half_covariant_zero (d : Data) (y a : X) :
    halfOperatorCovariantDerivativeL d
      (fun _ => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (fun _ => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) y a=0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hC := DFunLike.congr_fun (frameAngularConnectionHigherL_compatible d y a) u
  simp only [halfOperatorCovariantDerivativeL,directionalFDeriv,fderiv_const_apply,
    _root_.zero_apply,ContinuousLinearMap.comp_apply,_root_.sub_apply,_root_.add_apply] at hC ⊢
  rw [hC]
  module

lemma model_first_shifted_degree_half_covariant_zero (d : Data) (y a : X) :
    halfOperatorCovariantDerivativeL d (fun _ => modelFirstShiftedDegreeLow)
      (fun _ => modelFirstShiftedDegreeHigh) y a=0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hD := DFunLike.congr_fun (degreeHalf_covariant_derivative_zero d y a) u
  have hI := DFunLike.congr_fun (model_first_inclusion_half_covariant_zero d y a) u
  simp only [halfOperatorCovariantDerivativeL,modelFirstShiftedDegreeLow,modelFirstShiftedDegreeHigh,
    directionalFDeriv,fderiv_const_apply,_root_.zero_apply,ContinuousLinearMap.comp_apply,
    _root_.sub_apply,_root_.add_apply,map_sub] at hD hI ⊢
  have hh := congrArg₂ (fun x z : SphereSobolev (-(1/2:ℝ)) => x-z) hD hI
  convert hh using 1 <;> module

lemma model_first_shifted_degree_higher_covariant_zero (d : Data) (y a : X) :
    higherOperatorCovariantDerivativeL d (fun _ => modelFirstShiftedDegreeHigh) y a=0 := by
  rw [higher_covariant_derivative_eq_half d (fun _ => modelFirstShiftedDegreeLow)
    (fun _ => modelFirstShiftedDegreeHigh) y a contDiffAt_const contDiffAt_const
    (Eventually.of_forall (fun _ => modelFirstShiftedDegree_balanced)),
    model_first_shifted_degree_half_covariant_zero,ContinuousLinearMap.zero_comp]

def modelFirstZeroAdjointWeakL (d : Data) (c : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (framedRaisingHalfL d y (axis c)).adjoint.comp modelFirstShiftedDegreeHigh

def modelFirstZeroAdjointWeakJet (d : Data) (c i : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (framedRaisingFirstHalfJet d i c y).adjoint.comp modelFirstShiftedDegreeHigh

/-- Genuine first covariant graph of the exact zero model R†(D−I).
The shifted degree is parallel and the arbitrary frame derivatives cancel
in the SAME background raising covariant jet. -/
theorem model_first_zero_adjoint_weak_jet_graph
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y : X} (hy : y ∈ Y) (c i : I) :
    quadraticOperatorCovariantDerivativeL d (modelFirstZeroAdjointWeakL d c) y (axis i)=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        ((modelFirstZeroAdjointWeakJet d c i y).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) := by
  let R := fun x => framedRaisingHalfL d x (axis c)
  let RA := scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c
  have hRS := ((hd.framedRaisingHalf_smooth (axis c)).1).contDiffAt (hY.mem_nhds hy)
  have hAS := (scalarModelRaisingAdjoint_smooth hd c).contDiffAt (hY.mem_nhds hy)
  have hDL := half_covariant_adjoint_strong_extension d R (fun x => framedRaisingHigherL d x (axis c)) RA hRS
    (axis i) (framedRaisingHalf_balanced d y (axis c))
    (scalarModelRaisingAdjointHigher_balanced modelFirstFlatAdjointHigher d c y modelFirstFlatAdjointHigher_graph)
    (framedRaisingFirstHalfJet d i c y) (framed_raising_strong_half_graph hY hΩ hd hK hy i c)
  have hDH : higherOperatorCovariantDerivativeL d (fun _ => modelFirstShiftedDegreeHigh) y (axis i)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        ((0 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) := by
    rw [model_first_shifted_degree_higher_covariant_zero,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero]
  apply ContinuousLinearMap.ext
  intro u
  have hRaw := quadratic_covariant_product_rule d (fun x => (R x).adjoint) RA
    (fun _ => modelFirstShiftedDegreeHigh) y (axis i) hAS contDiffAt_const
    (framedRaisingFirstHalfJet d i c y).adjoint 0
    (scalarModelRaisingAdjointHigher_balanced modelFirstFlatAdjointHigher d c y modelFirstFlatAdjointHigher_graph)
    hDL hDH u (scalarModelShiftedDegreeSection (fun _ : X => u) 0) (modelFirstShiftedDegree_lift u)
  change quadraticOperatorCovariantDerivativeL d
    (fun x => (framedRaisingHalfL d x (axis c)).adjoint.comp modelFirstShiftedDegreeHigh) y (axis i) u=_
  simpa only [modelFirstZeroAdjointWeakL,modelFirstZeroAdjointWeakJet,R,ContinuousLinearMap.comp_zero,add_zero,
    ContinuousLinearMap.comp_apply] using hRaw

end ShrinkingSpheres.ParallelEnergy
