import Proof.ActualCovariantRotationGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def coarseSectionCovariantDerivative (d : Data) (U : X → SphereSobolev 0) (y a : X) : SphereSobolev (-1) :=
  sphereSobolevInclusionL 0 (-1) (by norm_num) (fderiv ℝ U y a)-
    ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
      sphereSobolevRotationL 0 i j (U y)

def highSectionCovariantDerivative (d : Data) (U : X → SphereSobolev 2) (y a : X) : SphereSobolev 1 :=
  sphereSobolevInclusionL 2 1 (by norm_num) (fderiv ℝ U y a)-
    ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
      sphereSobolevRotationL 2 i j (U y)

/-- The genuine operator graph implies the covariant Leibniz rule on its
    actual H2 core. Angular connection terms cancel in H(-1); no angular
    coefficient is applied outside its declared domain. -/
theorem CoarseCovariantRotationGraph.apply_section {d : Data} {y a : X}
    {H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {S : SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (hGraph : CoarseCovariantRotationGraph d y a H S)
    (hH : DifferentiableAt ℝ H y) (U : X → SphereSobolev 2) (hU : DifferentiableAt ℝ U y) :
    coarseSectionCovariantDerivative d (fun x => H x (sphereSobolevInclusionL 2 1 (by norm_num) (U x))) y a=
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (S (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+H y (highSectionCovariantDerivative d U y a)) := by
  let I21 := sphereSobolevInclusionL 2 1 (by norm_num)
  have hDU := I21.hasFDerivAt.comp y hU.hasFDerivAt
  have hD : fderiv ℝ (fun x => H x (I21 (U x))) y a=
      fderiv ℝ H y a (I21 (U y))+H y (I21 (fderiv ℝ U y a)) := by
    have hh := congrArg (fun L : X →L[ℝ] SphereSobolev 0 => L a)
      (hH.hasFDerivAt.clm_apply hDU).fderiv
    have hD0 : fderiv ℝ (fun x => H x (I21 (U x))) y a=
        H y (I21 (fderiv ℝ U y a))+fderiv ℝ H y a (I21 (U y)) := by
      simpa only [Function.comp_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply] using hh
    exact hD0.trans (add_comm _ _)
  have hCore := hGraph (U y)
  simp only [smul_sub,Finset.sum_sub_distrib] at hCore
  unfold coarseSectionCovariantDerivative highSectionCovariantDerivative
  change sphereSobolevInclusionL 0 (-1) (by norm_num) (fderiv ℝ (fun x => H x (I21 (U x))) y a)-_= _
  rw [hD]
  simp only [map_add,map_sub,map_sum,map_smul]
  rw [hCore]
  abel
end ShrinkingSpheres
