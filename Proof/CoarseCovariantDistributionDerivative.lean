import Proof.CoarseCovariantJetFamily
import Proof.Archive.NativeHarmonicHalfCoarseDualPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

/-- The actual distribution-valued covariant derivative of a coarse
family. This expression is smooth whenever the family and connection are;
no regularity of a pointwise chosen coarse graph witness is required. -/
def coarseCovariantDistributionDerivativeL (d : Data)
    (F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (a y : X) :
    SphereSobolev 2 →L[ℝ] SphereSobolev (-1) :=
  (sphereSobolevInclusionL 0 (-1) (by norm_num)).comp
      ((fderiv ℝ F y a).comp (sphereSobolevInclusionL 2 1 (by norm_num)))-
    ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
      ((sphereSobolevRotationL 0 i j).comp
          ((F y).comp (sphereSobolevInclusionL 2 1 (by norm_num)))-
        (sphereSobolevInclusionL 0 (-1) (by norm_num)).comp ((F y).comp (sphereSobolevRotationL 2 i j)))

lemma CoarseCovariantRotationGraph.distribution_eq {d : Data} {y a : X}
    {F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {T : SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (h : CoarseCovariantRotationGraph d y a F T) :
    coarseCovariantDistributionDerivativeL d F a y=
      (sphereSobolevInclusionL 0 (-1) (by norm_num)).comp
        (T.comp (sphereSobolevInclusionL 2 1 (by norm_num))) := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [coarseCovariantDistributionDerivativeL,ContinuousLinearMap.comp_apply,
    _root_.sub_apply,_root_.sum_apply,_root_.smul_apply] using (h u).symm

lemma contDiffOn_coarseCovariantDistributionDerivativeL {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hF : ContDiffOn ℝ ∞ F Y) (a : X) :
    ContDiffOn ℝ ∞ (coarseCovariantDistributionDerivativeL d F a) Y := by
  have hD : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y a) Y :=
    (hF.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  have hLeading : ContDiffOn ℝ ∞ (fun y => (sphereSobolevInclusionL 0 (-1) (by norm_num)).comp
      ((fderiv ℝ F y a).comp (sphereSobolevInclusionL 2 1 (by norm_num)))) Y :=
    contDiffOn_const.clm_comp (hD.clm_comp contDiffOn_const)
  have hAngular (i j : I) : ContDiffOn ℝ ∞ (fun y =>
      ((sphereSobolevRotationL 0 i j).comp ((F y).comp (sphereSobolevInclusionL 2 1 (by norm_num)))-
        (sphereSobolevInclusionL 0 (-1) (by norm_num)).comp ((F y).comp (sphereSobolevRotationL 2 i j)))) Y :=
    (contDiffOn_const.clm_comp (hF.clm_comp contDiffOn_const)).sub
      (contDiffOn_const.clm_comp (hF.clm_comp contDiffOn_const))
  exact hLeading.sub (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK d.frame he
      (fun _ => a) contDiffOn_const i j)).smul (hAngular i j))))

/-- The genuine graph gives the stronger weak norm through the actual
inclusions; this estimate can be used pointwise without choosing T smoothly. -/
lemma CoarseCovariantRotationGraph.distribution_pair_bound {d : Data} {y a : X}
    {F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {T : SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (h : CoarseCovariantRotationGraph d y a F T) (u : SphereSobolev 1) (v : SphereSobolev 2) :
    |sphereSobolevDualPairing 1 u (coarseCovariantDistributionDerivativeL d F a y v)| ≤
      ‖T‖*‖sphereSobolevInclusionL 1 0 (by norm_num) u‖*
        ‖sphereSobolevInclusionL 2 1 (by norm_num) v‖ := by
  rw [h.distribution_eq]
  simp only [ContinuousLinearMap.comp_apply]
  rw [sphereSobolevDualPairing_zero_inclusion 1 (by norm_num)]
  calc
    _ ≤ ‖sphereSobolevInclusionL 1 0 (by norm_num) u‖*
      ‖T (sphereSobolevInclusionL 2 1 (by norm_num) v)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖sphereSobolevInclusionL 1 0 (by norm_num) u‖*
      (‖T‖*‖sphereSobolevInclusionL 2 1 (by norm_num) v‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

end ShrinkingSpheres
