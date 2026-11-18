import Proof.CovariantOperatorApplication
import Proof.OrderZeroCovariantGraph
import Proof.CanonicalCovariantSection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The genuine H1-section covariant derivative, taking values in H0. -/
def oneSectionCovariantDerivative (d : Data) (U : X → SphereSobolev 1) (y a : X) : SphereSobolev 0 :=
  sphereSobolevInclusionL 1 0 (by norm_num) (fderiv ℝ U y a)-
    ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • sphereSobolevRotationL 1 i j (U y)

lemma coarseSectionCovariantDerivative_of_one (d : Data) (U : X → SphereSobolev 1)
    (y a : X) (hU : DifferentiableAt ℝ U y) :
    coarseSectionCovariantDerivative d (fun x => sphereSobolevInclusionL 1 0 (by norm_num) (U x)) y a=
      sphereSobolevInclusionL 0 (-1) (by norm_num) (oneSectionCovariantDerivative d U y a) := by
  have hD := (sphereSobolevInclusionL 1 0 (by norm_num)).hasFDerivAt.comp y hU.hasFDerivAt
  have hDF : fderiv ℝ (fun x => sphereSobolevInclusionL 1 0 (by norm_num) (U x)) y a=
      sphereSobolevInclusionL 1 0 (by norm_num) (fderiv ℝ U y a) := by
    exact DFunLike.congr_fun hD.fderiv a
  simp only [coarseSectionCovariantDerivative,oneSectionCovariantDerivative,hDF,
    sphereSobolevRotationL_zero_inclusion_one,map_sub,map_sum,map_smul]

lemma oneSectionCovariantDerivative_congr_germ {d : Data} {U V : X → SphereSobolev 1}
    {y a : X} (h : U =ᶠ[nhds y] V) :
    oneSectionCovariantDerivative d U y a=oneSectionCovariantDerivative d V y a := by
  rw [oneSectionCovariantDerivative,oneSectionCovariantDerivative,h.fderiv_eq,h.eq_of_nhds]

lemma oneSectionCovariantDerivative_high_inclusion (d : Data) (U : X → SphereSobolev 2)
    (y a : X) (hU : DifferentiableAt ℝ U y) :
    oneSectionCovariantDerivative d (fun x => sphereSobolevInclusionL 2 1 (by norm_num) (U x)) y a=
      sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U y a) := by
  have hD := (sphereSobolevInclusionL 2 1 (by norm_num)).hasFDerivAt.comp y hU.hasFDerivAt
  have hDF : fderiv ℝ (fun x => sphereSobolevInclusionL 2 1 (by norm_num) (U x)) y a=
      sphereSobolevInclusionL 2 1 (by norm_num) (fderiv ℝ U y a) := DFunLike.congr_fun hD.fderiv a
  simp only [oneSectionCovariantDerivative,highSectionCovariantDerivative,hDF,
    sphereSobolevRotationL_one_inclusion_two,map_sub,map_sum,map_smul]

lemma oneSectionCovariantDerivative_ambient (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y a : X) :
    oneSectionCovariantDerivative d (ambientSobolevSection 1 (by norm_num) G hG) y a=
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (ambientCovariantL2 G hG y a (frameConnectionCoefficient d.γ d.frame y a)) := by
  have hEq : ambientSobolevSection 1 (by norm_num) G hG=
      fun x => sphereSobolevInclusionL 2 1 (by norm_num) (ambientSobolevSection 2 (by norm_num) G hG x) := by
    funext x
    exact (ambientSobolevSection_inclusion 2 1 (by norm_num) (by norm_num) (by norm_num) G hG x).symm
  rw [hEq,oneSectionCovariantDerivative_high_inclusion d _ y a
    ((contDiff_ambientSobolevSection 2 (by norm_num) G hG).differentiable (by simp) y)]
  exact highSectionCovariantDerivative_ambient_coarse d G hG y a

end ShrinkingSpheres
