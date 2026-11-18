import Proof.CovariantOperatorApplication
import Proof.MetricSmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma contDiffOn_highSectionCovariantDerivative_frame {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y) (i : I) :
    ContDiffOn ℝ ∞ (fun x => highSectionCovariantDerivative d U x (d.frame x i)) Y := by
  have hD := hU.fderiv_of_isOpen (m:=∞) hY (by simp)
  have hLead := (sphereSobolevInclusionL 2 1 (by norm_num)).contDiff.comp_contDiffOn (hD.clm_apply (he i))
  have hAngular : ContDiffOn ℝ ∞ (fun x => ∑ j : I,∑ k : I,
      ((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame x (d.frame x i) j k) • sphereSobolevRotationL 2 j k (U x)) Y := by
    apply ContDiffOn.sum
    intro j _
    apply ContDiffOn.sum
    intro k _
    exact (contDiffOn_const.mul (h.contDiffOn_frameConnection hY hK d.frame he (fun x => d.frame x i) (he i) j k)).smul
      ((sphereSobolevRotationL 2 j k).contDiff.comp_contDiffOn hU)
  exact hLead.sub hAngular
end ShrinkingSpheres
