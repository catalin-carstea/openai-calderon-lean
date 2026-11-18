import Proof.OneSectionCovariantDerivative
import Proof.CoarseAmbientCovariantSection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A genuine operator graph acts on a smooth H1 output section with its
    own actual derivative; no unproved higher endpoint is substituted. -/
lemma CoarseCovariantRotationGraph.apply_oneSection {d : Data} {y a : X}
    {H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {S : SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (hGraph : CoarseCovariantRotationGraph d y a H S) (hH : DifferentiableAt ℝ H y)
    (U : X → SphereSobolev 2) (hU : DifferentiableAt ℝ U y)
    (V : X → SphereSobolev 1) (hV : DifferentiableAt ℝ V y)
    (hOut : (fun x => sphereSobolevInclusionL 1 0 (by norm_num) (V x)) =ᶠ[𝓝 y]
      (fun x => H x (sphereSobolevInclusionL 2 1 (by norm_num) (U x)))) :
    oneSectionCovariantDerivative d V y a=
      S (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+H y (highSectionCovariantDerivative d U y a) := by
  apply sphereSobolevInclusionL_injective 0 (-1) (by norm_num)
  rw [← coarseSectionCovariantDerivative_of_one d V y a hV]
  exact (coarseSectionCovariantDerivative_congr_germ d y a _ _ hOut).trans
    (hGraph.apply_section hH U hU)

/-- The tensor-index connection cancels exactly against the SAME physical
    output sections, leaving the actual operator jet and first source derivative. -/
theorem covariant_tensor_section_application (d : Data) (y a : X)
    (H : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (J : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (U : X → SphereSobolev 2) (V : I → X → SphereSobolev 1)
    (hH : ∀ j,DifferentiableAt ℝ (H j) y) (hU : DifferentiableAt ℝ U y)
    (hV : ∀ j,DifferentiableAt ℝ (V j) y)
    (hOut : ∀ j,(fun x => sphereSobolevInclusionL 1 0 (by norm_num) (V j x)) =ᶠ[𝓝 y]
      (fun x => H j x (sphereSobolevInclusionL 2 1 (by norm_num) (U x))))
    (hGraph : ∀ j,CoarseCovariantRotationGraph d y a (H j)
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • H k y)+J j)) (j : I) :
    oneSectionCovariantDerivative d (V j) y a-
      ∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k •
        sphereSobolevInclusionL 1 0 (by norm_num) (V k y)=
      J j (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+H j y (highSectionCovariantDerivative d U y a) := by
  have hApply := (hGraph j).apply_oneSection (hH j) U hU (V j) (hV j) (hOut j)
  have hPoint (k : I) : sphereSobolevInclusionL 1 0 (by norm_num) (V k y)=
      H k y (sphereSobolevInclusionL 2 1 (by norm_num) (U y)) := (hOut k).eq_of_nhds
  rw [hApply]
  simp only [_root_.add_apply,_root_.sum_apply,_root_.smul_apply,hPoint]
  abel
end ShrinkingSpheres
