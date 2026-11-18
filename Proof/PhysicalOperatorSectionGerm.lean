import Proof.CanonicalSmoothSobolevSection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereFields

/-- A physical pointwise realization on every H1 input gives equality of
    the corresponding canonical smooth sections, rather than only AE values. -/
lemma physical_operator_canonical_section_eq {Y : Set X} (d : Data)
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G V : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (hV : ContDiff ℝ ∞ V)
    (F N : X × X → ℝ)
    (hSource : ∀ x ∈ Y,∀ w : UnitSphere,G (x,w.val)=F (x,frameVector d.frame x w.val))
    (hTarget : ∀ x ∈ Y,∀ w : UnitSphere,V (x,w.val)=N (x,frameVector d.frame x w.val))
    (hPhysical : ∀ x ∈ Y,∀ u : SphereSobolev 1,
      ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (sphereSobolevInclusionL 1 0 (by norm_num) u) =ᵐ[sphereProbability]
        fun w : UnitSphere => F (x,frameVector d.frame x w.val)) →
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (H x u) =ᵐ[sphereProbability]
        fun w : UnitSphere => N (x,frameVector d.frame x w.val)) :
    ∀ x ∈ Y,H x (ambientSobolevSection 1 (by norm_num) G hG x)=
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientSphereL2 V hV x) := by
  intro x hx
  have hInput : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) (ambientSobolevSection 1 (by norm_num) G hG x)) =ᵐ[sphereProbability]
      fun w : UnitSphere => F (x,frameVector d.frame x w.val) := by
    rw [ambientSobolevSection_coarse,LinearIsometryEquiv.symm_apply_apply]
    exact (ambientSphereL2_ae G hG x).trans (Eventually.of_forall (hSource x hx))
  have hOut := hPhysical x hx _ hInput
  have hVOut := (ambientSphereL2_ae V hV x).trans (Eventually.of_forall (hTarget x hx))
  apply (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact Lp.ext (hOut.trans hVOut.symm)

lemma physical_operator_canonical_section_germ {Y : Set X} (hY : IsOpen Y)
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G V : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (hV : ContDiff ℝ ∞ V)
    (hEq : ∀ x ∈ Y,H x (ambientSobolevSection 1 (by norm_num) G hG x)=
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientSphereL2 V hV x))
    {y : X} (hy : y ∈ Y) :
    (fun x => H x (ambientSobolevSection 1 (by norm_num) G hG x)) =ᶠ[𝓝 y]
      (fun x => sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientSphereL2 V hV x)) := by
  filter_upwards [hY.mem_nhds hy] with x hx
  exact hEq x hx
end ShrinkingSpheres
