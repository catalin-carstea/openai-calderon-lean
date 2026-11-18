import Proof.CanonicalHorizontalSection
import Proof.CanonicalCovariantSection
import Proof.HorizontalComponents
import Proof.FrameAdjointLinearity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereFields

/-- The actual first moving trace has its canonical H1 section equal to the
    genuine horizontal H2-to-H1 section plus the actual adjoint H1 section.
    Equality in H1 follows from the injective genuine inclusion into L2. -/
theorem canonical_frameTrace_oneSection_eq {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (φ : Field) (hφ : smoothNear φ (bundle Y d.γ)) (L : ℂ →L[ℝ] ℝ)
    (F W V : X × X → ℝ) (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) (j : I)
    (hSource : ∀ x ∈ Y,∀ w : UnitSphere,F (x,w.val)=L (φ (x,frameVector d.frame x w.val)))
    (hTrace : ∀ x ∈ Y,∀ w : UnitSphere,W (x,w.val)=L (frameTraceDerivative d.γ d.adjoint d.frame j φ (x,frameVector d.frame x w.val)))
    (hAdjoint : ∀ x ∈ Y,∀ w : UnitSphere,V (x,w.val)=L (frameAdjointField d.adjoint d.frame j φ (x,frameVector d.frame x w.val)))
    {y : X} (hy : y ∈ Y) :
    ambientSobolevSection 1 (by norm_num) W hW y=
      highSectionCovariantDerivative d (ambientSobolevSection 2 (by norm_num) F hF) y (d.frame y j)+
        ambientSobolevSection 1 (by norm_num) V hV y := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hW0 : Z.symm (sphereSobolevInclusionL 1 0 (by norm_num) (ambientSobolevSection 1 (by norm_num) W hW y))
      =ᵐ[sphereProbability] fun w : UnitSphere => L (frameTraceDerivative d.γ d.adjoint d.frame j φ (y,frameVector d.frame y w.val)) := by
    rw [ambientSobolevSection_coarse,LinearIsometryEquiv.symm_apply_apply]
    exact (ambientSphereL2_ae W hW y).trans (Eventually.of_forall (hTrace y hy))
  have hV0 : Z.symm (sphereSobolevInclusionL 1 0 (by norm_num) (ambientSobolevSection 1 (by norm_num) V hV y))
      =ᵐ[sphereProbability] fun w : UnitSphere => L (frameAdjointField d.adjoint d.frame j φ (y,frameVector d.frame y w.val)) := by
    rw [ambientSobolevSection_coarse,LinearIsometryEquiv.symm_apply_apply]
    exact (ambientSphereL2_ae V hV y).trans (Eventually.of_forall (hAdjoint y hy))
  have hH0 : Z.symm (sphereSobolevInclusionL 1 0 (by norm_num)
      (highSectionCovariantDerivative d (ambientSobolevSection 2 (by norm_num) F hF) y (d.frame y j)))
      =ᵐ[sphereProbability] fun w : UnitSphere => L (horizontal d.γ φ y (frameVector d.frame y w.val) (d.frame y j)) := by
    exact canonical_horizontal_section_ae hY d h hK he hFrame φ hφ L F hF hSource hy (d.frame y j)
  have hSum := coarseValue_add _ _ _ _ hH0 hV0
  have hSumTrace := hSum.trans (Eventually.of_forall (fun w : UnitSphere =>
    ((congrArg L (frameTraceDerivative_eq_horizontal_adjoint d.γ d.adjoint d.frame j φ y
      (frameVector d.frame y w.val))).trans (L.map_add _ _)).symm))
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  rw [map_add]
  apply Z.symm.injective
  exact Lp.ext (hW0.trans hSumTrace.symm)
end ShrinkingSpheres
