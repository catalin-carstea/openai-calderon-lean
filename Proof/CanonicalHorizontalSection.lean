import Proof.CanonicalCovariantSection
import Proof.HorizontalComponents
import Proof.FrameAdjointLinearity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereFields

/-- Shared physical horizontal realization, extracted from the checked
canonical first-trace proof for use by both that caller and the model output. -/
theorem canonical_horizontal_section_ae {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (φ : Field) (hφ : smoothNear φ (bundle Y d.γ)) (L : ℂ →L[ℝ] ℝ)
    (F : X × X → ℝ) (hF : ContDiff ℝ ∞ F)
    (hSource : ∀ x ∈ Y,∀ w : UnitSphere,F (x,w.val)=L (φ (x,frameVector d.frame x w.val)))
    {y : X} (hy : y ∈ Y) (a : X) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num)
        (highSectionCovariantDerivative d (ambientSobolevSection 2 (by norm_num) F hF) y a))
      =ᵐ[sphereProbability] fun w : UnitSphere => L (horizontal d.γ φ y (frameVector d.frame y w.val) a) := by
  rw [highSectionCovariantDerivative_ambient_coarse,LinearIsometryEquiv.symm_apply_apply]
  apply (ambientCovariantL2_ae_horizontal hY h hK d.frame he hFrame (fun p => L (φ p))
    (hφ.clm_comp L) F hF hSource hy a).trans
  apply Eventually.of_forall
  intro w
  exact horizontal_clm L d.γ φ y (frameVector d.frame y w.val) a
    (hφ.differentiableAt ⟨hy,frameVector_mem_sphere d.γ d.frame y (hFrame y hy) w⟩)

/-- A smooth physical horizontal representative is the same genuine H1
section as the derivative of the canonical H2 input. -/
theorem canonical_horizontal_oneSection_eq {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (φ : Field) (hφ : smoothNear φ (bundle Y d.γ)) (L : ℂ →L[ℝ] ℝ)
    (F H : X × X → ℝ) (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H) (j : I)
    (hSource : ∀ x ∈ Y,∀ w : UnitSphere,F (x,w.val)=L (φ (x,frameVector d.frame x w.val)))
    (hHorizontal : ∀ x ∈ Y,∀ w : UnitSphere,H (x,w.val)=L (horizontal d.γ φ x (frameVector d.frame x w.val) (d.frame x j)))
    {y : X} (hy : y ∈ Y) :
    highSectionCovariantDerivative d (ambientSobolevSection 2 (by norm_num) F hF) y (d.frame y j)=
      ambientSobolevSection 1 (by norm_num) H hH y := by
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  apply (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm.injective
  apply Lp.ext
  have hActual := canonical_horizontal_section_ae hY d h hK he hFrame φ hφ L F hF hSource hy (d.frame y j)
  rw [ambientSobolevSection_coarse,LinearIsometryEquiv.symm_apply_apply]
  exact hActual.trans ((ambientSphereL2_ae H hH y).trans (Eventually.of_forall (hHorizontal y hy))).symm
end ShrinkingSpheres
