import Proof.OneSectionCovariantDerivative
import Proof.FrameAdjointLinearity
import Proof.HorizontalComponents
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

lemma coarseValue_sub (u v : SphereSobolev 0) (f g : UnitSphere → ℝ)
    (hu : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm u =ᵐ[sphereProbability] f)
    (hv : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm v =ᵐ[sphereProbability] g) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (u-v)
      =ᵐ[sphereProbability] fun w => f w-g w := by
  have hn := coarseValue_smul (-1) v g hv
  have hn' : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (-v)
      =ᵐ[sphereProbability] fun w => -g w := by
    simpa only [neg_one_smul,neg_one_mul] using hn
  simpa only [sub_eq_add_neg] using coarseValue_add u (-v) f (fun w => -g w) hu hn'

/-- The actual covariant second moving trace is the derivative and adjoint
    action of its SAME canonical first-trace section, with the exact index connection. -/
theorem physical_second_trace_section_ae {Y : Set X} (hY : IsOpen Y) (d : Data)
    {K : ℝ} (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (φ : Field) (L : ℂ →L[ℝ] ℝ) (W : I → X × X → ℝ) (hW : ∀ j,ContDiff ℝ ∞ (W j))
    (hRep : ∀ k,∀ x ∈ Y,∀ w : UnitSphere,W k (x,w.val)=
      L (frameTraceDerivative d.γ d.adjoint d.frame k φ (x,frameVector d.frame x w.val)))
    {y : X} (hy : y ∈ Y) (i j : I)
    (hSmooth : smoothNear (frameTraceDerivative d.γ d.adjoint d.frame j φ) (bundle Y d.γ))
    (C : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hAdjoint : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (C (ambientSobolevSection 1 (by norm_num) (W j) (hW j) y)) =ᵐ[sphereProbability]
      fun w : UnitSphere => L (frameAdjointField d.adjoint d.frame i
        (frameTraceDerivative d.γ d.adjoint d.frame j φ) (y,frameVector d.frame y w.val))) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (oneSectionCovariantDerivative d (ambientSobolevSection 1 (by norm_num) (W j) (hW j)) y (d.frame y i)-
        (∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
          sphereSobolevInclusionL 1 0 (by norm_num) (ambientSobolevSection 1 (by norm_num) (W k) (hW k) y))+
        C (ambientSobolevSection 1 (by norm_num) (W j) (hW j) y)) =ᵐ[sphereProbability]
      fun w : UnitSphere => L (frameCovariantTraceSecond d.γ d.adjoint d.frame i j φ (y,frameVector d.frame y w.val)) := by
  have hHorizontal : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (oneSectionCovariantDerivative d (ambientSobolevSection 1 (by norm_num) (W j) (hW j)) y (d.frame y i))
      =ᵐ[sphereProbability] fun w : UnitSphere => L (horizontal d.γ
        (frameTraceDerivative d.γ d.adjoint d.frame j φ) y (frameVector d.frame y w.val) (d.frame y i)) := by
    rw [oneSectionCovariantDerivative_ambient,LinearIsometryEquiv.symm_apply_apply]
    apply (ambientCovariantL2_ae_horizontal hY h hK d.frame he hFrame
      (fun p => L (frameTraceDerivative d.γ d.adjoint d.frame j φ p)) (hSmooth.clm_comp L)
      (W j) (hW j) (hRep j) hy (d.frame y i)).trans
    apply Eventually.of_forall
    intro w
    exact horizontal_clm L d.γ (frameTraceDerivative d.γ d.adjoint d.frame j φ)
      y (frameVector d.frame y w.val) (d.frame y i)
      (hSmooth.differentiableAt ⟨hy,frameVector_mem_sphere d.γ d.frame y (hFrame y hy) w⟩)
  have hFirst (k : I) : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) (ambientSobolevSection 1 (by norm_num) (W k) (hW k) y))
      =ᵐ[sphereProbability] fun w : UnitSphere => L (frameTraceDerivative d.γ d.adjoint d.frame k φ (y,frameVector d.frame y w.val)) := by
    rw [ambientSobolevSection_coarse,LinearIsometryEquiv.symm_apply_apply]
    exact (ambientSphereL2_ae (W k) (hW k) y).trans (Eventually.of_forall (hRep k y hy))
  have hConnection := coarseValue_weighted_sum_three
    (frameConnectionCoefficient d.γ d.frame y (d.frame y i) j) _ _ hFirst
  have hActual := coarseValue_add _ _ _ _ (coarseValue_sub _ _ _ _ hHorizontal hConnection) hAdjoint
  apply hActual.trans
  apply Eventually.of_forall
  intro w
  simp only [frameCovariantTraceSecond,frameTraceDerivative_eq_horizontal_adjoint,map_sub,map_add,map_sum,map_smul,smul_eq_mul]
  ring
end ShrinkingSpheres
