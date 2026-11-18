import Proof.ActualSecondTraceDefinitions
import Proof.StrongActualSecondTraceAssembly
import Proof.SecondTraceSectionExpansion
import Proof.PhysicalSecondTraceSection
import Proof.CanonicalFrameTraceSection
import Proof.FrameTraceRepresentatives
import Proof.SmoothHighCovariantSections
import Proof.UniformCompleteFirstAdjointGraph
import Proof.CompleteAdjointPhysicalSection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

/-- Uniform actual second-trace expansion with one shared first-error jet and
    the SAME physical adjoint representatives. The selected theorem does not
    assume this result; all inputs are the existing actual radial/center witnesses. -/
theorem uniform_actual_second_trace_assembly {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (C0 : ℝ) (hC0 : 0 ≤ C0) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ a,ContDiffOn ℝ ∞ (G a) Y) →
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) →
      (∀ a,∀ x ∈ Y,‖actualFirstAdjointErrorFamily d (axis a) A (G a) x‖ ≤ C0*d.radius x) →
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ i j,ContDiffOn ℝ ∞ (S i j) Y) ∧
        (∀ y ∈ Y,∀ i j,‖S i j y‖ ≤ CE*d.radius y*beta d.γ d.radius y) ∧
        ∀ φ : Field,smoothNear φ (bundle Y d.γ) →
        (∃ T : Set X,IsCompact T ∧ T ⊆ Y ∧ ∀ x ∈ Y \ T,∀ w ∈ sphereAt d.γ x,φ (x,w)=0) →
        ∀ L : ℂ →L[ℝ] ℝ,∀ F : X × X → ℝ,∀ hF : ContDiff ℝ ∞ F,
        (∀ x ∈ Y,∀ w : UnitSphere,F (x,w.val)=L (φ (x,frameVector d.frame x w.val))) →
        Nonempty (SecondTraceSectionOutput Y d A G S φ L F hF) := by
  obtain ⟨η,CE,hη,hη1,hCE,hProduce⟩ :=
    uniform_actual_second_trace_assembly_with_error_graph hY hΩ hSub hm K ρ c₀ M Cj hK hρ C0 hC0
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA G hGS hG hE
  obtain ⟨S,hSS,hGraph,hSN,hP⟩ := hProduce floor hf ε hε hSmall d hd R A hAS hR hA G hGS hG hE
  exact ⟨S,hSS,hSN,hP⟩
end ShrinkingSpheres
