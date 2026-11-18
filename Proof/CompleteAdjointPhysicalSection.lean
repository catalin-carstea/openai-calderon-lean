import Proof.CompleteFirstAdjointCovariantGraph
import Proof.PhysicalTraceRegularity
import Proof.TestRepresentative
import Proof.PhysicalOperatorSectionGerm
import Proof.UniformActualFrozenAdjointNormalForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 25
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SmoothSphereFields

/-- The actual trace adjoint of a compact test has a global smooth scalar
    standard-sphere representative, with compact base support inside Y. -/
theorem Admissible.exists_frameAdjoint_scalar_representative {Y Ω : Set X} (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ))
    (hcpt : ∃ S : Set X,IsCompact S ∧ S ⊆ Y ∧ ∀ x ∈ Y \ S,∀ w ∈ sphereAt d.γ x,φ (x,w)=0) (j : I) (L : ℂ →L[ℝ] ℝ) :
    ∃ S : Set X,IsCompact S ∧ S ⊆ Y ∧ ∃ V : X × X → ℝ,ContDiff ℝ ∞ V ∧
      (∀ x ∈ Y,∀ w : UnitSphere,V (x,w.val)=L (frameAdjointField d.adjoint d.frame j φ (x,frameVector d.frame x w.val))) ∧
      ∀ x ∉ S,∀ w : UnitSphere,V (x,w.val)=0 := by
  have he := fun a => (hd.1.2.2.2.2.2.2.1 a).mono hSub
  have hFrame := fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  obtain ⟨S,hS,hSY,hZero⟩ := hcpt
  have hSmooth : smoothNear (frameAdjointField d.adjoint d.frame j φ) (bundle Y d.γ) := by
    apply smoothNear.finset_sum Finset.univ
    intro a _
    exact ((hd.2.2.2.1 a φ hφ).1).smul_base hY
      ((EuclideanSpace.proj (𝕜:=ℝ) a).contDiff.comp_contDiffOn (he j))
  have hOutZero : ∀ x ∈ Y \ S,∀ w ∈ sphereAt d.γ x,frameAdjointField d.adjoint d.frame j φ (x,w)=0 := by
    intro x hx w hw
    unfold frameAdjointField
    apply Finset.sum_eq_zero
    intro a _
    rw [hd.2.2.2.1.zero_on_sphere hd.2.2.1 hφ a hx.1 (hFrame x hx.1) (hZero x hx) w hw,smul_zero]
  obtain ⟨T,hT,hTY,V,hV,hRep,hVZero⟩ := exists_smooth_standard_representative_of_support hY d.frame he hFrame
    hSmooth ⟨S,hS,hSY,hOutZero⟩
  refine ⟨T,hT,hTY,fun p => L (V p),L.contDiff.comp hV,?_,?_⟩
  · intro x hx w
    exact congrArg L (hRep x hx w)
  · intro x hx w
    change L (V (x,w.val))=0
    rw [hVZero x hx w,map_zero]

/-- The same physical first-adjoint operator acts on canonical Sobolev
    sections as the actual smooth compact adjoint field, identically on Y. -/
theorem uniform_complete_adjoint_section_realization {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,∃ Q : SmoothCoefficientJets 2,0 < η ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) → ∀ i : I,
      ∀ φ : Field,smoothNear φ (bundle Y d.γ) →
      (∃ S : Set X,IsCompact S ∧ S ⊆ Y ∧ ∀ x ∈ Y \ S,∀ w ∈ sphereAt d.γ x,φ (x,w)=0) → ∀ L : ℂ →L[ℝ] ℝ,
      ∀ F : X × X → ℝ,∀ hF : ContDiff ℝ ∞ F,
      (∀ x ∈ Y,∀ w : UnitSphere,F (x,w.val)=L (φ (x,frameVector d.frame x w.val))) →
      ∃ S : Set X,IsCompact S ∧ S ⊆ Y ∧ ∃ V : X × X → ℝ,∃ hV : ContDiff ℝ ∞ V,
        (∀ x ∈ Y,∀ w : UnitSphere,V (x,w.val)=L (frameAdjointField d.adjoint d.frame i φ (x,frameVector d.frame x w.val))) ∧
        (∀ x ∉ S,∀ w : UnitSphere,V (x,w.val)=0) ∧
        ∀ x ∈ Y,completeFirstAdjointFamily d A G i x (ambientSobolevSection 1 (by norm_num) F hF x)=
          sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientSphereL2 V hV x) := by
  have hNormalTheorem := uniform_actual_frozen_adjoint_normal_form (Y:=Y) (Ω:=Ω) (m:=m)
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,Q,hη,hQ,hNormal⟩ := hNormalTheorem
  refine ⟨η,Q,hη,hQ,?_⟩
  intro floor hf ε hε hSmall d hd R A hR hA G hG i φ hφ hcpt L F hF hRep
  obtain ⟨S,hS,hSY,V,hV,hVRep,hVZero⟩ := hd.exists_frameAdjoint_scalar_representative hY hSub hφ hcpt i L
  refine ⟨S,hS,hSY,V,hV,hVRep,hVZero,?_⟩
  apply physical_operator_canonical_section_eq d (completeFirstAdjointFamily d A G i) F V hF hV
    (fun p => L (φ p)) (fun p => L (frameAdjointField d.adjoint d.frame i φ p)) hRep hVRep
  intro x hx u hInput
  have hh := frame_adjoint_normal_form_of_axes Q hQ d x (hd.1.2.2.2.2.2.2.2 x (hSub hx))
    (fun a => actualFirstAdjointErrorFamily d (axis a) A (G a) x) i φ L u
    (fun a => hNormal floor hf ε hε hSmall d hd R A hR hA a (G a) (hG a) x hx φ hφ L u hInput)
  simpa only [completeFirstAdjointFamily_eq_normal_form Q hQ,_root_.add_apply,ContinuousLinearMap.comp_apply,
    actualFrameFirstAdjointErrorFamily,_root_.sum_apply,_root_.smul_apply] using hh
end ShrinkingSpheres
