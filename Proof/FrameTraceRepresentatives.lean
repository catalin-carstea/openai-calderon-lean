import Proof.FrameAdjointLinearity
import Proof.TestRepresentative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma Admissible.frameTraceDerivative_smoothNear {Y Ω : Set X} (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ)) (j : I) :
    smoothNear (frameTraceDerivative d.γ d.adjoint d.frame j φ) (bundle Y d.γ) := by
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hEq : frameTraceDerivative d.γ d.adjoint d.frame j φ=
      fun p => ∑ a : I,d.frame p.1 j a • traceDerivative d.γ d.adjoint a φ p := by
    funext p
    exact frameTraceDerivative_apply _ _ _ _ _ _
  rw [hEq]
  apply smoothNear.finset_sum Finset.univ
  intro a _
  exact (smoothNear_traceDerivative hY h hK hd.2.2.2.1 hφ a).smul_base hY
    ((EuclideanSpace.proj (𝕜:=ℝ) a).contDiff.comp_contDiffOn (he j))

lemma Admissible.exists_frameTrace_scalar_representative {Y Ω : Set X} (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ))
    (hcpt : ∃ S : Set X,IsCompact S ∧ S ⊆ Y ∧ ∀ x ∈ Y \ S,∀ w ∈ sphereAt d.γ x,φ (x,w)=0)
    (j : I) (L : ℂ →L[ℝ] ℝ) :
    ∃ S : Set X,IsCompact S ∧ S ⊆ Y ∧ ∃ W : X × X → ℝ,ContDiff ℝ ∞ W ∧
      (∀ x ∈ Y,∀ w : UnitSphere,W (x,w.val)=L (frameTraceDerivative d.γ d.adjoint d.frame j φ (x,frameVector d.frame x w.val))) ∧
      ∀ x ∉ S,∀ w : UnitSphere,W (x,w.val)=0 := by
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame := fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  obtain ⟨S,hS,hSY,hZero⟩ := hcpt
  have hSmooth := hd.frameTraceDerivative_smoothNear hY hSub hK hφ j
  have hOutZero : ∀ x ∈ Y \ S,∀ w ∈ sphereAt d.γ x,frameTraceDerivative d.γ d.adjoint d.frame j φ (x,w)=0 := by
    intro x hx w hw
    rw [frameTraceDerivative_apply]
    apply Finset.sum_eq_zero
    intro a _
    rw [traceDerivative_zero_of_support hY h hK d.frame he hFrame hd.2.2.2.1 hd.2.2.1
      hφ S hS.isClosed hZero a hx w hw,smul_zero]
  obtain ⟨T,hT,hTY,V,hV,hRep,hVZero⟩ := exists_smooth_standard_representative_of_support hY d.frame he hFrame
    hSmooth ⟨S,hS,hSY,hOutZero⟩
  refine ⟨T,hT,hTY,fun p => L (V p),L.contDiff.comp hV,?_,?_⟩
  · intro x hx w
    exact congrArg L (hRep x hx w)
  · intro x hx w
    change L (V (x,w.val))=0
    rw [hVZero x hx w,map_zero]
end ShrinkingSpheres
