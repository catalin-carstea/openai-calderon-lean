import Proof.ActualSmoothRadialPair
import Proof.UniformActualFirstAdjointError
import Proof.ActualFrameErrorEndpointPair
import Proof.BalancedSecondTraceWitness
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- One physical coefficient choice, made before any test, for the complete
principal residual. All subsequent derivatives and products use these SAME
radial, adjoint, center and tensor families. -/
structure PhysicalPrincipalData (Y : Set X) (d : Data) (CF CT : ℝ) where
  radial : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  adjoint : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  center : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  tensor : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  radial_smooth : ContDiffOn ℝ ∞ radial Y
  adjoint_smooth : ContDiffOn ℝ ∞ adjoint Y
  center_smooth : ∀ i,ContDiffOn ℝ ∞ (center i) Y
  tensor_smooth : ∀ i j,ContDiffOn ℝ ∞ (tensor i j) Y
  radial_actual : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (radial x)
  adjoint_pair : ∀ x ∈ Y,∀ u v,⟪(radial x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,adjoint x v⟫_ℝ
  center_actual : ∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (adjoint x) (center a x)
  first : ActualFrameErrorEndpointPair Y d adjoint center CF
  tensor_graph : ∀ y ∈ Y,∀ i j,CoarseCovariantRotationGraph d y (d.frame y i)
    (actualFrameFirstAdjointErrorFamily d adjoint center j)
    ((∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
      actualFrameFirstAdjointErrorFamily d adjoint center k y)+tensor i j y)
  tensor_bound : ∀ y ∈ Y,∀ i j,‖tensor i j y‖ ≤ CT*d.radius y*beta d.γ d.radius y
  tensor_endpoints : ∀ y ∈ Y,∀ i j,
    ∃ Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    ∃ Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (tensor i j y)=
        Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
        (tensor i j y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
      ‖Lo‖ ≤ CT*d.radius y*beta d.γ d.radius y ∧ ‖Hi‖ ≤ CT*d.radius y*beta d.γ d.radius y
  physical : ∀ φ : Field,smoothNear φ (bundle Y d.γ) →
    (∃ T : Set X,IsCompact T ∧ T ⊆ Y ∧ ∀ x ∈ Y \ T,∀ w ∈ sphereAt d.γ x,φ (x,w)=0) →
    ∀ L : ℂ →L[ℝ] ℝ,∀ F : X × X → ℝ,∀ hF : ContDiff ℝ ∞ F,
    (∀ x ∈ Y,∀ w : UnitSphere,F (x,w.val)=L (φ (x,frameVector d.frame x w.val))) →
    Nonempty (SecondTraceSectionOutput Y d adjoint center tensor φ L F hF)

/-- Closed uniform production of all physical coefficient witnesses needed
by the principal residual. Constants precede every admitted radius, frame and
test; no realization or endpoint estimate is an extra selected premise. -/
theorem uniform_physical_principal_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CF CT : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CF ∧ 0 ≤ CT ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → Nonempty (PhysicalPrincipalData Y d CF CT) := by
  classical
  obtain ⟨ηR,hηR,hRadial⟩ := uniform_actual_smooth_radial_pair hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hError⟩ :=
    uniform_actual_smooth_first_adjoint_error hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,CF,hηF,hηF1,hCF,hFirst⟩ :=
    uniform_actual_frame_error_endpoint_pair hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηT,CT,hηT,hηT1,hCT,hTensor⟩ :=
    uniform_actual_second_trace_with_tensor_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ CE hCE
  let η := min ηR (min ηE (min ηF ηT))
  refine ⟨η,CF,CT,lt_min hηR (lt_min hηE (lt_min hηF hηT)),?_,hCF,hCT,?_⟩
  · exact ((min_le_right ηR _).trans ((min_le_right ηE _).trans (min_le_left ηF ηT))).trans hηF1
  intro floor hf ε hε hSmall d hd
  have hSmallR : ε ≤ ηR := hSmall.trans (min_le_left _ _)
  have hSmallE : ε ≤ ηE := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallF : ε ≤ ηF := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSmallT : ε ≤ ηT := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨R,A,hRS,hAS,hPair⟩ := hRadial floor hf ε hε hSmallR d hd
  have hR := fun x hx => (hPair x hx).1
  have hA := fun x hx => (hPair x hx).2
  choose G hGS hG hES hEN using fun a : I => hError floor hf ε hε hSmallE d hd R A hAS hR hA (axis a)
  have hAxisBound : ∀ a,∀ x ∈ Y,‖actualFirstAdjointErrorFamily d (axis a) A (G a) x‖ ≤ CE*d.radius x := by
    intro a x hx
    simpa only [norm_axis,mul_one] using hEN a x hx
  obtain ⟨First⟩ := hFirst floor hf ε hε hSmallF d hd R A G hR hA hG
  obtain ⟨S,hSS,hGraph,hBound,hEndpoints,hPhysical⟩ :=
    hTensor floor hf ε hε hSmallT d hd R A hAS hR hA G hGS hG hAxisBound
  exact ⟨{
    radial := R
    adjoint := A
    center := G
    tensor := S
    radial_smooth := hRS
    adjoint_smooth := hAS
    center_smooth := hGS
    tensor_smooth := hSS
    radial_actual := hR
    adjoint_pair := hA
    center_actual := hG
    first := First
    tensor_graph := hGraph
    tensor_bound := hBound
    tensor_endpoints := hEndpoints
    physical := hPhysical }⟩
end ShrinkingSpheres
