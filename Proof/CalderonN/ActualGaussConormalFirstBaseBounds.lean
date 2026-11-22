module

public import Proof.CalderonN.ActualRotatedConormalFiberDerivativeWeak
public import Proof.CalderonN.SmoothTraceAngularBoundsFromMatrix

import Proof.CalderonN.InverseMetricBounds
import Mathlib.Tactic

/-! Once differentiated in the ordinary base chart, the actual scaled
conormal remainder remains angular order one and costs a factor beta. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actualGauss_scaledConormal_first_base_angularBounds_on_unit_directions (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 6 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (D : ∀ x ∈ Y,ActualGaussFiberData d x)
        (hF : SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily D)),
        (∀ x (hx : x ∈ Y),∀ z ∈ ball (0:X dim) 1,((D x hx).coefficient z).IsSymm) →
        ∀ x ∈ Y,∀ a : X dim, ‖a‖ ≤ 1 → SmoothTraceAngularBound hn 1 (C*beta d.γ d.radius x)
          (smoothSupportedTraceFiberDerivative hY (actualGaussScaledConormalFamily D) hF a x) := by
  have hn₂ : 2 ≤ dim := by omega
  obtain ⟨η₁,C₁,hη₁,hC₁,h₁⟩ := uniform_actual_physicalWeakConormal_jets hn₂ hY hΩ hYc hSub 1
    (by decide) (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨η₂,C₂,hη₂,hC₂,h₂⟩ := uniform_actual_physicalRotatedConormal_jets hn₂ hY hΩ hYc hSub 1
    (by decide) hm K ρ c₀ M Cj hK hρ
  let A := C₁/unitSphereArea dim
  let B := C₂/unitSphereArea dim
  have hA : 0 ≤ A := div_nonneg hC₁ unitSphereArea_pos.le
  have hB : 0 ≤ B := div_nonneg hC₂ unitSphereArea_pos.le
  let C := max A (smoothTraceRotationLiftConstant dim A B)
  refine ⟨min η₁ η₂,C,lt_min hη₁ hη₂,hA.trans (le_max_left _ _),?_⟩
  intro floor hf ε he hs d hd hFrame D hF hSym x hx a ha
  let F := actualGaussScaledConormalFamily D
  let T := smoothSupportedTraceFiberDerivative hY F hF a x
  have hAdj : SmoothTraceAdjoint hn T T := smoothSupportedTraceFiberDerivative_symmetric hn hY F hF
    (fun y hy => actualGaussScaledConormalFamily_symmetric hn D hy (hSym y hy)) a hx
  obtain ⟨G⟩ := h₁ floor hf ε he (hs.trans (min_le_left _ _)) d hd hFrame D x hx
  have hR (i j : I dim) := h₂ floor hf ε he (hs.trans (min_le_right _ _)) d hd hFrame D hSym i j x hx
  have hScale : 0 ≤ beta d.γ d.radius x := Real.sqrt_nonneg _
  apply smoothTraceAngularBound_orderOne_of_scaled_rotated_finite_pairs hn T hAdj A B _
    hA hB hScale
  · intro f g
    exact G.fiberDerivative_weak_pair hn hY hx (by decide) hF a ha f g
  · intro i j f g
    obtain ⟨R⟩ := hR i j
    exact R.fiberDerivative_weak_pair hn hY hx (by decide) hF a ha f g

theorem uniform_actualGauss_scaledConormal_first_base_angularBounds (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 6 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (D : ∀ x ∈ Y,ActualGaussFiberData d x)
        (hF : SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily D)),
        (∀ x (hx : x ∈ Y),∀ z ∈ ball (0:X dim) 1,((D x hx).coefficient z).IsSymm) →
        ∀ x ∈ Y,∀ a : I dim, SmoothTraceAngularBound hn 1 (C*beta d.γ d.radius x)
          (smoothSupportedTraceFiberDerivative hY (actualGaussScaledConormalFamily D) hF (axis a) x) := by
  obtain ⟨η,C,hη,hC,hB⟩ := uniform_actualGauss_scaledConormal_first_base_angularBounds_on_unit_directions
    hn hY hΩ hYc hSub hm K ρ c₀ M Cj hK hρ
  exact ⟨η,C,hη,hC,fun floor hf ε he hs d hd hFrame D hF hSym x hx a =>
    hB floor hf ε he hs d hd hFrame D hF hSym x hx (axis a) (norm_axis a).le⟩

end CalderonN
