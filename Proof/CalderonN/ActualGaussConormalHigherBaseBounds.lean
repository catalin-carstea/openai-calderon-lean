module

public import Proof.CalderonN.ActualGaussConormalFirstBaseBounds
public import Proof.CalderonN.SmoothSupportedFiberHigherDerivatives

import Proof.CalderonN.ActualConormalFiberDerivativeWeak
import Proof.CalderonN.ActualRotatedConormalFiberDerivativeWeak
import Proof.CalderonN.SmoothTraceAngularBoundsFromMatrix
import Mathlib.Tactic

/-! Transfer the physical weak conormal Taylor jets to ordinary base
derivatives on the smooth trace core and lift their angular endpoints. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actualGauss_scaledConormal_baseJet_angularBounds (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (N : ℕ) (hN : N ≤ 8) (hm : N+5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (D : ∀ x ∈ Y,ActualGaussFiberData d x)
        (hF : SmoothSupportedTraceFiberRegular Y (actualGaussScaledConormalFamily D)),
        (∀ x (hx : x ∈ Y),∀ z ∈ ball (0:X dim) 1,((D x hx).coefficient z).IsSymm) →
        ∀ x ∈ Y,∀ n ≤ N,∀ a : Fin n → X dim,(∀ i, ‖a i‖ ≤ 1) →
          let F : RegularTraceFiberFamily Y := ⟨actualGaussScaledConormalFamily D,hF⟩
          SmoothTraceAngularBound hn 1 (C*(beta d.γ d.radius x)^n) ((F.iteratedDerivative hY n a).1 x) := by
  have hn₂ : 2 ≤ dim := by omega
  obtain ⟨η₁,C₁,hη₁,hC₁,h₁⟩ := uniform_actual_physicalWeakConormal_jets hn₂ hY hΩ hYc hSub N
    hN (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨η₂,C₂,hη₂,hC₂,h₂⟩ := uniform_actual_physicalRotatedConormal_jets hn₂ hY hΩ hYc hSub N
    hN hm K ρ c₀ M Cj hK hρ
  let P := C₁/unitSphereArea dim
  let Q := C₂/unitSphereArea dim
  have hP : 0 ≤ P := div_nonneg hC₁ unitSphereArea_pos.le
  have hQ : 0 ≤ Q := div_nonneg hC₂ unitSphereArea_pos.le
  let C := max P (smoothTraceRotationLiftConstant dim P Q)
  refine ⟨min η₁ η₂,C,lt_min hη₁ hη₂,hP.trans (le_max_left _ _),?_⟩
  intro floor hf ε he hs d hd hFrame D hF hSym x hx n hnN a ha
  let F : RegularTraceFiberFamily Y := ⟨actualGaussScaledConormalFamily D,hF⟩
  let T := (F.iteratedDerivative hY n a).1 x
  let β := beta d.γ d.radius x
  have hAdj : SmoothTraceAdjoint hn T T := F.iteratedDerivative_symmetric hn hY
    (fun y hy => actualGaussScaledConormalFamily_symmetric hn D hy (hSym y hy)) n a hx
  obtain ⟨G⟩ := h₁ floor hf ε he (hs.trans (min_le_left _ _)) d hd hFrame D x hx
  have hR (i j : I dim) := h₂ floor hf ε he (hs.trans (min_le_right _ _)) d hd hFrame D hSym i j x hx
  have hScale : 0 ≤ β^n := pow_nonneg (Real.sqrt_nonneg _) n
  apply smoothTraceAngularBound_orderOne_of_scaled_rotated_finite_pairs hn T hAdj P Q _ hP hQ hScale
  · intro f g
    have h := F.abs_iteratedDerivative_pair_of_entry hn hY hx (finiteHarmonicSmoothTraceL f)
      (finiteHarmonicSmoothTraceL g) n a ha (actualPhysicalWeakConormalEntry D f g) _
      (actualPhysicalWeakConormalEntry_trace_germ hn hY hx D f g) ((G.matrix_entry_bound f g).2 n hnN)
    exact h.trans_eq (by dsimp only [P,β]; ring)
  · intro i j f g
    obtain ⟨G'⟩ := hR i j
    let R := F.rotationComm hY i j
    have h := R.abs_iteratedDerivative_pair_of_entry hn hY hx (finiteHarmonicSmoothTraceL f)
      (finiteHarmonicSmoothTraceL g) n a ha (actualPhysicalRotatedConormalEntry D i j f g) _
      (actualPhysicalRotatedConormalEntry_trace_germ hn hY hx D i j f g) ((G'.matrix_entry_bound f g).2 n hnN)
    change |⟪smoothSphereTraceL2 hn (((F.rotationComm hY i j).iteratedDerivative hY n a).1 x
        (finiteHarmonicSmoothTraceL f)),smoothSphereTraceL2 hn (finiteHarmonicSmoothTraceL g)⟫_ℝ| ≤ _ at h
    rw [F.iteratedDerivative_rotationComm hn hY i j n a hx] at h
    exact h.trans_eq (by dsimp only [Q,β]; ring)

end CalderonN
