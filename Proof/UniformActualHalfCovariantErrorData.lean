import Proof.UniformActualHalfCovariantDerivative
import Proof.BalancedDegreeCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- SAME globally smooth physical endpoints, including the literal Green
    covariant derivative with radius-beta and epsilon bounds. -/
def ActualHalfCovariantErrorData (Y : Set X) (d : Data) (a : X)
    (A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (C0 C1 ε : ℝ) : Prop :=
  ∃ Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
  ∃ Hi : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    ContDiffOn ℝ ∞ Lo Y ∧ ContDiffOn ℝ ∞ Hi Y ∧ ∀ x ∈ Y,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x)=
        (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi x)=
        (actualFirstAdjointErrorFamily d a A G x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Hi x)=
        (Lo x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖Lo x‖ ≤ C0*‖a‖*d.radius x ∧ ‖Hi x‖ ≤ C0*‖a‖*d.radius x ∧
      ∀ b : X,‖b‖ ≤ 1 →
        ‖halfOperatorCovariantDerivativeL d Lo Hi x b‖ ≤ C1*‖a‖*d.radius x*beta d.γ d.radius x ∧
        ‖halfOperatorCovariantDerivativeL d Lo Hi x b‖ ≤ C1*‖a‖*ε

/-- Closed common producer. Smooth physical endpoints and the covariant
    estimate are constructed; none are added as theorem premises. -/
theorem uniform_actual_first_error_half_covariant_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 C1 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ a : X,
      ∀ R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y → ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ActualHalfCovariantErrorData Y d a A G C0 C1 ε := by
  obtain ⟨ηE,C0,hηE,hηE1,hC0,hEndpoints⟩ := uniform_actual_first_adjoint_error_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,C1,hηD,_hηD1,hC1,hDerivative⟩ := uniform_actual_first_error_half_covariant_derivative
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηE ηD,C0,C1,lt_min hηE hηD,(min_le_left _ _).trans hηE1,hC0,hC1,?_⟩
  intro floor hf ε hε hSmall d hd a R A G hAS hGS hR hA hG
  obtain ⟨Lo,Hi,hLS,hHS,hAll⟩ := hEndpoints floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd a R A G hR hA hG
  refine ⟨Lo,Hi,hLS,hHS,?_⟩
  intro x hx
  have hLow (y) (hy : y ∈ Y) := (hAll y hy).1
  have hHigh (y) (hy : y ∈ Y) := (hAll y hy).2.1
  refine ⟨hLow x hx,hHigh x hx,balanced_endpoint_pair_of_coarse _ _ _ (hLow x hx) (hHigh x hx),
    (hAll x hx).2.2.1,(hAll x hx).2.2.2,?_⟩
  intro b hb
  have hN := hDerivative floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd R A hAS hR hA
    a G hGS hG Lo Hi hLS hLow hHigh x hx b hb
  have hr := (hd.2.2.2.2.1.2 x hx).1
  have hR := radius_bounds (d.radius x) (beta d.γ d.radius x) floor ε hr.le hf
    (hd.2.2.2.2.1.2 x hx).2.1 (hd.2.2.2.2.2 x hx).2
  have hrβ : d.radius x*beta d.γ d.radius x ≤ ε := hR.2.1.trans (div_le_self hε hf)
  refine ⟨hN,hN.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrβ (mul_nonneg hC1 (norm_nonneg a))
end ShrinkingSpheres
