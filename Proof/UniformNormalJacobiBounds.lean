import Proof.NormalJacobiBounds
import Proof.UniformNormalGeodesicBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set
namespace ShrinkingSpheres

def backgroundConnectionDerivativeBudget {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  27*(81*K^2*|M ⟨1,by omega⟩|^2+9*K*|M ⟨2,by omega⟩|)

def normalVariationBudget {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  1+2*(243*K*|M ⟨1,by omega⟩|)*K+backgroundConnectionDerivativeBudget hm K M*K^2

lemma Background.connection_derivative_budget {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 2 ≤ m) {y : X} (hy : y ∈ Ω) :
    ‖fderiv ℝ (connectionBilinear g) y‖ ≤ backgroundConnectionDerivativeBudget hm K M := by
  have hh := h.1.connection_operator_bounds hΩ hK hy |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
    (abs_nonneg _) (abs_nonneg _)
    (fun i j => (h.reference_fderiv_bound (by omega) hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_second_fderiv_bound hm hy i j).trans (le_abs_self _))
  exact hh.2

/-- The actual normal first variation has one common exponential bound computed
    from the frozen first two background metric budgets. -/
theorem Background.normal_velocity_variation_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 2 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : X} (hy : y ∈ Y) (v u : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖normalVelocityVariation expMap y v u t‖ ≤ ‖u‖*Real.exp (normalVariationBudget hm K M*t) := by
  have hC : 0 ≤ 243*K*|M ⟨1,by omega⟩| := by positivity
  have hD : 0 ≤ backgroundConnectionDerivativeBudget hm K M := by
    unfold backgroundConnectionDerivativeBudget
    positivity
  exact hN.velocity_variation_bound hΩ h.1 hK hC hD
    (fun x hx => h.connection_budget hK (by omega) hx)
    (fun x hx => h.connection_derivative_budget hΩ hK hm hx) hy v u hv hv1 ht

end ShrinkingSpheres
