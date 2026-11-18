import Proof.BackgroundCurvature
import Proof.PhysicalModeCoercivity

noncomputable section
set_option autoImplicit false
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

def backgroundCoercivityFloor {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (c₀ : ℝ) : ℝ :=
  max 1 (450*backgroundCurvatureBudget hm K M / c₀)

def backgroundModeCoercivityConstant (c₀ : ℝ) : ℝ := profileCoercivityConstant (min (c₀/8) 1) c₀

lemma backgroundCoercivityFloor_ge_one {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (c₀ : ℝ) :
    1 ≤ backgroundCoercivityFloor hm K M c₀ := le_max_left _ _

lemma backgroundModeCoercivityConstant_pos (c₀ : ℝ) (hc₀ : 0 < c₀) :
    0 < backgroundModeCoercivityConstant c₀ :=
  profileCoercivityConstant_pos _ c₀ (lt_min (by positivity) zero_lt_one) hc₀

variable {ι : Type*} [Fintype ι]

/-- Degreewise coercivity with constants from the actual frozen background budgets. The
    curvature premise has been proved, and the radius is any admissible profile. -/
theorem Background.energySq_finite_mode_coercive {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hsub : Y ⊆ Ω) {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (hbg : Background Ω K M g g₁ g₂ e)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : backgroundCoercivityFloor hm K M c₀ ≤ floor)
    (ℓ : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ j, (b j).IsHomogeneous (ℓ+1))
    (hΔ : ∀ j, laplacian (b j) = 0) (c : X → ι → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    backgroundModeCoercivityConstant c₀ * energySq Y g e r (complexPolynomialField g e b c) ≤
      outputSq Y g e (sphereRaisedField g e b c (fun x => Real.log (r x)) ℓ) -
        outputSq Y g e (sphereLoweredField g e b c (fun x => Real.log (r x)) ℓ) := by
  have hE : Elliptic Y K g := ⟨fun i j => (hbg.1.1 i j).mono hsub, fun y hy => hbg.1.2 y (hsub hy)⟩
  have he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y :=
    fun i => (hbg.2.2.2.2.2.2.1 i).mono hsub
  have hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0 :=
    fun y hy => hbg.2.2.2.2.2.2.2 y (hsub hy)
  have hf : 1 ≤ floor := (backgroundCoercivityFloor_ge_one hm K M c₀).trans hfloor
  have hcurvf : 450*backgroundCurvatureBudget hm K M/c₀ ≤ floor := (le_max_right _ _).trans hfloor
  have hthreshold : 450*backgroundCurvatureBudget hm K M ≤ c₀*floor := by
    have hh := (div_le_iff₀ hc₀).mp hcurvf
    simpa only [mul_comm] using hh
  exact hp.energySq_finite_mode_coercive hY hE hK e he hframe hc₀ hf
    (backgroundCurvatureBudget hm K M) (backgroundCurvatureBudget_nonneg hm K hK.le M)
    (fun y hy i j a b => hbg.frameCurvatureCoefficient_uniform_bound hΩ hK hm (hsub hy) i j a b)
    hthreshold ℓ b hb hΔ c hc hcompact hsupp (min (c₀/8) 1)
    (lt_min (by positivity) zero_lt_one) (min_le_left _ _) ((min_le_right _ _).trans hf)

end ShrinkingSpheres
