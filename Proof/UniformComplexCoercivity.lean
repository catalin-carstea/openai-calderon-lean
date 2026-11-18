import Proof.ComplexRaisingEnergy

noncomputable section
set_option autoImplicit false
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

/-- The frozen complex finite-mode energy has a uniform positive lower bound for every
    admissible radius, with its curvature constant produced from the given background. -/
theorem Background.energySq_complex_finite_mode_coercive {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hsub : Y ⊆ Ω) {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (hbg : Background Ω K M g g₁ g₂ e)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : backgroundCoercivityFloor hm K M c₀ ≤ floor)
    (ℓ : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ j, (b j).IsHomogeneous (ℓ+1))
    (hΔ : ∀ j, laplacian (b j) = 0) (c d : X → ι → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (hcompactc : HasCompactSupport c) (hcompactd : HasCompactSupport d) (hsuppc : tsupport c ⊆ Y) (hsuppd : tsupport d ⊆ Y) :
    backgroundModeCoercivityConstant c₀ * energySq Y g e r (pairedPolynomialField g e b c d) ≤
      outputSq Y g e (pairedRaisedField g e b c d (fun x => Real.log (r x)) ℓ) -
        outputSq Y g e (pairedLoweredField g e b c d (fun x => Real.log (r x)) ℓ) := by
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
  exact hp.energySq_paired_mode_coercive hY hE hK e he hframe hc₀ hf
    (backgroundCurvatureBudget hm K M) (backgroundCurvatureBudget_nonneg hm K hK.le M)
    (fun y hy i j a b => hbg.frameCurvatureCoefficient_uniform_bound hΩ hK hm (hsub hy) i j a b)
    hthreshold ℓ b hb hΔ c d hc hd hcompactc hcompactd hsuppc hsuppd (min (c₀/8) 1)
    (lt_min (by positivity) zero_lt_one) (min_le_left _ _) ((min_le_right _ _).trans hf)

end ShrinkingSpheres
