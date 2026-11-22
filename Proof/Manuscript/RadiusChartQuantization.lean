module

public import Proof.Manuscript.RadiusAngularLine
public import Proof.Manuscript.CompactAngularFourier

import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter MeasureTheory Set
open scoped ContDiff Topology
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {dim : ℕ}
local notation "E" => AngularCoordinates dim

private theorem continuous_angularSymbol_slice
    {a : P × E → E → ℂ} {U : Set P}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    {p : P} (hp : p ∈ U) (x : E) : Continuous (a (p,x)) := by
  apply ContDiff.continuous (𝕜 := ℝ) (n := ∞)
  apply contDiffOn_univ.mp
  exact ha.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => ⟨⟨hp,mem_univ _⟩,mem_univ _⟩)

private theorem angularFourierTransform_integrable_linearGrowth (f : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hK : HasCompactSupport f) (C : ℝ) :
    Integrable (fun ξ => C*(1+‖ξ‖)*‖angularFourierTransform f ξ‖) := by
  have h₀ := angularFourierTransform_integrable_norm_weight f hf hK 0
  have h₁ := angularFourierTransform_integrable_norm_weight f hf hK 1
  simp only [pow_zero,one_mul] at h₀
  simp only [pow_one] at h₁
  have h := (h₀.add h₁).const_mul C
  simpa only [Pi.add_apply,add_mul,one_mul,mul_assoc] using h

/-- A chart's actual localized operator differentiates in the independent
radius by differentiating its order-one symbol under the Fourier integral. -/
theorem radiusChartQuantization_first
    {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} (hU : IsOpen U)
    {a : P × E → E → ℂ} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (q : Q) (x : E) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (hK : HasCompactSupport f)
    (A : ℝ → ℂ) (c : ℂ) {O : Set ℝ} (hO : O ∈ 𝓝 (0:ℝ))
    (hOU : ∀ r ∈ O, e (q,r) ∈ U)
    (hEq : ∀ r ∈ O,
      c * A r = ∫ ξ, angularFourierPhase x ξ * a (e (q,r),x) ξ * angularFourierTransform f ξ)
    (hInt : Integrable (fun ξ => angularFourierPhase x ξ * a (e (q,0),x) ξ *
      angularFourierTransform f ξ))
    (C : ℝ)
    (hBound : ∀ r ∈ O, ∀ ξ, ‖radiusFirstAngular e a (e (q,r),x) ξ‖ ≤ C*(1+‖ξ‖)) :
    Integrable (fun ξ => angularFourierPhase x ξ * radiusFirstAngular e a (e (q,0),x) ξ *
      angularFourierTransform f ξ) ∧
    c * deriv A 0 = ∫ ξ, angularFourierPhase x ξ * radiusFirstAngular e a (e (q,0),x) ξ *
      angularFourierTransform f ξ := by
  let s (r : ℝ) (ξ : E) := a (e (q,r),x) ξ
  let ds (r : ℝ) (ξ : E) := radiusFirstAngular e a (e (q,r),x) ξ
  let v (ξ : E) := angularFourierPhase x ξ * angularFourierTransform f ξ
  have hPhase : Continuous (angularFourierPhase x) := by unfold angularFourierPhase; fun_prop
  have hV : Continuous v := hPhase.mul (angularFourierTransform_continuous f hf hK)
  have h0 : (0:ℝ) ∈ O := mem_of_mem_nhds hO
  have hSwap (g : E → ℂ) (ξ : E) :
      angularFourierPhase x ξ * g ξ * angularFourierTransform f ξ = g ξ * v ξ := by
    unfold v
    ring
  have hds : ContDiffOn ℝ ∞ (Function.uncurry (radiusFirstAngular e a)) ((U ×ˢ univ) ×ˢ univ) :=
    radiusFirstAngular_contDiffOn hU isOpen_univ ha
  have hS (r : ℝ) (hr : r ∈ O) : Continuous (s r) := continuous_angularSymbol_slice ha (hOU r hr) x
  have hdS : Continuous (ds 0) := continuous_angularSymbol_slice hds (hOU 0 h0) x
  have hD (ξ : E) (r : ℝ) (hr : r ∈ O) : HasDerivAt (fun r' => s r' ξ) (ds r ξ) r :=
    hasDerivAt_radiusFirstAngular_line hU isOpen_univ ha q r (hOU r hr) x (mem_univ _)
  have hBd : ∀ᵐ ξ, ∀ r ∈ O, ‖ds r ξ‖ * ‖v ξ‖ ≤ C*(1+‖ξ‖)*‖angularFourierTransform f ξ‖ := by
    apply Eventually.of_forall
    intro ξ r hr
    dsimp only [v]
    rw [norm_mul,angularFourierPhase_norm,one_mul]
    exact mul_le_mul_of_nonneg_right (hBound r hr ξ) (norm_nonneg _)
  have hQ := radiusLocalized_derivative_of_quantization A c s ds v hO
    (fun r hr => by simpa only [s,hSwap] using hEq r hr)
    (fun r hr => ((hS r hr).mul hV).aestronglyMeasurable)
    (by simpa only [s,← hSwap] using hInt)
    (hdS.mul hV).aestronglyMeasurable
    (fun ξ => C*(1+‖ξ‖)*‖angularFourierTransform f ξ‖)
    (angularFourierTransform_integrable_linearGrowth f hf hK C) hBd (Eventually.of_forall hD)
  simpa only [ds,hSwap] using hQ

/-- The literal symbol Taylor remainder is the exact chart quantization of
the quadratic operator remainder at each nonzero admitted radius. -/
theorem radiusChartQuantization_remainder
    {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} (hU : IsOpen U)
    {a : P × E → E → ℂ} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (q : Q) (r : ℝ) (hr : r ≠ 0) (hq : ∀ t ∈ Icc (0:ℝ) 1, e (q,t*r) ∈ U)
    (x : E) (f : E → ℂ) (A : ℝ → ℂ) (c : ℂ)
    (hEq₀ : c * A 0 = ∫ ξ, angularFourierPhase x ξ * a (e (q,0),x) ξ * angularFourierTransform f ξ)
    (hEq : c * A r = ∫ ξ, angularFourierPhase x ξ * a (e (q,r),x) ξ * angularFourierTransform f ξ)
    (hFirst : c * deriv A 0 = ∫ ξ, angularFourierPhase x ξ *
      radiusFirstAngular e a (e (q,0),x) ξ * angularFourierTransform f ξ)
    (hInt₀ : Integrable (fun ξ => angularFourierPhase x ξ * a (e (q,0),x) ξ *
      angularFourierTransform f ξ))
    (hInt : Integrable (fun ξ => angularFourierPhase x ξ * a (e (q,r),x) ξ *
      angularFourierTransform f ξ))
    (hIntFirst : Integrable (fun ξ => angularFourierPhase x ξ * radiusFirstAngular e a
      (e (q,0),x) ξ * angularFourierTransform f ξ)) :
    Integrable (fun ξ => angularFourierPhase x ξ * radiusTaylorAngular e a (e (q,r),x) ξ *
      angularFourierTransform f ξ) ∧
    c * ((r^2)⁻¹ • (A r - A 0 - r • deriv A 0)) =
      ∫ ξ, angularFourierPhase x ξ * radiusTaylorAngular e a (e (q,r),x) ξ *
        angularFourierTransform f ξ := by
  let s (r : ℝ) (ξ : E) := a (e (q,r),x) ξ
  let ds (r : ℝ) (ξ : E) := radiusFirstAngular e a (e (q,r),x) ξ
  let v (ξ : E) := angularFourierPhase x ξ * angularFourierTransform f ξ
  let R (ξ : E) := radiusTaylorAngular e a (e (q,r),x) ξ
  have hSwap (g : E → ℂ) (ξ : E) :
      angularFourierPhase x ξ * g ξ * angularFourierTransform f ξ = g ξ * v ξ := by
    unfold v
    ring
  have h := radiusLocalized_remainder_of_quantization A c s ds R v r hr
    (by simpa only [s,hSwap] using hEq₀) (by simpa only [s,hSwap] using hEq)
    (by simpa only [ds,hSwap] using hFirst) (by simpa only [s,← hSwap] using hInt₀)
    (by simpa only [s,← hSwap] using hInt) (by simpa only [ds,← hSwap] using hIntFirst)
    (fun ξ => radiusAngular_taylor_eq hU isOpen_univ ha q r hq x (mem_univ ξ))
  simpa only [R,hSwap] using h

end CalderonPaper
