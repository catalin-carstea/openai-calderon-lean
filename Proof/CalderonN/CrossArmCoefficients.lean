module

public import Proof.CalderonN.CrossCoefficients
public import Proof.CalderonN.CrossPairing

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace LocalMetricExtension

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {m₁ m₂ : Measure α} {n₁ n₂ : Measure β}
  [SFinite m₁] [SFinite m₂] [SFinite n₁] [SFinite n₂]

/-- Restriction of a square-integrable class along measure domination. -/
def restrictL2 {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    (h : μ ≤ ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp) (by rwa [one_smul])

theorem restrictL2_ae {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    (h : μ ≤ ν) (q : Lp ℝ 2 ν) : (restrictL2 h q : Ω → ℝ) =ᵐ[μ] q :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp) (by rwa [one_smul]) q

theorem norm_restrictL2_le {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    (h : μ ≤ ν) : ‖restrictL2 h‖ ≤ 1 := by
  unfold restrictL2
  simpa using Lp.norm_LpToLpOfMeasureLeSMul_le (p := 2) (E := ℝ)
    (c := (1 : ℝ≥0∞)) (by simp) (by rwa [one_smul] : μ ≤ (1 : ℝ≥0∞) • ν)

/-- Coefficients continued from the thin first-variable cross arm. -/
@[expose] def crossArmCoefficient (w : Lp ℝ 2 m₂) (μ : ℝ) (q : Lp ℝ 2 (m₂.prod n₂)) : Lp ℝ 2 n₂ :=
  (μ ^ 2)⁻¹ • tensorCoefficient w q

theorem norm_crossArmCoefficient_le {w : Lp ℝ 2 m₂} {μ : ℝ}
    (hμ : 0 < μ) (hw : ‖w‖ = μ) (q : Lp ℝ 2 (m₂.prod n₂)) :
    ‖crossArmCoefficient w μ q‖ ≤ μ⁻¹ * ‖q‖ := by
  rw [crossArmCoefficient, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine (mul_le_mul_of_nonneg_left (norm_tensorCoefficient_le w q) (by positivity)).trans_eq ?_
  rw [hw]
  field_simp

theorem crossArmCoefficient_ae_integral [IsFiniteMeasure n₂]
    (w : Lp ℝ 2 m₂) (μ : ℝ) (q : Lp ℝ 2 (m₂.prod n₂)) :
    (crossArmCoefficient w μ q : β → ℝ) =ᵐ[n₂]
      fun y => (μ ^ 2)⁻¹ * ∫ x, w x * q (x,y) ∂m₂ := by
  filter_upwards [Lp.coeFn_smul (μ ^ 2)⁻¹ (tensorCoefficient w q),
    tensorCoefficient_ae_integral w q] with y h₁ h₂
  rw [crossArmCoefficient, h₁, Pi.smul_apply, h₂, smul_eq_mul]

/-- The same coefficient on the two arms, with the thin-arm singular
normalization determined by the restriction Gram identity. -/
theorem crossArmCoefficient_restrict_eq [IsFiniteMeasure n₁] [IsFiniteMeasure n₂]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} (w : HilbertBasis ι ℝ E) (μ : ι → ℝ)
    (R : E →L[ℝ] Lp ℝ 2 m₂) (J : E →ₗᵢ[ℝ] Lp ℝ 2 m₁)
    (hm : m₂ ≤ m₁) (hn : n₁ ≤ n₂)
    (hR : ∀ u : E, R u = restrictL2 hm (J u))
    (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i, (R.adjoint ∘L R) (w i) = μ i ^ 2 • w i)
    (q₁ : Lp ℝ 2 (m₁.prod n₁)) (q₂ : Lp ℝ 2 (m₂.prod n₂))
    (hagree : (q₁ : α × β → ℝ) =ᵐ[m₂.prod n₁] q₂)
    (hslice : ∀ᵐ y ∂n₁, ∃ u : E, (J u : α → ℝ) =ᵐ[m₁] fun x => q₁ (x,y)) (i : ι) :
    restrictL2 hn (crossArmCoefficient (R (w i)) (μ i) q₂) = tensorCoefficient (J (w i)) q₁ := by
  apply Lp.ext
  have hswap := (Measure.measurePreserving_swap (μ := n₁) (ν := m₂)).quasiMeasurePreserving.ae hagree
  filter_upwards [restrictL2_ae hn (crossArmCoefficient (R (w i)) (μ i) q₂),
    ae_mono hn (crossArmCoefficient_ae_integral
      (R (w i)) (μ i) q₂), tensorCoefficient_ae_integral (J (w i)) q₁,
    Measure.ae_ae_of_ae_prod (μ := n₁) (ν := m₂) (p := fun z => q₁ (z.2,z.1) = q₂ (z.2,z.1))
      hswap, hslice] with y h₁ h₂ h₃ heq hslice'
  obtain ⟨u, hu⟩ := hslice'
  have hright : (∫ x, J (w i) x * q₁ (x,y) ∂m₁) = inner ℝ (J u) (J (w i)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx]
  have hleft : (∫ x, R (w i) x * q₂ (x,y) ∂m₂) = inner ℝ (R u) (R (w i)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have hRu : (R u : α → ℝ) =ᵐ[m₂] J u := by
      rw [hR]
      exact restrictL2_ae hm (J u)
    filter_upwards [heq, hRu, ae_mono hm hu] with x hx hxR hxu
    rw [RCLike.inner_apply, conj_trivial, hxR, hxu, hx]
  rw [h₁, h₂, h₃, hleft, hright]
  have hcoef := singularCoefficient_restrict R w μ hμ heigen u i
  change (μ i ^ 2)⁻¹ * inner ℝ (R (w i)) (R u) = inner ℝ (w i) u at hcoef
  rw [real_inner_comm (R (w i)) (R u), hcoef, J.inner_map_map, real_inner_comm]

omit [SFinite m₁] in
/-- An orthogonal test coefficient vanishes on the observed second arm.
The only reconstruction used here is the actual first-arm slice. -/
theorem restrict_tensorCoefficient_eq_zero_of_orthogonal [IsFiniteMeasure n₂]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E →L[ℝ] Lp ℝ 2 m₂) (J : E →L[ℝ] Lp ℝ 2 m₁)
    (hm : m₂ ≤ m₁) (hn : n₁ ≤ n₂)
    (hR : ∀ u : E, R u = restrictL2 hm (J u))
    (q₁ : Lp ℝ 2 (m₁.prod n₁)) (q₂ : Lp ℝ 2 (m₂.prod n₂))
    (hagree : (q₁ : α × β → ℝ) =ᵐ[m₂.prod n₁] q₂)
    (hslice : ∀ᵐ y ∂n₁, ∃ u : E, (J u : α → ℝ) =ᵐ[m₁] fun x => q₁ (x,y))
    (z : Lp ℝ 2 m₂) (hz : ∀ u : E, inner ℝ (R u) z = 0) :
    restrictL2 hn (tensorCoefficient z q₂) = 0 := by
  apply Lp.ext
  have hswap := (Measure.measurePreserving_swap (μ := n₁) (ν := m₂)).quasiMeasurePreserving.ae hagree
  filter_upwards [restrictL2_ae hn (tensorCoefficient z q₂), ae_mono hn (tensorCoefficient_ae_integral z q₂),
    Measure.ae_ae_of_ae_prod hswap, hslice, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := n₁)]
    with y h₁ h₂ heq hslice' hzero
  obtain ⟨u, hu⟩ := hslice'
  rw [h₁, h₂, hzero, Pi.zero_apply, ← hz u, L2.inner_def]
  apply integral_congr_ae
  have hRu : (R u : α → ℝ) =ᵐ[m₂] J u := by
    rw [hR]
    exact restrictL2_ae hm (J u)
  filter_upwards [heq, hRu, ae_mono hm hu] with x hx hxR hxu
  change q₁ (x,y) = q₂ (x,y) at hx
  rw [RCLike.inner_apply, conj_trivial, hxR, hxu, hx]

end LocalMetricExtension
