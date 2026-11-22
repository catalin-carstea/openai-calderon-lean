module

public import Proof.CalderonN.PhysicalTraceScalarJets

import Proof.CalderonN.UniformLogRadiusChartJets
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! The physical radius and its first derivative are bounded coefficients
at the scaled chart, with the radius absorbing one power of beta. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_radius_firstDerivative_bounds {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ floor ≥ 1,∀ ε ≤ 1,∀ d : Data dim,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ x ∈ Y,
      let β := beta d.γ d.radius x
      let r := d.radius
      let b (i : I dim) (y : X dim) := fderiv ℝ r y (axis i)
      |r x| ≤ C ∧ (∀ a : X dim,‖a‖ ≤ 1 → |fderiv ℝ r x a| ≤ C*β) ∧
      (∀ i, |b i x| ≤ C) ∧
      (∀ i a, ‖a‖ ≤ 1 → |fderiv ℝ (b i) x a| ≤ C*β) := by
  obtain ⟨L,hL,hLog⟩ := uniform_background_logRadius_chart_jets hY hΩ hSub 2 (by decide) hm K M Cj hK
  let L₀ := max 1 L
  obtain ⟨R,hR,hRJ⟩ := uniform_radius_scaled_chart_jets hY 2 L₀ (le_max_left _ _)
  let C := max 1 R
  refine ⟨C,le_max_left _ _,?_⟩
  intro floor hFloor ε hε d hd x hx
  dsimp only
  let β := beta d.γ d.radius x
  let r := d.radius
  have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  have hr := hd.2.2.2.2.1.1
  have hp (y : X dim) (hy : y ∈ Y) : 0 < r y := (hd.2.2.2.2.1.2 y hy).1
  have hβ' := zero_le_one.trans hβ
  have hRβ : r x*β ≤ 1 := by
    calc
      r x*β ≤ r x*β^2 := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hβ' (sub_nonneg.mpr hβ)])
        (hp x hx).le
      _ ≤ ε := (hd.2.2.2.2.2 x hx).2
      _ ≤ 1 := hε
  have hr₁ : r x ≤ 1 := (le_mul_of_one_le_right (hp x hx).le hβ).trans hRβ
  have hLog' n (hn : n ≤ 2) (hn₁ : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n (fun y => Real.log (r y)) x‖ ≤ L₀*β^n :=
    (hLog d.γ d.g₁ d.g₂ d.frame hd.1 r floor c₀ hFloor hd.2.2.2.2.1 x hx n hn hn₁).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hβ' _))
  obtain ⟨hRatio,_⟩ := hRJ r hr x hx hp β hβ hLog'
  have hJet := hRatio.const_smul (r x) (hp x hx).le
  have he : (fun v : X dim => r x • (r (x+β⁻¹ • v)/r x)) = fun v => r (x+β⁻¹ • v) := by
    funext v
    change r x*(r (x+β⁻¹ • v)/r x) = _
    field_simp [(hp x hx).ne']
  rw [he] at hJet
  have hDeriv := localSmoothJetBudget_scaled_chart_bound hβ hJet
  have hD₁ : ‖fderiv ℝ r x‖ ≤ R := by
    have h := hDeriv 1 (by decide)
    rw [norm_iteratedFDeriv_one,pow_one] at h
    exact h.trans ((by rw [mul_right_comm]; exact mul_le_of_le_one_left hR hRβ) : r x*R*β ≤ R)
  have hD₂ : ‖fderiv ℝ (fderiv ℝ r) x‖ ≤ R*β := by
    have h := hDeriv 2 (by decide)
    rw [← norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_one] at h
    exact h.trans (by nlinarith only [mul_nonneg (show 0 ≤ R*β by positivity) (sub_nonneg.mpr hRβ)])
  have hD (a : X dim) (ha : ‖a‖ ≤ 1) : |fderiv ℝ r x a| ≤ C :=
    ((fderiv ℝ r x).le_opNorm a).trans ((mul_le_of_le_one_right (norm_nonneg _) ha).trans
      (hD₁.trans (le_max_right _ _)))
  refine ⟨(by rwa [abs_of_pos (hp x hx)] : |r x| ≤ 1).trans (le_max_left _ _),
    fun a ha => (hD a ha).trans (le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _)) hβ),
    fun i => hD (axis i) (norm_axis i).le,?_⟩
  intro i a ha
  let E := ContinuousLinearMap.apply ℝ ℝ (axis i)
  have hE : ‖E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    rw [one_mul]
    exact (T.le_opNorm _).trans_eq (by rw [norm_axis,mul_one])
  have hSmooth := (hr.contDiffAt (hY.mem_nhds hx)).fderiv_right (m:=∞) (by simp)
  change |fderiv ℝ (E ∘ fderiv ℝ r) x a| ≤ C*β
  rw [(E.hasFDerivAt.comp x (hSmooth.differentiableAt (by simp)).hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply]
  exact (E.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hE).trans
    (((fderiv ℝ (fderiv ℝ r) x).le_opNorm a).trans
      ((mul_le_of_le_one_right (norm_nonneg _) ha).trans
        (hD₂.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hβ')))))

end CalderonN
