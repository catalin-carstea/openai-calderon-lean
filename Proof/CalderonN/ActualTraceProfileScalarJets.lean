module

public import Proof.CalderonN.PhysicalTraceScalarJets
public import Proof.CalderonN.UniformLogRadiusChartJets

import Proof.CalderonN.CoordinateJets
public import Proof.CalderonN.TraceCoordinateModel
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! Radius, its coordinate gradients, and the logarithmic radius
gradients at the physical rate of the small chart. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem uniform_actualTraceProfile_scalar_jets
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m N : ℕ} (hm : N+1 ≤ m) (hN : N ≤ 8) (K ρ c₀ : ℝ)
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 0 < K) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ floor ≥ 1,∀ ε,∀ d : Data dim,Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ x ∈ Y,
        let β := beta d.γ d.radius x
        (∀ n ≤ N,‖iteratedFDeriv ℝ n d.radius x‖ ≤ C*d.radius x*β^n) ∧
        (∀ i n,n+1 ≤ N → ‖iteratedFDeriv ℝ n (coordDeriv i d.radius) x‖ ≤ C*d.radius x*β^(n+1)) ∧
        (∀ i n,n+1 ≤ N → ‖iteratedFDeriv ℝ n (traceCoordinateLogGradient d.radius i) x‖ ≤ C*β^(n+1)) := by
  obtain ⟨J,hJ,hLog⟩ := uniform_background_logRadius_chart_jets hY hΩ hSub N hN hm K M Cj hK
  obtain ⟨D,hD,hRad⟩ := uniform_radius_scaled_chart_jets hY N (1+J) (le_add_of_nonneg_right hJ)
  let C := 1+J+D
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hJ,hD]
  refine ⟨C,hC,?_⟩
  intro floor hFloor ε d hd x hx
  dsimp only
  let β := beta d.γ d.radius x
  have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  have hβp := zero_lt_one.trans_le hβ
  have hr := hd.2.2.2.2.1.1
  have hrp (y : X dim) (hy : y ∈ Y) := (hd.2.2.2.2.1.2 y hy).1
  have hlog := hr.log (fun y hy => (hrp y hy).ne')
  have hlog' := hLog d.γ d.g₁ d.g₂ d.frame hd.1 d.radius floor c₀ hFloor hd.2.2.2.2.1 x hx
  have hR := (hRad d.radius hr x hx hrp β hβ (fun n hn hn₀ =>
    (hlog' n hn hn₀).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg hβp.le n)))).1
  have hR' := hR.const_smul (d.radius x) (hrp x hx).le
  have hEq : (fun v : X dim => d.radius x • (d.radius (x+β⁻¹ • v)/d.radius x)) =
      fun v => d.radius (x+β⁻¹ • v) := by
    funext v
    rw [smul_eq_mul]
    field_simp [(hrp x hx).ne']
  rw [hEq] at hR'
  have hCJ : J ≤ C := by dsimp only [C]; linarith only [hD]
  have hCD : d.radius x*D ≤ C*d.radius x := by
    rw [mul_comm (d.radius x) D]
    exact mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [hJ]) (hrp x hx).le
  have hRn := localSmoothJetBudget_scaled_chart_bound hβ (hR'.enlarge hCD)
  exact ⟨hRn,fun i n hn =>
    (norm_iteratedFDeriv_coordDeriv_le (hr.contDiffAt (hY.mem_nhds hx)) i n).trans (hRn (n+1) hn),
    fun i n hn =>
      (norm_iteratedFDeriv_coordDeriv_le (hlog.contDiffAt (hY.mem_nhds hx)) i n).trans
        ((hlog' (n+1) hn (by omega)).trans (mul_le_mul_of_nonneg_right hCJ (pow_nonneg hβp.le _)))⟩

end CalderonN
