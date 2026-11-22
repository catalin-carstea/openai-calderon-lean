module

public import Proof.CalderonN.ActualTraceProfileScalarJets
public import Proof.CalderonN.UniformMetricInverseEntryJets

import Proof.CalderonN.NormalizedRadialInverseJets
import Proof.CalderonN.WeakEnergyConormalJets
import Proof.CalderonN.PrincipalMetric
import Mathlib.Tactic

/-! The small second-base coefficient and the normalized difference
of principal tensors at the actual radius scale. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def tracePrincipalSmallDifference (d : Data dim) (i j : I dim) (x : X dim) : ℝ :=
  ((principal d.γ d.g₂ x-(d.γ x)⁻¹) i j)/d.radius x

theorem contDiffOn_tracePrincipalSmallDifference {Y : Set (X dim)} {d : Data dim}
    (hγ : SmoothMetric Y d.γ) (hg₂ : SmoothMetric Y d.g₂)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0) (i j : I dim) :
    ContDiffOn ℝ ∞ (tracePrincipalSmallDifference d i j) Y :=
  ((contDiffOn_principal_entry hγ hg₂ i j).sub (contDiffOn_metric_inv_entry hγ i j)).div hr hr₀

theorem uniform_actualPrincipalTrace_scalar_jets
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 0 < K) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d : Data dim,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ x ∈ Y,
      let β := beta d.γ d.radius x
      (∀ i j n,n ≤ 3 → ‖iteratedFDeriv ℝ n (tracePrincipalSmallDifference d i j) x‖ ≤ C*ε*β^n) ∧
      (∀ i j n,n ≤ 3 → ‖iteratedFDeriv ℝ n (fun y => d.radius y*principal d.γ d.g₂ y i j) x‖ ≤
        (C*ε*(β⁻¹)^2)*β^n) := by
  obtain ⟨P,hP,hRad⟩ := uniform_actualTraceProfile_scalar_jets hY hΩ hSub hm (by decide : 3 ≤ 8) K ρ c₀ M Cj hK
  obtain ⟨G,hG,hInv⟩ := uniform_metric_inverse_entry_jet_budget hΩ 3 (by omega) K M hK
  obtain ⟨J,hJ,hLog⟩ := uniform_background_logRadius_chart_jets hY hΩ hSub 3 (by decide) hm K M Cj hK
  obtain ⟨D,hD,hDiff⟩ := uniform_physical_trace_small_scalar_jets (dim:=dim) hY 3 (by decide) (1+J)
    (le_add_of_nonneg_right hJ)
  let L := (2:ℝ)^3*‖ContinuousLinearMap.mul ℝ ℝ‖
  let Q := G+L*P*D
  let C := 1+D+L*P*Q
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity : 0 ≤ D+L*P*Q) |>.trans_eq (by dsimp only [C]; ring)
  refine ⟨C,hC,?_⟩
  intro floor hFloor ε hε hs d hd x hx
  dsimp only
  let r := d.radius
  let β := beta d.γ r x
  let p (w : X dim) := x+β⁻¹ • w
  have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  have hβ' := zero_lt_one.trans_le hβ
  have hr := hd.2.2.2.2.1.1
  have hrp (y : X dim) (hy : y ∈ Y) := (hd.2.2.2.2.1.2 y hy).1
  have hγ : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have hg₂ : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun y hy => hd.1.2.2.1.2 y (hSub hy)⟩
  have hSmall : r x ≤ ε*(β⁻¹)^2 := by
    rw [inv_pow,← div_eq_mul_inv,le_div_iff₀ (sq_pos_of_pos hβ')]
    exact (hd.2.2.2.2.2 x hx).2
  have hr₁ : r x ≤ 1 := by
    have h := le_mul_of_one_le_right (hrp x hx).le (one_le_pow₀ hβ (n:=2))
    exact (h.trans (hd.2.2.2.2.2 x hx).2).trans hs
  have hRad' := (hRad floor hFloor ε d hd x hx).1
  have hRadius : LocalSmoothJetBudget (r ∘ p) 0 3 (P*r x) :=
    localSmoothJetBudget_scaled_chart hβ (hr.contDiffAt (hY.mem_nhds hx)) hRad'
  have hLog' := hLog d.γ d.g₁ d.g₂ d.frame hd.1 r floor c₀ hFloor hd.2.2.2.2.1 x hx
  have hDiff' := hDiff d.γ d.g₂ (hγ.smoothMetric hK) (hg₂.smoothMetric hK) r hr hrp x hx β ε hβ hε
    (hd.2.2.2.2.2 x hx).1 (fun n hn hn₀ => (hLog' n hn hn₀).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg hβ'.le n)))
  refine ⟨fun i j n hn => (hDiff' i j n hn).trans ?_,?_⟩
  · have hDC : D ≤ C := by dsimp only [C]; linarith only [mul_nonneg (mul_nonneg hL (zero_le_one.trans hP)) hQ]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC hε) (pow_nonneg hβ'.le _)
  · intro i j n hn
    let q := tracePrincipalSmallDifference d i j
    have hq := contDiffOn_tracePrincipalSmallDifference (hγ.smoothMetric hK) (hg₂.smoothMetric hK)
      hr (fun y hy => (hrp y hy).ne') i j
    have hq' : LocalSmoothJetBudget (q ∘ p) 0 3 (D*ε) :=
      localSmoothJetBudget_scaled_chart hβ (hq.contDiffAt (hY.mem_nhds hx)) (hDiff' i j)
    have hp : ∀ᶠ w in 𝓝 (0:X dim),p w ∈ Y := by
      have hc : Continuous p := (continuous_const (y:=x)).add ((show Continuous (fun w : X dim => w) from continuous_id).const_smul β⁻¹)
      exact hc.continuousAt.eventually (show Y ∈ 𝓝 (p 0) by simpa [p] using hY.mem_nhds hx)
    let g (y : X dim) := (d.γ y)⁻¹ i j
    have hg : LocalSmoothJetBudget g x 3 G :=
      hInv d.γ hd.1.1 (hd.1.2.2.2.2.1 d.γ (by simp)) x (hSub hx) i j
    have hgc : LocalSmoothJetBudget (g ∘ p) 0 3 G :=
      localSmoothJetBudget_scaled_chart hβ hg.smooth (fun n hn =>
        (hg.bound n hn).trans (le_mul_of_one_le_right (zero_le_one.trans hG) (one_le_pow₀ hβ)))
    have hQu := hgc.add ((hRadius.enlarge (mul_le_of_le_one_right (zero_le_one.trans hP) hr₁)).real_mul
      (hq'.enlarge (mul_le_of_le_one_right hD hs)))
    have hEq : (fun w => principal d.γ d.g₂ (p w) i j) =ᶠ[𝓝 (0:X dim)]
        fun w => (g ∘ p) w+(r ∘ p) w*(q ∘ p) w := by
      filter_upwards [hp] with w hw
      have hR := (hrp _ hw).ne'
      dsimp only [Function.comp_apply,g,r,q,tracePrincipalSmallDifference,Matrix.sub_apply]
      field_simp [hR]
      <;> ring
    have hQu' : LocalSmoothJetBudget (fun w => principal d.γ d.g₂ (p w) i j) 0 3 Q :=
      hQu.congr_germ hEq
    have hprod := (hRadius.enlarge (mul_le_mul_of_nonneg_left hSmall (zero_le_one.trans hP))).real_mul hQu'
    have hConst : L*(P*(ε*(β⁻¹)^2))*Q ≤ C*ε*(β⁻¹)^2 := by
      calc
        _ = (L*P*Q)*ε*(β⁻¹)^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (show L*P*Q ≤ C from le_add_of_nonneg_left (add_nonneg zero_le_one hD)) hε) (sq_nonneg _)
    exact localSmoothJetBudget_scaled_chart_bound hβ (hprod.enlarge hConst) n hn

end CalderonN
