module

public import Proof.CalderonN.ScaledRadiusJetBudget
public import Proof.CalderonN.SmallPrincipalOrdinaryJets
public import Proof.CalderonN.MovingTraceCoordinateSquare

import Proof.CalderonN.WeakEnergyConormalJets
import Proof.CalderonN.PrincipalMetric
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

/-! Radius weights in the actual scalar coefficients of the principal
part. The small tensor is differentiated only through the eight
ordinary chart jets in the protected smallness condition. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

section Rescaling
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem localSmoothJetBudget_scaled_chart {f : E → F} {x : E} {N : ℕ} {C β : ℝ}
    (hβ : 1 ≤ β) (hf : ContDiffAt ℝ ∞ f x)
    (h : ∀ n ≤ N, ‖iteratedFDeriv ℝ n f x‖ ≤ C*β^n) :
    LocalSmoothJetBudget (fun p => f (x+β⁻¹ • p)) 0 N C := by
  have hp : ContDiff ℝ ∞ (fun p : E => x+β⁻¹ • p) :=
    contDiff_const.add (contDiff_id.const_smul _)
  have hβp := zero_lt_one.trans_le hβ
  have hF : ContDiffAt ℝ ∞ f ((fun p : E => x+β⁻¹ • p) 0) := by simpa using hf
  refine ⟨hF.comp 0 hp.contDiffAt,fun n hn => ?_⟩
  rw [norm_iteratedFDeriv_affine_scale f x 0 _ (inv_ne_zero hβp.ne') n,smul_zero,add_zero,
    abs_of_pos (inv_pos.mpr hβp),inv_pow,← div_eq_inv_mul]
  exact (div_le_iff₀ (pow_pos hβp n)).mpr (h n hn)

theorem localSmoothJetBudget_scaled_chart_bound {f : E → F} {x : E} {N : ℕ} {C β : ℝ}
    (hβ : 1 ≤ β) (h : LocalSmoothJetBudget (fun p => f (x+β⁻¹ • p)) 0 N C) :
    ∀ n ≤ N, ‖iteratedFDeriv ℝ n f x‖ ≤ C*β^n := by
  intro n hn
  have hβp := zero_lt_one.trans_le hβ
  have hh := h.bound n hn
  rw [norm_iteratedFDeriv_affine_scale f x 0 _ (inv_ne_zero hβp.ne') n,smul_zero,add_zero,
    abs_of_pos (inv_pos.mpr hβp),inv_pow,← div_eq_inv_mul] at hh
  exact (div_le_iff₀ (pow_pos hβp n)).mp hh

end Rescaling

variable {dim : ℕ} [NeZero dim]

omit [NeZero dim] in
theorem traceCoordinateDrift_eq_second_connection (γ g₂ : MetricField dim) (k : I dim)
    (x : X dim) : traceCoordinateDrift γ g₂ k x =
      -(∑ i : I dim,∑ j : I dim,principal γ g₂ x i j*christoffel g₂ x k i j) := by
  unfold traceCoordinateDrift drift
  simp only [mul_sub,Finset.sum_sub_distrib]
  abel

theorem uniform_physical_trace_small_scalar_jets {Y : Set (X dim)} (hY : IsOpen Y)
    (N : ℕ) (hN : N ≤ 8) (C : ℝ) (hC : 1 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (γ g₂ : MetricField dim) (hγ : SmoothMetric Y γ) (hg : SmoothMetric Y g₂)
      (r : X dim → ℝ) (hr : ContDiffOn ℝ ∞ r Y) (hpos : ∀ y ∈ Y,0 < r y)
      (x : X dim) (hx : x ∈ Y) (β ε : ℝ), 1 ≤ β → 0 ≤ ε → smallJet γ g₂ x ≤ ε*r x →
      (∀ n ≤ N,1 ≤ n → ‖iteratedFDeriv ℝ n (fun y => Real.log (r y)) x‖ ≤ C*β^n) →
      ∀ i j : I dim, ∀ n ≤ N,
        ‖iteratedFDeriv ℝ n (fun y => (principal γ g₂ y-(γ y)⁻¹) i j/r y) x‖ ≤ D*ε*β^n := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  let S := (dim:ℝ)^N
  obtain ⟨R,hR,hJ⟩ := uniform_radius_scaled_chart_jets hY N C hC
  let D := (2:ℝ)^N*‖L‖*S*R
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D,hD,?_⟩
  intro γ g₂ hγ hg r hr hpos x hx β ε hβ hε hSmall hj i j n hn
  let p (v : X dim) := x+β⁻¹ • v
  let h (y : X dim) := (principal γ g₂ y-(γ y)⁻¹) i j
  have hdim : (1:ℝ) ≤ dim := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne dim)
  have hOrd (k : ℕ) (hk : k ≤ N) : ‖iteratedFDeriv ℝ k h x‖ ≤ S*(ε*r x)*β^k := by
    refine (norm_iteratedFDeriv_principalDifference_le_smallJet hY hγ hg hx k (hk.trans hN) i j).trans ?_
    exact (mul_le_mul (pow_le_pow_right₀ hdim hk) hSmall
      (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) hS).trans
        (le_mul_of_one_le_right (mul_nonneg hS (mul_nonneg hε (hpos x hx).le)) (one_le_pow₀ hβ))
  have hSmooth : ContDiffAt ℝ ∞ h x := by
    exact ((contDiffOn_principal_entry hγ hg i j).sub (contDiffOn_metric_inv_entry hγ i j)).contDiffAt
      (hY.mem_nhds hx)
  have hh := localSmoothJetBudget_scaled_chart hβ hSmooth hOrd
  obtain ⟨_,hI⟩ := hJ r hr x hx hpos β hβ hj
  have hP := (hh.bilinear hI L).const_smul (r x)⁻¹ (inv_nonneg.mpr (hpos x hx).le)
  have hProd : (fun v : X dim => (r x)⁻¹ • L (h (p v)) (r x/r (p v))) =
      (fun v => h (p v)/r (p v)) := by
    funext v
    change (r x)⁻¹*(h (p v)*(r x/r (p v))) = _
    rw [div_eq_mul_inv,div_eq_mul_inv]
    field_simp [(hpos x hx).ne']
  have hConst : (r x)⁻¹*((2:ℝ)^N*‖L‖*(S*(ε*r x))*R) = D*ε := by
    dsimp only [D]
    field_simp [(hpos x hx).ne']
    <;> ring
  rw [hProd,hConst] at hP
  exact localSmoothJetBudget_scaled_chart_bound hβ hP n hn

end CalderonN
