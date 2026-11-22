module

public import Proof.CalderonN.PhysicalTraceScalarJets

import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! Simultaneous base and angular jets after restriction to the
physical radius, with only the base axis rescaled by beta. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {E Z F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_affine_pos_le (L : E →L[ℝ] F) (a : F) (x : E) (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun y => a+L y) x‖ ≤ ‖L‖ := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
  have h : fderiv ℝ (fun y => a+L y) = fun _ => L :=
    funext fun y => (L.hasFDerivAt.const_add a).fderiv
  rw [← norm_iteratedFDeriv_fderiv,h]
  cases k with
  | zero => rw [norm_iteratedFDeriv_zero]
  | succ k => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,norm_nonneg]

theorem uniform_physicalChart_angular_jet_composition {Y : Set E} (hY : IsOpen Y)
    (N : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (r : E → ℝ) (hr : ContDiffOn ℝ ∞ r Y) (x : E) (hx : x ∈ Y)
      (hpos : ∀ y ∈ Y,0 < r y) (hr₁ : r x ≤ 1) (β : ℝ), 1 ≤ β →
      (∀ n ≤ N,1 ≤ n → ‖iteratedFDeriv ℝ n (fun y => Real.log (r y)) x‖ ≤ C*β^n) →
      ∀ (z : Z) (G : (E × ℝ) × Z → F) (A : ℝ),
        LocalSmoothJetBudget G ((x,r x),z) N A →
        LocalSmoothJetBudget (fun q : E × Z => G ((x+β⁻¹ • q.1,r (x+β⁻¹ • q.1)),z+q.2))
          0 N (D*A) := by
  obtain ⟨R,hR,hRadius⟩ := uniform_radius_scaled_chart_jets hY N C hC
  let C₀ := max 1 ((N.factorial:ℝ)*R)
  have hC₀ : 1 ≤ C₀ := le_max_left _ _
  let D := (N.factorial:ℝ)*C₀^N
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D,hD,?_⟩
  intro r hr x hx hpos hr₁ β hβ hLog z G A hG
  let L : E × Z →L[ℝ] E := β⁻¹ • ContinuousLinearMap.fst ℝ E Z
  let S : E × Z →L[ℝ] Z := ContinuousLinearMap.snd ℝ E Z
  let p (q : E × Z) := x+L q
  let t (q : E × Z) := z+S q
  let P (q : E × Z) := ((p q,r (p q)),t q)
  have hP₀ : P 0 = ((x,r x),z) := by simp [P,p,t]
  have hL : ‖L‖ ≤ 1 := by
    have hI : 0 ≤ β⁻¹ := inv_nonneg.mpr (zero_le_one.trans hβ)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hI]
    have hFst : ‖ContinuousLinearMap.fst ℝ E Z‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      rw [one_mul]
      exact norm_fst_le v
    calc
      β⁻¹ * ‖ContinuousLinearMap.fst ℝ E Z‖ ≤ β⁻¹ * 1 := mul_le_mul_of_nonneg_left hFst hI
      _ ≤ 1 := by rw [mul_one]; exact inv_le_one_of_one_le₀ hβ
  have hS : ‖S‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    rw [one_mul]
    exact norm_snd_le v
  have hp : ContDiffAt ℝ ∞ p (0:E × Z) := contDiffAt_const.add L.contDiff.contDiffAt
  have ht : ContDiffAt ℝ ∞ t (0:E × Z) := contDiffAt_const.add S.contDiff.contDiffAt
  obtain ⟨hR₁,_⟩ := hRadius r hr x hx hpos β hβ hLog
  let L₀ := ContinuousLinearMap.fst ℝ E Z
  have hL₀ : ‖L₀‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    rw [one_mul]
    exact norm_fst_le v
  have hR₂ : LocalSmoothJetBudget (fun q : E × Z => r (p q)/r x) 0 N ((N.factorial:ℝ)*R) := by
    have h := LocalSmoothJetBudget.linear_precomp L₀ (0:E × Z)
      (show LocalSmoothJetBudget (fun u => r (x+β⁻¹ • u)/r x) (L₀ 0) N R from by rw [map_zero]; exact hR₁)
    have hEq : (fun q : E × Z => r (p q)/r x) = (fun u => r (x+β⁻¹ • u)/r x) ∘ L₀ := by
      rfl
    rw [hEq]
    simpa only [max_eq_left hL₀,one_pow,mul_one] using h
  have hLeg : LocalSmoothJetBudget (fun q => r (p q)) 0 N ((N.factorial:ℝ)*R) := by
    have h := hR₂.const_smul (r x) (hpos x hx).le
    have hEq : (fun q : E × Z => r x • (r (p q)/r x)) = fun q => r (p q) := by
      funext q
      change r x*(r (p q)/r x) = _
      field_simp [(hpos x hx).ne']
    rw [hEq] at h
    exact h.enlarge (mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) hR) hr₁)
  have hG' : LocalSmoothJetBudget G (P 0) N A := hP₀.symm ▸ hG
  have hB := LocalSmoothJetBudget.comp_of_positive_inner
    ((hp.prodMk hLeg.smooth).prodMk ht) hG' hC₀
  have hEq : (N.factorial:ℝ)*A*C₀^N = D*A := by dsimp only [D]; ring
  rw [hEq] at hB
  apply hB
  intro n hn hnN
  have hB₁ : ‖iteratedFDeriv ℝ n p 0‖ ≤ C₀ :=
    (norm_iteratedFDeriv_affine_pos_le L x _ n hn).trans (hL.trans hC₀)
  have hB₂ : ‖iteratedFDeriv ℝ n (fun q => r (p q)) 0‖ ≤ C₀ :=
    (hLeg.bound n hnN).trans (le_max_right _ _)
  have hB₃ : ‖iteratedFDeriv ℝ n t 0‖ ≤ C₀ :=
    (norm_iteratedFDeriv_affine_pos_le S z _ n hn).trans (hS.trans hC₀)
  have hP := norm_iteratedFDeriv_prod_envelope_at _ _ _ _ hp hLeg.smooth hB₁ hB₂
  rw [max_self] at hP
  exact (norm_iteratedFDeriv_prod_envelope_at _ _ _ _
    (hp.prodMk hLeg.smooth) ht hP hB₃).trans (max_self C₀).le

end CalderonN
