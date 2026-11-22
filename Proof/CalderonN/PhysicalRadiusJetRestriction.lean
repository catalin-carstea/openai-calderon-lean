module

public import Proof.CalderonN.ScaledRadiusJetBudget
public import Proof.CalderonN.WeakEnergyConormalJets

import Mathlib.Tactic

/-! Restrict a relative-radius Taylor family to the physical radius, and
divide by its physical quadratic scale while preserving weighted jets. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_physicalRadius_restrict_quadratic_jets {Y : Set E} (hY : IsOpen Y)
    (N : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (r : E → ℝ) (hr : ContDiffOn ℝ ∞ r Y) (x : E) (hx : x ∈ Y)
      (hpos : ∀ y ∈ Y,0 < r y) (β : ℝ), 1 ≤ β →
      (∀ n ≤ N,1 ≤ n → ‖iteratedFDeriv ℝ n (fun y => Real.log (r y)) x‖ ≤ C*β^n) →
      ∀ (G : E × ℝ → F) (B : ℝ), LocalSmoothJetBudget G (x,0) N (B*(r x)^2) →
      ContDiffAt ℝ ∞ (fun y => ((r y)^2)⁻¹ • G (y,r y/r x-1)) x ∧
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (fun y => ((r y)^2)⁻¹ • G (y,r y/r x-1)) x‖ ≤ D*B*β^n := by
  let M : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  let S : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  obtain ⟨A,hA,hR⟩ := uniform_radius_scaled_chart_jets hY N C hC
  let P := max 1 (A+1)
  let D₁ := (2:ℝ)^N*‖M‖*A*A
  let D₂ := (2:ℝ)^N*‖S‖*D₁*N.factorial*P^N
  have hP : 1 ≤ P := le_max_left _ _
  have hD₁ : 0 ≤ D₁ := by dsimp only [D₁]; positivity
  have hD₂ : 0 ≤ D₂ := by dsimp only [D₂]; positivity
  refine ⟨D₂,hD₂,?_⟩
  intro r hr x hx hpos β hβ hLog G B hG
  let p (v : E) := x+β⁻¹ • v
  let q (v : E) := (p v,r (p v)/r x-1)
  let F₀ (y : E) := ((r y)^2)⁻¹ • G (y,r y/r x-1)
  have hβp := zero_lt_one.trans_le hβ
  have hp : p 0 = x := by simp [p]
  have hq : q 0 = (x,0) := by simp [q,hp,(hpos x hx).ne']
  obtain ⟨hR₁,hR₂⟩ := hR r hr x hx hpos β hβ hLog
  have hDiff : LocalSmoothJetBudget (fun v => r (p v)/r x-1) 0 N (A+1) := by
    simpa only [sub_eq_add_neg,Real.norm_eq_abs,abs_neg,abs_one] using
      hR₁.add (LocalSmoothJetBudget.const (P:=E) (x:=0) (N:=N) (-1:ℝ))
  have hP₀ : ContDiffAt ℝ ∞ p 0 := contDiffAt_const.add (contDiffAt_id.const_smul _)
  have hPS (n : ℕ) (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n p 0‖ ≤ 1 := by
    let L := β⁻¹ • ContinuousLinearMap.id ℝ E
    have hL : fderiv ℝ p = fun _ => L := by
      funext v
      exact ((L.hasFDerivAt (x:=v)).const_add x).fderiv
    obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
    rw [← norm_iteratedFDeriv_fderiv,hL]
    cases k with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      have hI : |β⁻¹| ≤ 1 := by
        rw [abs_of_pos (inv_pos.mpr hβp)]
        exact inv_le_one_of_one_le₀ hβ
      exact (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
        (ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=E))).trans (by rwa [Real.norm_eq_abs]))
    | succ k => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,zero_le_one]
  have hComp : LocalSmoothJetBudget (G ∘ q) 0 N (N.factorial*(B*(r x)^2)*P^N) := by
    apply LocalSmoothJetBudget.comp_of_positive_inner (hP₀.prodMk hDiff.smooth)
      (show LocalSmoothJetBudget G (q 0) N _ by rwa [hq]) hP
    intro n hn hnN
    exact norm_iteratedFDeriv_prod_envelope_at _ _ _ _ hP₀ hDiff.smooth
      (hPS n hn) (hDiff.bound n hnN)
  have hSq : LocalSmoothJetBudget (fun v => (r x/r (p v))^2) 0 N D₁ := by
    have h := hR₂.bilinear hR₂ M
    change LocalSmoothJetBudget (fun v => (r x/r (p v))*(r x/r (p v))) 0 N D₁ at h
    simpa only [pow_two] using h
  have hB := (hSq.bilinear hComp S).const_smul ((r x)^2)⁻¹ (inv_nonneg.mpr (sq_nonneg _))
  have hEq : (fun v => ((r x)^2)⁻¹ • S ((r x/r (p v))^2) ((G ∘ q) v)) = F₀ ∘ p := by
    funext v
    change ((r x)^2)⁻¹ • ((r x/r (p v))^2 • G (q v)) = ((r (p v))^2)⁻¹ • G (q v)
    rw [smul_smul,div_pow,div_eq_mul_inv,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 (hpos x hx).ne'),one_mul]
  have hBudget : LocalSmoothJetBudget (F₀ ∘ p) 0 N (D₂*B) := by
    have hConst : ((r x)^2)⁻¹*((2:ℝ)^N*‖S‖*D₁*((N.factorial:ℝ)*(B*(r x)^2)*P^N)) = D₂*B := by
      dsimp only [D₂]
      field_simp [(hpos x hx).ne']
      <;> ring
    rwa [hEq,hConst] at hB
  have hF : ContDiffAt ℝ ∞ F₀ x := by
    have hRx := hr.contDiffAt (hY.mem_nhds hx)
    have hQ : ContDiffAt ℝ ∞ (fun y => (y,r y/r x-1)) x :=
      contDiffAt_id.prodMk ((hRx.div contDiffAt_const (hpos x hx).ne').sub contDiffAt_const)
    have hGx : ContDiffAt ℝ ∞ G (x,r x/r x-1) := by
      simpa only [div_self (hpos x hx).ne',sub_self] using hG.smooth
    exact ((hRx.pow 2).inv (pow_ne_zero 2 (hpos x hx).ne')).smul (hGx.comp x hQ)
  refine ⟨hF,fun n hn => ?_⟩
  have hBd := hBudget.bound n hn
  change ‖iteratedFDeriv ℝ n (fun v => F₀ (x+β⁻¹ • v)) 0‖ ≤ D₂*B at hBd
  rw [norm_iteratedFDeriv_affine_scale F₀ x 0 _ (inv_ne_zero hβp.ne') n,smul_zero,add_zero,
    abs_of_pos (inv_pos.mpr hβp),inv_pow,← div_eq_inv_mul] at hBd
  exact (div_le_iff₀ (pow_pos hβp n)).mp hBd

end CalderonN
