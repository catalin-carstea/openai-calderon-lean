module

public import Proof.CalderonN.UniformLogRadiusChartJets

import Proof.CalderonN.LocalMixedParameterJetCalculus
import Mathlib.Tactic

/-! Convert weighted chart derivatives into uniform jets in coordinates
scaled by the logarithmic-radius gradient. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_affine_scale (f : E → F) (x p : E) (c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    iteratedFDeriv ℝ n (fun v => f (x+c • v)) p =
      c^n • iteratedFDeriv ℝ n f (x+c • p) := by
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  let g (v : E) := f (x+v)
  have hLp (v : E) : L v = c • v := rfl
  have h := L.iteratedFDerivWithin_comp_right g
    (s:=(univ : Set E)) uniqueDiffOn_univ (x:=p) (mem_univ _) n
  simp only [preimage_univ,iteratedFDerivWithin_univ] at h
  have hg : iteratedFDeriv ℝ n g (L p) = iteratedFDeriv ℝ n f (x+c • p) := by
    rw [← hLp p]
    exact iteratedFDeriv_comp_add_left n x (L p)
  rw [hg] at h
  have hFun : g ∘ L = fun v => f (x+c • v) := funext fun v => by
    change f (x+L v) = _
    rw [hLp]
  rw [hFun] at h
  rw [h]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe,hLp,ContinuousMultilinearMap.map_smul_univ,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,ContinuousMultilinearMap.smul_apply]

theorem norm_iteratedFDeriv_affine_scale (f : E → F) (x p : E) (c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v => f (x+c • v)) p‖ =
      |c|^n*‖iteratedFDeriv ℝ n f (x+c • p)‖ := by
  rw [iteratedFDeriv_affine_scale f x p c hc n,norm_smul,Real.norm_eq_abs,abs_pow]

theorem norm_iteratedFDeriv_comp_exp_at_zero_le (N : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : E → ℝ), f 0 = 0 → LocalSmoothJetBudget f 0 N C →
      LocalSmoothJetBudget (Real.exp ∘ f) 0 N D := by
  let M := 1+∑ n : Fin (N+1),‖iteratedFDeriv ℝ n.val Real.exp 0‖
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨(N.factorial:ℝ)*M*C^N,by positivity,?_⟩
  intro f hf hF
  apply hF.comp _ hC
  refine ⟨Real.contDiff_exp.contDiffAt,?_⟩
  intro n hn
  rw [hf]
  exact (Finset.single_le_sum (f:=fun n : Fin (N+1) => ‖iteratedFDeriv ℝ n.val Real.exp 0‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ ⟨n,by omega⟩)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem uniform_radius_scaled_chart_jets {Y : Set E} (hY : IsOpen Y)
    (N : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (r : E → ℝ) (hr : ContDiffOn ℝ ∞ r Y) (x : E) (hx : x ∈ Y)
      (hpos : ∀ y ∈ Y,0 < r y) (β : ℝ), 1 ≤ β →
      (∀ n ≤ N,1 ≤ n → ‖iteratedFDeriv ℝ n (fun y => Real.log (r y)) x‖ ≤ C*β^n) →
      LocalSmoothJetBudget (fun p => r (x+β⁻¹ • p)/r x) 0 N D ∧
      LocalSmoothJetBudget (fun p => r x/r (x+β⁻¹ • p)) 0 N D := by
  obtain ⟨D,hD,hExp⟩ := norm_iteratedFDeriv_comp_exp_at_zero_le (E:=E) N C hC
  refine ⟨D,hD,?_⟩
  intro r hr x hx hpos β hβ hLog
  let f (y : E) := Real.log (r y)
  let p (v : E) := x+β⁻¹ • v
  have hfx := hr.log (fun y hy => (hpos y hy).ne')
  have hp : p 0 = x := by simp [p]
  have hSmooth : ContDiff ℝ ∞ p := contDiff_const.add (contDiff_id.const_smul _)
  have hNear : ∀ᶠ v in 𝓝 (0:E), p v ∈ Y := by
    change ∀ᶠ v in 𝓝 (0:E),Y (p v)
    exact hSmooth.continuous.continuousAt.eventually
      (show Y ∈ 𝓝 (p 0) by rw [hp]; exact hY.mem_nhds hx)
  let g (v : E) := f (p v)-f x
  have hg₀ : g 0 = 0 := by simp [g,hp]
  have hg : ContDiffAt ℝ ∞ g 0 := by
    have hAt : ContDiffAt ℝ ∞ f (p 0) := by
      rw [hp]
      exact hfx.contDiffAt (hY.mem_nhds hx)
    exact (hAt.comp 0 hSmooth.contDiffAt).sub contDiffAt_const
  have hgNorm (n : ℕ) (hn : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n g 0‖ = ‖iteratedFDeriv ℝ n (f ∘ p) 0‖ := by
    have hE : fderiv ℝ g =ᶠ[𝓝 (0:E)] fderiv ℝ (f ∘ p) := by
      filter_upwards [hNear] with v hv
      have hFP := ((hfx.contDiffAt (hY.mem_nhds hv)).comp v hSmooth.contDiffAt).differentiableAt (by simp)
      change fderiv ℝ ((f ∘ p)-(fun _ : E => f x)) v = _
      rw [fderiv_sub hFP (differentiableAt_const _),fderiv_fun_const,Pi.zero_apply,sub_zero]
    obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
    rw [← norm_iteratedFDeriv_fderiv,← norm_iteratedFDeriv_fderiv,
      (hE.iteratedFDeriv ℝ k).eq_of_nhds]
  have hG : LocalSmoothJetBudget g 0 N C := by
    refine ⟨hg,fun n hn => ?_⟩
    by_cases hzero : n=0
    · subst n
      rw [norm_iteratedFDeriv_zero,hg₀,norm_zero]
      exact zero_le_one.trans hC
    · rw [hgNorm n (by omega)]
      change ‖iteratedFDeriv ℝ n (fun v => f (x+β⁻¹ • v)) 0‖ ≤ C
      have hβp := zero_lt_one.trans_le hβ
      rw [norm_iteratedFDeriv_affine_scale f x 0 _ (inv_ne_zero hβp.ne') n,smul_zero,add_zero,
        abs_of_pos (inv_pos.mpr hβp)]
      have hBound := mul_le_mul_of_nonneg_left (hLog n hn (by omega))
        (pow_nonneg (inv_nonneg.mpr hβp.le) n)
      exact hBound.trans_eq (by rw [inv_pow]; field_simp)
  have hNeg : LocalSmoothJetBudget (-g) 0 N C := by
    refine ⟨hg.neg,fun n hn => ?_⟩
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact hG.bound n hn
  have hE := hExp g hg₀ hG
  have hI := hExp (-g) (by simp [hg₀]) hNeg
  have hEeq : Real.exp ∘ g =ᶠ[𝓝 (0:E)] fun v => r (p v)/r x := by
    filter_upwards [hNear] with v hv
    change Real.exp (Real.log (r (p v))-Real.log (r x)) = _
    rw [Real.exp_sub,Real.exp_log (hpos (p v) hv),Real.exp_log (hpos x hx)]
  have hIeq : Real.exp ∘ (-g) =ᶠ[𝓝 (0:E)] fun v => r x/r (p v) := by
    filter_upwards [hNear] with v hv
    change Real.exp (-(Real.log (r (p v))-Real.log (r x))) = _
    rw [neg_sub,Real.exp_sub,Real.exp_log (hpos (p v) hv),Real.exp_log (hpos x hx)]
  exact ⟨⟨hE.smooth.congr_of_eventuallyEq hEeq.symm,fun n hn =>
    (hEeq.iteratedFDeriv ℝ n).eq_of_nhds.symm ▸ hE.bound n hn⟩,
    ⟨hI.smooth.congr_of_eventuallyEq hIeq.symm,fun n hn =>
      (hIeq.iteratedFDeriv ℝ n).eq_of_nhds.symm ▸ hI.bound n hn⟩⟩

end CalderonN
