module

public import Proof.CalderonN.FirstMetricConformalFactor
public import Proof.CalderonN.LogJetBounds

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The actual first metric is exp(-2t) times the reference metric. -/
def firstMetricConformalDepth (γ g₁ : (MetricField dim)) (x : (X dim)) : ℝ :=
  (1/2:ℝ)*(Real.log (γ x 0 0)-Real.log (g₁ x 0 0))

lemma Elliptic.diagonal_inverse_le {Ω : Set (X dim)} {K : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) (hK : 0 < K) {x : (X dim)} (hx : x ∈ Ω) (i : (I dim)) : (g x i i)⁻¹ ≤ K := by
  have hPos := hg.diagonal_entry_pos hK hx i
  have hl := ((hg.2 x hx).2 (axis i)).1
  have hEntry : metricPair g x (axis i) (axis i) = g x i i := by simp [metricPair,axis]
  rw [hEntry,norm_axis,one_pow,mul_one] at hl
  apply (inv_le_iff_one_le_mul₀ hPos).2
  have hh := mul_le_mul_of_nonneg_left hl hK.le
  simpa only [mul_inv_cancel₀ hK.ne'] using hh

theorem Background.firstMetricConformalDepth_smooth {Ω : Set (X dim)} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (firstMetricConformalDepth γ g₁) Ω :=
  contDiffOn_const.mul (((hB.1.1 0 0).log (fun x hx => (hB.1.diagonal_entry_pos hK hx 0).ne')).sub
    ((hB.2.1.1 0 0).log (fun x hx => (hB.2.1.diagonal_entry_pos hK hx 0).ne')))

theorem Background.firstMetricConformalFactor_eq_exp_depth {Ω : Set (X dim)} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : (X dim)} (hx : x ∈ Ω) :
    firstMetricConformalFactor γ g₁ x = Real.exp (-2*firstMetricConformalDepth γ g₁ x) := by
  have hArg : -2*firstMetricConformalDepth γ g₁ x = Real.log (g₁ x 0 0)-Real.log (γ x 0 0) := by
    dsimp [firstMetricConformalDepth];ring
  rw [hArg,Real.exp_sub,Real.exp_log (hB.2.1.diagonal_entry_pos hK hx 0),
    Real.exp_log (hB.1.diagonal_entry_pos hK hx 0)]
  rfl

theorem Background.firstMetric_eq_exp_depth {Ω : Set (X dim)} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : (X dim)} (hx : x ∈ Ω) :
    g₁ x = Real.exp (-2*firstMetricConformalDepth γ g₁ x) • γ x := by
  rw [← hB.firstMetricConformalFactor_eq_exp_depth hK hx]
  exact hB.firstMetric_eq_conformalFactor hK hx

/-- Common first and second conformal-depth jets come directly from the frozen
    metric budgets and ellipticity. No arbitrary smooth family bound is used. -/
theorem Background.firstMetricConformalDepth_jet_bounds {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {γ g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) (hm : 2 ≤ m) {x : (X dim)} (hx : x ∈ Ω) :
    ‖fderiv ℝ (firstMetricConformalDepth γ g₁) x‖ ≤ K*|M ⟨1,by omega⟩| ∧
    ‖fderiv ℝ (fderiv ℝ (firstMetricConformalDepth γ g₁)) x‖ ≤
      K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2 := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let f := fun y : (X dim) => Real.log (γ y 0 0)
  let h := fun y : (X dim) => Real.log (g₁ y 0 0)
  have hLog (g : (MetricField dim)) (hg : g ∈ ({γ,g₁}:Set (MetricField dim))) :
      ‖fderiv ℝ (fun y => Real.log (g y 0 0)) x‖ ≤ K*M1 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => Real.log (g y 0 0))) x‖ ≤ K*M2+K^2*M1^2 := by
    have hEll : Elliptic Ω K g := by
      simp only [mem_insert_iff,mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hB.1
      · exact hB.2.1
    have hPos := hEll.diagonal_entry_pos hK hx 0
    have hInv := hEll.diagonal_inverse_le hK hx 0
    have hInvSq : ((g x 0 0)^2)⁻¹ ≤ K^2 := by rw [← inv_pow];gcongr
    have hD : ‖fderiv ℝ (fun y => g y 0 0) x‖ ≤ M1 := by
      have hh := hB.2.2.2.2.1 g hg ⟨1,by omega⟩ 0 0 x hx
      rw [norm_iteratedFDeriv_one] at hh
      exact hh.trans (le_abs_self _)
    have hDD : ‖fderiv ℝ (fderiv ℝ (fun y => g y 0 0)) x‖ ≤ M2 := by
      have hh := hB.2.2.2.2.1 g hg ⟨2,by omega⟩ 0 0 x hx
      rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at hh
      exact hh.trans (le_abs_self _)
    have hSmooth := (hEll.1 0 0).contDiffAt (hΩ.mem_nhds hx)
    refine ⟨(norm_fderiv_log_le _ _ (hSmooth.differentiableAt (by simp)) hPos M1 hD).trans
      (mul_le_mul_of_nonneg_right hInv (abs_nonneg _)),?_⟩
    exact (norm_second_fderiv_log_le _ _ hSmooth hPos M1 M2 (abs_nonneg _) (abs_nonneg _) hD hDD).trans
      (add_le_add (mul_le_mul_of_nonneg_right hInv (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hInvSq (sq_nonneg _)))
  have hf : ContDiffOn ℝ ∞ f Ω := (hB.1.1 0 0).log (fun y hy => (hB.1.diagonal_entry_pos hK hy 0).ne')
  have hh : ContDiffOn ℝ ∞ h Ω := (hB.2.1.1 0 0).log (fun y hy => (hB.2.1.diagonal_entry_pos hK hy 0).ne')
  have hFD := (((hf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.sub
    ((hh.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).const_smul (1/2:ℝ)
  have hDId : fderiv ℝ (firstMetricConformalDepth γ g₁) x =
      (1/2:ℝ) • (fderiv ℝ f x-fderiv ℝ h x) := hFD.fderiv
  have hEq : fderiv ℝ (firstMetricConformalDepth γ g₁) =ᶠ[𝓝 x]
      (fun y => (1/2:ℝ) • (fderiv ℝ f y-fderiv ℝ h y)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact ((((hf.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt.sub
      ((hh.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt).const_smul (1/2:ℝ)).fderiv
  have hDDId := (((((hf.fderiv_of_isOpen (m:=∞) hΩ (by simp)).contDiffAt (hΩ.mem_nhds hx)).differentiableAt
    (by simp)).hasFDerivAt.sub
      (((hh.fderiv_of_isOpen (m:=∞) hΩ (by simp)).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).const_smul (1/2:ℝ)).fderiv
  have hHalfFunEq : (1/2:ℝ) • (fderiv ℝ f-fderiv ℝ h) =
      (fun y => (1/2:ℝ) • (fderiv ℝ f y-fderiv ℝ h y)) := by
    funext y
    rfl
  rw [hHalfFunEq] at hDDId
  have hγ := hLog γ (by simp)
  have h1 := hLog g₁ (by simp)
  constructor
  · rw [hDId,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    exact (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hγ.1 h1.1))
      (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)
  · rw [hEq.fderiv_eq,hDDId,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    exact (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hγ.2 h1.2))
      (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)

end CalderonN
