module

public import Proof.CalderonN.ActualNormalizedParallelCenterJets
public import Proof.CalderonN.ActualNormalCoefficientRemainder

import Mathlib.Tactic

/-! The quadratic center-velocity remainder through the full signed
radius interval, with the same actual normal map throughout. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def actualParallelCenterRadialRemainder (d : Data dim)
    (a : NormalCoefficientRadialParameter dim) : X dim →L[ℝ] X dim :=
  normalRadialTaylorRemainder (actualNormalizedParallelCenterField d.γ d.expMap) a

theorem uniform_actual_parallelCenter_radialRemainder
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ y ∈ Y, ∀ s : ℝ, |s| ≤ 2*d.radius y → ∀ w ∈ disk d.γ y L,
        LocalSmoothJetBudget (actualParallelCenterRadialRemainder d) (y,(s,w)) N C ∧
        normalizedParallelCenterJacobian d.γ d.expMap y (s • w) =
          ContinuousLinearMap.id ℝ (X dim)+s^2 • actualParallelCenterRadialRemainder d (y,(s,w)) := by
  obtain ⟨η,hη,hGeometry⟩ := uniform_actual_normal_radial_segment_enlarged (Y:=Y)
    hΩ (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ L hL
  obtain ⟨CA,hCA,hA⟩ := uniform_actual_normalizedParallelCenter_jets hY hΩ K hK
    (N+2) (by omega) M
  obtain ⟨C,hC,hTaylor⟩ := exists_uniform_normalRadialTaylorRemainder_jets
    (E:=X dim →L[ℝ] X dim) hYc (K*L) N CA hCA
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε he hs d hd y hy s hsR w hw
  obtain ⟨hs₁,hw₁,hGeom⟩ := hGeometry floor hf ε he hs d hd y hy s hsR w hw
  have hK' := zero_lt_one.trans_le hK
  obtain ⟨U,hU,hTube,hF⟩ := smoothNear_actualNormalizedParallelCenter hΩ hd.1.1 hK' hd.2.1
  let F := actualNormalizedParallelCenterField d.γ d.expMap
  have hr : ContinuousAt (fun x => max ρ (d.radius x)) y :=
    continuousAt_const.max ((hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hy)).continuousAt)
  have hContains (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (y,(t*s) • w) ∈ U := by
    have hJ : ‖normalVerticalJacobian d.expMap y ((t*s) • w)-ContinuousLinearMap.id ℝ (X dim)‖ < 1 :=
      ((hGeom t ht).2.2.2).trans_lt (by norm_num)
    exact hTube ⟨hy,(hGeom t ht).1,hJ⟩
  have hZ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : LocalSmoothJetBudget F (y,(t*s) • w) (N+2) CA :=
    hA d.γ d.g₁ d.g₂ d.frame hd.1 d.expMap _ hd.2.1 y hy hr ((t*s) • w)
      (hGeom t ht).2.1 (hGeom t ht).2.2.1 (hGeom t ht).2.2.2
  have h₁ := hTaylor F U hU hF y (subset_closure hy) s hs₁ w hw₁ hContains hZ
  obtain ⟨hZero,hFirst⟩ := hd.1.normalizedParallelCenter_zero_jets hY hΩ hK' (by omega) hd.2.1 hy hr
  have ht₀ : (0:ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have h0U : (y,(0:X dim)) ∈ U := by simpa only [zero_mul,zero_smul] using hContains 0 ht₀
  have hDiff := (hF.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
  have heq : fderiv ℝ (normalizedParallelCenterJacobian d.γ d.expMap y) (0:X dim) =
      (fderiv ℝ F (y,0)).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim)) :=
    (hDiff.hasFDerivAt.comp (0:X dim) (hasFDerivAt_prodMk_right y (0:X dim))).fderiv
  have hVert : fderiv ℝ F (y,0) (0,w) = 0 := by
    simpa only [heq,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,ContinuousLinearMap.zero_apply] using
      congrArg (fun D : X dim →L[ℝ] (X dim →L[ℝ] X dim) => D w) hFirst
  refine ⟨h₁.1,?_⟩
  have h₂ := h₁.2
  rw [show F (y,(0:X dim)) = ContinuousLinearMap.id ℝ (X dim) from hZero,hVert,smul_zero,add_zero] at h₂
  exact h₂

end CalderonN
