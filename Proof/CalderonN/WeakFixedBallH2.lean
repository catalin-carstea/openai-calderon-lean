module

public import Proof.CalderonN.UniformEllipticExtension
public import Proof.CalderonN.WeakSolutionLocalization

import Mathlib.Tactic

public section

/- Interior localization of the fixed-ball weak source. The generic
   difference-quotient proof comes from the checked 3D analysis imports. -/
noncomputable section
open Set MeasureTheory Metric Filter TopologicalSpace
open scoped ContDiff ENNReal Distributions Gradient Matrix.Norms.Elementwise

namespace CalderonN
open TauCeti TauCeti.PDE OAI.AnisotropicCalderon.Regularity
variable {n : ℕ}

set_option maxHeartbeats 1800000 in
theorem weakFixedBall_test
    {a : X n → Mat n} {F : Lp ℝ 2 ((volume : Measure (X n)).restrict (fixedBallOpens n))}
    {u : FixedBallH1Zero n} (h : IsWeakSolutionDirichlet a 0 0 F u)
    (ψ : 𝓓(fixedBallOpens n, ℝ)) :
    (∫ x in (fixedBallOpens n : Set (X n)),
      matrixBilinearForm (a x) (gradient (ψ : X n → ℝ) x) (W1p.gradient (u : FixedBallH1 n) x)) =
        ∫ x in (fixedBallOpens n : Set (X n)), F x * ψ x := by
  let v : FixedBallH1Zero n := ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule ψ⟩
  have hv := (isWeakSolutionDirichlet_iff F u).mp h v
  rw [energyFormH1_def] at hv
  simp at hv
  refine (integral_congr_ae ?_).trans (hv.trans (integral_congr_ae ?_))
  · filter_upwards [gradientTestFunctionLp_apply_ae (mu := (volume : Measure (X n))) 2 ψ] with x hx
    rw [matrixBilinearForm_apply, show (v : FixedBallH1 n) =
      W1p.ofTestFunctionₗ volume (fixedBallOpens n) 2 ψ from rfl, W1p.gradient_ofTestFunctionₗ, hx]
  · filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure (X n))) 2 ψ] with x hx
    change F x * W1p.value (W1p.ofTestFunctionₗ volume (fixedBallOpens n) 2 ψ) x = _
    rw [W1p.value_ofTestFunctionₗ, hx]

set_option maxHeartbeats 2300000 in
theorem exists_localized_fixedBall_H2
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) {lo hi : ℝ}
    (he : UniformlyEllipticOn (fixedBallOpens n : Set (X n)) a lo hi)
    {F : Lp ℝ 2 ((volume : Measure (X n)).restrict (fixedBallOpens n))}
    {u : FixedBallH1Zero n} (hu : IsWeakSolutionDirichlet a 0 0 F u)
    {ψ : X n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ ball (0 : X n) (7/8)) :
    ∃ U : Wkp (volume : Measure (X n)) (fixedBallOpens n) 2 2,
      W1p.value (Wkp.lowerOrder 1 U) =ᵐ[(volume : Measure (X n)).restrict (fixedBallOpens n)]
        fun x => ψ x * W1p.value (u : FixedBallH1 n) x := by
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall (0 : X n) (7/8)).of_isClosed_subset (isClosed_tsupport ψ)
      (hψs.trans ball_subset_closedBall)
  have hts : tsupport ψ ⊆ (fixedBallOpens n : Set (X n)) :=
    hψs.trans (ball_subset_ball (by norm_num))
  have he' := uniformlyEllipticOn_ellExt he (fun _ _ => rfl)
  obtain ⟨K,hK⟩ := exists_lipschitz_ellExt ha lo
  obtain ⟨v,g,hvg,hval,_,_⟩ := exists_wholeSpace_solution (mu := (volume : Measure (X n))) ha
    he'.upper_nonneg (contDiff_ellExt ha lo).continuous
    (fun x η ξ => he'.upper_bound (mem_univ x) η ξ)
    (show Bornology.IsBounded (fixedBallOpens n : Set (X n)) from isBounded_ball)
    (weakFixedBall_test hu) hψ hψc hts (fun x hx => ellExt_eq (hψs hx))
  obtain ⟨U,hU⟩ := exists_lowerOrder_eq_var he' hK hvg
  have hle : fixedBallOpens n ≤ (⊤ : Opens (X n)) := le_top
  refine ⟨Wkp.restrictL hle 2 U, ?_⟩
  rw [Wkp.lowerOrder_restrictL, ← Wkp.value_one]
  filter_upwards [Wkp.value_restrictL_ae hle 1 (Wkp.lowerOrder 1 U),
    ae_restrict_of_ae hval, ae_restrict_mem (fixedBallOpens n).isOpen.measurableSet] with x h1 h2 h3
  rw [h1, Wkp.value_one, hU, h2, indicator_of_mem h3]

end CalderonN
