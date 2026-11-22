module

public import Proof.CalderonN.WeakFixedBallH2
public import Proof.CalderonN.SobolevInteriorRepresentative
import Proof.CalderonN.SobolevLocalizedForcing
import Proof.CalderonN.WholeSpaceRegularity
import Mathlib.Tactic

public section

/-! Interior smoothness of the fixed-ball weak source. The induction uses
cutoffs with support inside the same open ball. At each finite order the
next cutoff is identically one near the preceding support. -/
noncomputable section
open Set MeasureTheory TopologicalSpace Metric Filter
open scoped ENNReal ContDiff Distributions Gradient Matrix.Norms.Elementwise

namespace CalderonN
open TauCeti TauCeti.PDE OAI.AnisotropicCalderon.Regularity
variable {n : ℕ}

private abbrev I₀ (n : ℕ) : Set (X n) := ball (0 : X n) (7/8)
local notation "Ω₀" => (⊤ : Opens (X n))
local notation "μ₀" => (volume : Measure (X n))

private theorem hasCompactSupport_of_support_in_innerBall {ψ : X n → ℝ}
    (hψ : tsupport ψ ⊆ I₀ n) : HasCompactSupport ψ :=
  (isCompact_closedBall (0 : X n) (7/8)).of_isClosed_subset (isClosed_tsupport ψ)
    (hψ.trans ball_subset_closedBall)

set_option maxHeartbeats 5000000 in
private theorem exists_localized_fixedBall_order [NeZero n]
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) {lo hi : ℝ}
    (he : UniformlyEllipticOn (fixedBallOpens n : Set (X n)) a lo hi)
    {f : X n → ℝ} (hf : ContDiff ℝ ∞ f)
    {F : Lp ℝ 2 ((μ₀).restrict (fixedBallOpens n))}
    (hF : ⇑F =ᵐ[(μ₀).restrict (fixedBallOpens n)] f)
    {u : FixedBallH1Zero n} (hu : IsWeakSolutionDirichlet a 0 0 F u)
    (m : ℕ) {ψ : X n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ I₀ n) :
    ∃ W : Wkp μ₀ Ω₀ 2 (m + 1),
      (∀ᵐ x ∂μ₀, W1p.value (Wkp.firstOrder m W) x =
        (fixedBallOpens n : Set (X n)).indicator
          (fun y => ψ y * W1p.value (u : FixedBallH1 n) y) x) ∧
      (∀ᵐ x ∂μ₀, W1p.gradient (Wkp.firstOrder m W) x =
        (fixedBallOpens n : Set (X n)).indicator (fun y =>
          ψ y • W1p.gradient (u : FixedBallH1 n) y + W1p.value (u : FixedBallH1 n) y • gradient ψ y) x) := by
  have he' := uniformlyEllipticOn_ellExt he (fun _ _ => rfl)
  obtain ⟨K,hK⟩ := exists_lipschitz_ellExt ha lo
  have hl (ζ : X n → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hζs : tsupport ζ ⊆ I₀ n) :=
    exists_wholeSpace_solution (mu := μ₀) ha
      he'.upper_nonneg (contDiff_ellExt ha lo).continuous
      (fun x η ξ => he'.upper_bound (mem_univ x) η ξ)
      (show Bornology.IsBounded (fixedBallOpens n : Set (X n)) from isBounded_ball)
      (weakFixedBall_test hu) hζ (hasCompactSupport_of_support_in_innerBall hζs)
      (hζs.trans (ball_subset_ball (by norm_num))) (fun x hx => ellExt_eq (hζs hx))
  induction m generalizing ψ with
  | zero =>
    obtain ⟨w,g,_,hwv,hwg,_⟩ := hl ψ hψ hψs
    exact ⟨(w : W1p μ₀ Ω₀ 2), hwv, hwg⟩
  | succ m ih =>
    obtain ⟨w,g,hw,hwv,hwg,hg⟩ := hl ψ hψ hψs
    have hψc : HasCompactSupport ψ := hasCompactSupport_of_support_in_innerBall hψs
    obtain ⟨η,hη,_,hηs,hηOne⟩ := Elliptic.exists_plateau_cutoff
      (isOpen_ball : IsOpen (I₀ n)) hψc hψs
    obtain ⟨W,hWv,hWg⟩ := ih hη hηs
    obtain ⟨G,hG⟩ := exists_sobolev_localized_forcing ha hf F hF (u : FixedBallH1 n)
      hψ hψc (hψs.trans (ball_subset_ball (by norm_num))) hηOne m W hWv hWg
    have hEq : Wkp.value m G = g := by
      apply Lp.ext
      have htop : (μ₀).restrict Ω₀ = μ₀ := by rw [Opens.coe_top, Measure.restrict_univ]
      have hg' : ⇑g =ᵐ[μ₀] (fixedBallOpens n : Set (X n)).indicator
          (locForcing a ψ F (u : FixedBallH1 n)) := hg
      exact (hG.trans hg'.symm).filter_mono (ae_mono htop.le)
    have hw' : IsWeakSolutionDirichlet (ellExt a lo) 0 0 (Wkp.value m G) w := by rwa [hEq]
    obtain ⟨U,hU⟩ := exists_wholeSpace_higher_solution (contDiff_ellExt ha lo)
      (hasCompactSupport_ellExt_sub_const a lo) he' hK m G w hw'
    refine ⟨U, ?_, ?_⟩ <;> rw [hU]
    · exact hwv
    · exact hwg

set_option maxHeartbeats 2600000 in
/-- The same weak solution has a smooth representative in the interior ball. -/
theorem exists_fixedBall_smooth_interior_rep [NeZero n]
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) {lo hi : ℝ}
    (he : UniformlyEllipticOn (fixedBallOpens n : Set (X n)) a lo hi)
    {f : X n → ℝ} (hf : ContDiff ℝ ∞ f)
    {F : Lp ℝ 2 (volume.restrict (fixedBallOpens n))}
    (hF : ⇑F =ᵐ[volume.restrict (fixedBallOpens n)] f)
    {u : FixedBallH1Zero n} (hu : IsWeakSolutionDirichlet a 0 0 F u) :
    ∃ b : X n → ℝ, ContDiffOn ℝ ∞ b (ball (0 : X n) (7/8)) ∧
      b =ᵐ[volume.restrict (ball (0 : X n) (7/8))] ⇑(W1p.value (u : FixedBallH1 n)) := by
  apply exists_contDiffOn_ae_eq isOpen_ball
  intro x hx
  obtain ⟨R,hR,hRsub⟩ := Metric.isOpen_iff.mp (isOpen_ball : IsOpen (I₀ n)) x hx
  let ρ := R/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hcl : closedBall x ρ ⊆ I₀ n := (closedBall_subset_ball (by dsimp [ρ]; linarith)).trans hRsub
  have hsub : ball x ρ ⊆ I₀ n := ball_subset_closedBall.trans hcl
  refine ⟨ρ,hρ,hsub, fun k => ?_⟩
  obtain ⟨ψ,hψ,_,hψs,hψOne⟩ := Elliptic.exists_plateau_cutoff
    (isOpen_ball : IsOpen (I₀ n)) (isCompact_closedBall x ρ) hcl
  obtain ⟨W,hW,_⟩ := exists_localized_fixedBall_order ha he hf hF hu k hψ hψs
  let V : Opens (X n) := ⟨ball x ρ, isOpen_ball⟩
  let U := Wkp.lowerOrder k W
  let hle : V ≤ Ω₀ := le_top
  refine ⟨Wkp.restrictL hle k U, ?_⟩
  refine (Wkp.value_restrictL_ae hle k U).trans ?_
  have hWV : ⇑(Wkp.value k U) =ᵐ[(μ₀).restrict V]
      (fixedBallOpens n : Set (X n)).indicator
        (fun y => ψ y * W1p.value (u : FixedBallH1 n) y) := by
    filter_upwards [ae_restrict_of_ae (s := (V : Set (X n))) hW] with y hy
    change Wkp.value k (Wkp.lowerOrder k W) y = _
    rw [← Wkp.value_succ, ← Wkp.value_firstOrder]
    exact hy
  filter_upwards [hWV, ae_restrict_mem V.isOpen.measurableSet] with y hy hyV
  have hyB : y ∈ (fixedBallOpens n : Set (X n)) :=
    (ball_subset_ball (by norm_num : (7:ℝ)/8 ≤ 1)) (hsub hyV)
  rw [hy, indicator_of_mem hyB, (hψOne y (ball_subset_closedBall hyV)).eq_of_nhds, one_mul]

end CalderonN
