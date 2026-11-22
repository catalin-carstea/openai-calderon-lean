module

public import Proof.CalderonN.BallRegularity.FixedRegularity
public import Proof.CalderonN.BallRegularity.FixedCalculus
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! From Proof/Archive/CollaboratorRegularityCoefficientsOct17.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

noncomputable section
open MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace CalderonN.BallRegularity

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE


theorem exists_lipschitzWith_of_hasCompactSupport {f : (X dim) → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : ∃ K : NNReal, LipschitzWith K f := by
  have hcont : Continuous (fun x => ‖fderiv ℝ f x‖₊) :=
    continuous_nnnorm.comp (hf.continuous_fderiv one_ne_zero)
  have hcs : HasCompactSupport (fun x => ‖fderiv ℝ f x‖₊) := (hc.fderiv (𝕜 := ℝ)).comp_left nnnorm_zero
  obtain ⟨K, hK⟩ := hcont.bddAbove_range_of_hasCompactSupport hcs
  exact ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero)
    fun x => hK ⟨x, rfl⟩⟩


def bump (r R : ℝ) (hr : 0 < r) (hrR : r < R) : ContDiffBump (0 : (X dim)) := ⟨r, R, hr, hrR⟩

@[simp] theorem bump_rIn (r R : ℝ) (hr : 0 < r) (hrR : r < R) : (bump (dim := dim) r R hr hrR).rIn = r := rfl
@[simp] theorem bump_rOut (r R : ℝ) (hr : 0 < r) (hrR : r < R) : (bump (dim := dim) r R hr hrR).rOut = R := rfl

theorem contDiff_entry {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} {n : WithTop ℕ∞} (ha : ContDiff ℝ n a)
    (i j : Fin dim) : ContDiff ℝ n (fun x => a x i j) :=
  contDiff_pi.mp (contDiff_pi.mp ha i) j


theorem exists_smooth_extension {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ}
    (ha : ContDiffOn ℝ ∞ a (closedBall 0 2)) :
    ∃ â : (X dim) → Matrix (Fin dim) (Fin dim) ℝ, ContDiff ℝ ∞ â ∧
      (∀ x ∈ closedBall (0 : (X dim)) (3 / 2), â x = a x) ∧ HasCompactSupport â := by
  let χ := bump (dim := dim) (3 / 2) (7 / 4) (by norm_num) (by norm_num)
  refine ⟨fun x => χ x • a x, ?_, fun x hx => ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x‖ < 2
    · have hmem : closedBall (0 : (X dim)) 2 ∈ nhds x :=
        closedBall_mem_nhds_of_mem (by simpa using hx)
      exact (χ.contDiff.contDiffAt).smul (ha.contDiffAt hmem)
    · have hfar : ∀ᶠ y in nhds x, (fun y => χ y • a y) y = (fun _ => (0 : Matrix _ _ ℝ)) y := by
        have hout : x ∉ closedBall (0 : (X dim)) (7 / 4) := by
          simp only [mem_closedBall, dist_zero_right, not_le]; linarith
        have : ∀ᶠ y in nhds x, y ∉ tsupport χ := by
          rw [χ.tsupport_eq]
          exact isClosed_closedBall.isOpen_compl.mem_nhds hout
        filter_upwards [this] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
      exact contDiffAt_const.congr_of_eventuallyEq hfar
  · simp only
    rw [χ.one_of_mem_closedBall (by simpa [χ] using hx), one_smul]
  · refine χ.hasCompactSupport.mono' fun x hx => subset_tsupport _ ?_
    rw [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by simp only [h0, zero_smul])


theorem dotProduct_self_eq_norm_sq (ξ : (X dim)) : ξ.ofLp ⬝ᵥ ξ.ofLp = ‖ξ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

theorem abs_dotProduct_le (η ξ : (X dim)) : |η.ofLp ⬝ᵥ ξ.ofLp| ≤ ‖η‖ * ‖ξ‖ := by
  have := abs_real_inner_le_norm ξ η
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simpa [mul_comm] using this


def ellExt (â : (X dim) → Matrix (Fin dim) (Fin dim) ℝ) (lam : ℝ) : (X dim) → Matrix (Fin dim) (Fin dim) ℝ :=
  fun x => bump (dim := dim) (7 / 8) (15 / 16) (by norm_num) (by norm_num) x • â x +
    (1 - bump (dim := dim) (7 / 8) (15 / 16) (by norm_num) (by norm_num) x) • (lam • (1 : Matrix _ _ ℝ))

theorem ellExt_eq {â : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} {lam : ℝ} {x : (X dim)}
    (hx : x ∈ ball (0 : (X dim)) (7 / 8)) : ellExt â lam x = â x := by
  have h1 : bump (dim := dim) (7 / 8) (15 / 16) (by norm_num) (by norm_num) x = 1 :=
    ContDiffBump.one_of_mem_closedBall _ (by simpa using (mem_ball.mp hx).le)
  simp [ellExt, h1]

theorem uniformlyEllipticOn_ellExt {a â : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim)) a lam Lam)
    (hâ : ∀ x ∈ closedBall (0 : (X dim)) (3 / 2), â x = a x) :
    UniformlyEllipticOn (Set.univ : Set (X dim)) (ellExt â lam) lam Lam := by
  obtain ⟨hlam, hlL, hx⟩ := hell
  refine ⟨hlam, hlL, fun x _ => ?_⟩
  set χ := bump (dim := dim) (7 / 8) (15 / 16) (by norm_num) (by norm_num)
  have hc0 : 0 ≤ χ x := χ.nonneg
  have hc1 : χ x ≤ 1 := χ.le_one

  have hin : χ x ≠ 0 → x ∈ ((fixedBallOpens dim) : Set (X dim)) ∧ â x = a x := fun h => by
    have hts : x ∈ tsupport χ := subset_tsupport _ h
    rw [χ.tsupport_eq] at hts
    have hn : ‖x‖ ≤ 15 / 16 := by simpa [χ] using hts
    refine ⟨by simp only [fixedBallOpens, TopologicalSpace.Opens.coe_mk, mem_ball, dist_zero_right]; linarith,
      hâ x (by simp only [mem_closedBall, dist_zero_right]; linarith)⟩
  have hform : ∀ η ξ : (X dim), η.ofLp ⬝ᵥ (ellExt â lam x).mulVec ξ.ofLp =
      χ x * (η.ofLp ⬝ᵥ (â x).mulVec ξ.ofLp) + (1 - χ x) * lam * (η.ofLp ⬝ᵥ ξ.ofLp) := by
    intro η ξ
    simp only [ellExt, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, χ]
    ring
  constructor
  · intro ξ
    rw [Matrix.toQuadraticForm'_apply, hform, dotProduct_self_eq_norm_sq]
    by_cases h : χ x = 0
    · rw [h]; nlinarith [sq_nonneg ‖ξ‖]
    · obtain ⟨hxB, heq⟩ := hin h
      have := (hx hxB).1 ξ
      rw [Matrix.toQuadraticForm'_apply, ← heq] at this
      nlinarith [sq_nonneg ‖ξ‖]
  · intro η ξ
    rw [hform]
    have hdot := abs_dotProduct_le η ξ
    have hnn : 0 ≤ ‖η‖ * ‖ξ‖ := by positivity
    by_cases h : χ x = 0
    · rw [h, zero_mul, zero_add, sub_zero, one_mul, abs_mul, abs_of_pos hlam]
      calc lam * |η.ofLp ⬝ᵥ ξ.ofLp| ≤ lam * (‖η‖ * ‖ξ‖) := by gcongr
        _ ≤ Lam * ‖η‖ * ‖ξ‖ := by nlinarith
    · obtain ⟨hxB, heq⟩ := hin h
      have hb := (hx hxB).2 η ξ
      rw [← heq] at hb
      calc |χ x * (η.ofLp ⬝ᵥ (â x).mulVec ξ.ofLp) + (1 - χ x) * lam * (η.ofLp ⬝ᵥ ξ.ofLp)|
          ≤ |χ x * (η.ofLp ⬝ᵥ (â x).mulVec ξ.ofLp)| + |(1 - χ x) * lam * (η.ofLp ⬝ᵥ ξ.ofLp)| :=
            abs_add_le _ _
        _ = χ x * |η.ofLp ⬝ᵥ (â x).mulVec ξ.ofLp| + (1 - χ x) * lam * |η.ofLp ⬝ᵥ ξ.ofLp| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc0,
              abs_of_nonneg (sub_nonneg.mpr hc1), abs_of_pos hlam]
        _ ≤ χ x * (Lam * ‖η‖ * ‖ξ‖) + (1 - χ x) * lam * (‖η‖ * ‖ξ‖) := by
            gcongr
        _ ≤ Lam * ‖η‖ * ‖ξ‖ := by nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hnn]

theorem contDiff_ellExt {â : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (hâ : ContDiff ℝ ∞ â) (lam : ℝ) :
    ContDiff ℝ ∞ (ellExt â lam) :=
  ((ContDiffBump.contDiff _).smul hâ).add
    ((contDiff_const.sub (ContDiffBump.contDiff _)).smul contDiff_const)


theorem exists_lipschitz_entries {â : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (hâ : ContDiff ℝ ∞ â)
    (hc : HasCompactSupport â) : ∃ K : NNReal, ∀ i j, LipschitzWith K (fun x => â x i j) := by
  have h : ∀ i j, ∃ K : NNReal, LipschitzWith K (fun x => â x i j) := fun i j =>
    exists_lipschitzWith_of_hasCompactSupport ((contDiff_entry hâ i j).of_le (by simp))
      (hc.comp_left (g := fun M : Matrix (Fin dim) (Fin dim) ℝ => M i j) rfl)
  choose K hK using h
  refine ⟨∑ i, ∑ j, K i j, fun i j => (hK i j).weaken ?_⟩
  exact (Finset.single_le_sum (f := K i) (fun j _ => show 0 ≤ K i j from bot_le) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, K i j)
      (fun i _ => show 0 ≤ ∑ j, K i j from bot_le) (Finset.mem_univ i))

theorem exists_lipschitz_ellExt {â : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (hâ : ContDiff ℝ ∞ â)
    (lam : ℝ) : ∃ K : NNReal, ∀ i j, LipschitzWith K (fun x => ellExt â lam x i j) := by

  set χ := bump (dim := dim) (7 / 8) (15 / 16) (by norm_num) (by norm_num)
  have hdiff : ContDiff ℝ ∞ (fun x => ellExt â lam x - lam • (1 : Matrix (Fin dim) (Fin dim) ℝ)) :=
    (contDiff_ellExt hâ lam).sub contDiff_const
  have hcs : HasCompactSupport
      (fun x => ellExt â lam x - lam • (1 : Matrix (Fin dim) (Fin dim) ℝ)) := by
    refine χ.hasCompactSupport.mono' fun x hx => subset_tsupport _ ?_
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp only [ellExt, χ] at h0 ⊢
    rw [h0]
    simp
  obtain ⟨K, hK⟩ := exists_lipschitz_entries hdiff hcs
  refine ⟨K, fun i j => ?_⟩
  have := (hK i j).add (LipschitzWith.const (α := (X dim)) ((lam • (1 : Matrix (Fin dim) (Fin dim) ℝ)) i j))
  simpa using this

end CalderonN.BallRegularity
