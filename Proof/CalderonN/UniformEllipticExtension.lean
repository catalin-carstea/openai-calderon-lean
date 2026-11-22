module

public import Proof.CalderonN.FixedBallSourceEnergy
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

public section

/- The positive-definite extension and global Lipschitz control from the
   3D Theorem 3.1 release, unchanged in the choice of radii. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff Matrix Matrix.Norms.Elementwise InnerProductSpace
namespace CalderonN
open TauCeti TauCeti.PDE
variable {d : ℕ}

theorem exists_lipschitzWith_of_hasCompactSupport {f : (X d) → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : ∃ K : NNReal, LipschitzWith K f := by
  have hcont : Continuous (fun x => ‖fderiv ℝ f x‖₊) :=
    continuous_nnnorm.comp (hf.continuous_fderiv one_ne_zero)
  have hcs : HasCompactSupport (fun x => ‖fderiv ℝ f x‖₊) := (hc.fderiv (𝕜 := ℝ)).comp_left nnnorm_zero
  obtain ⟨K, hK⟩ := hcont.bddAbove_range_of_hasCompactSupport hcs
  exact ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero)
    fun x => hK ⟨x, rfl⟩⟩

 
@[expose] def bump (r R : ℝ) (hr : 0 < r) (hrR : r < R) : ContDiffBump (0 : (X d)) := ⟨r, R, hr, hrR⟩

@[simp] theorem bump_rIn (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    (bump (d := d) r R hr hrR).rIn = r := rfl
@[simp] theorem bump_rOut (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    (bump (d := d) r R hr hrR).rOut = R := rfl

theorem contDiff_entry {a : (X d) → Matrix (Fin d) (Fin d) ℝ} {n : WithTop ℕ∞} (ha : ContDiff ℝ n a)
    (i j : Fin d) : ContDiff ℝ n (fun x => a x i j) :=
  contDiff_pi.mp (contDiff_pi.mp ha i) j

 
theorem dotProduct_self_eq_norm_sq (ξ : (X d)) : ξ.ofLp ⬝ᵥ ξ.ofLp = ‖ξ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

theorem abs_dotProduct_le (η ξ : (X d)) : |η.ofLp ⬝ᵥ ξ.ofLp| ≤ ‖η‖ * ‖ξ‖ := by
  have := abs_real_inner_le_norm ξ η
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simpa [mul_comm] using this

 
def ellExt (â : (X d) → Matrix (Fin d) (Fin d) ℝ) (lam : ℝ) : (X d) → Matrix (Fin d) (Fin d) ℝ :=
  fun x => bump (7 / 8) (15 / 16) (by norm_num) (by norm_num) x • â x +
    (1 - bump (7 / 8) (15 / 16) (by norm_num) (by norm_num) x) • (lam • (1 : Matrix _ _ ℝ))

theorem ellExt_eq {â : (X d) → Matrix (Fin d) (Fin d) ℝ} {lam : ℝ} {x : (X d)}
    (hx : x ∈ ball (0 : (X d)) (7 / 8)) : ellExt â lam x = â x := by
  have h1 : bump (7 / 8) (15 / 16) (by norm_num) (by norm_num) x = 1 :=
    ContDiffBump.one_of_mem_closedBall _ (by simpa using (mem_ball.mp hx).le)
  simp [ellExt, h1]

theorem uniformlyEllipticOn_ellExt {a â : (X d) → Matrix (Fin d) (Fin d) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (fixedBallOpens d : Set (X d)) a lam Lam)
    (hâ : ∀ x ∈ closedBall (0 : (X d)) (3 / 2), â x = a x) :
    UniformlyEllipticOn (Set.univ : Set (X d)) (ellExt â lam) lam Lam := by
  obtain ⟨hlam, hlL, hx⟩ := hell
  refine ⟨hlam, hlL, fun x _ => ?_⟩
  set χ := bump (7 / 8) (15 / 16) (by norm_num) (by norm_num)
  have hc0 : 0 ≤ χ x := χ.nonneg
  have hc1 : χ x ≤ 1 := χ.le_one
   
  have hin : χ x ≠ 0 → x ∈ (fixedBallOpens d : Set (X d)) ∧ â x = a x := fun h => by
    have hts : x ∈ tsupport χ := subset_tsupport _ h
    rw [χ.tsupport_eq] at hts
    have hn : ‖x‖ ≤ 15 / 16 := by simpa [χ] using hts
    refine ⟨by change x ∈ ball (0 : X d) 1; rw [mem_ball_zero_iff]; linarith,
      hâ x (by simp only [mem_closedBall, dist_zero_right]; linarith)⟩
  have hform : ∀ η ξ : (X d), η.ofLp ⬝ᵥ (ellExt â lam x).mulVec ξ.ofLp =
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

theorem contDiff_ellExt {â : (X d) → Matrix (Fin d) (Fin d) ℝ} (hâ : ContDiff ℝ ∞ â) (lam : ℝ) :
    ContDiff ℝ ∞ (ellExt â lam) :=
  ((ContDiffBump.contDiff _).smul hâ).add
    ((contDiff_const.sub (ContDiffBump.contDiff _)).smul contDiff_const)

 
theorem exists_lipschitz_entries {â : (X d) → Matrix (Fin d) (Fin d) ℝ} (hâ : ContDiff ℝ ∞ â)
    (hc : HasCompactSupport â) : ∃ K : NNReal, ∀ i j, LipschitzWith K (fun x => â x i j) := by
  have h : ∀ i j, ∃ K : NNReal, LipschitzWith K (fun x => â x i j) := fun i j =>
    exists_lipschitzWith_of_hasCompactSupport ((contDiff_entry hâ i j).of_le (by simp))
      (hc.comp_left (g := fun M : Matrix (Fin d) (Fin d) ℝ => M i j) rfl)
  choose K hK using h
  refine ⟨∑ i, ∑ j, K i j, fun i j => (hK i j).weaken ?_⟩
  exact (Finset.single_le_sum (f := K i) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, K i j) (fun _ _ => by positivity) (Finset.mem_univ i))

/-- The extension is constant off the support of the bump. -/
theorem hasCompactSupport_ellExt_sub_const (a : X d → Mat d) (lam : ℝ) :
    HasCompactSupport (fun x => ellExt a lam x - lam • (1 : Mat d)) := by
  let χ := bump (d := d) (7/8) (15/16) (by norm_num) (by norm_num)
  refine χ.hasCompactSupport.mono' fun x hx => subset_tsupport _ ?_
  rw [Function.mem_support] at hx ⊢
  intro h0
  apply hx
  simp only [ellExt, χ] at h0 ⊢
  rw [h0]
  simp

theorem exists_lipschitz_ellExt {â : (X d) → Matrix (Fin d) (Fin d) ℝ} (hâ : ContDiff ℝ ∞ â)
    (lam : ℝ) : ∃ K : NNReal, ∀ i j, LipschitzWith K (fun x => ellExt â lam x i j) := by

  have hdiff : ContDiff ℝ ∞ (fun x => ellExt â lam x - lam • (1 : Matrix (Fin d) (Fin d) ℝ)) :=
    (contDiff_ellExt hâ lam).sub contDiff_const
  have hcs := hasCompactSupport_ellExt_sub_const â lam
  obtain ⟨K, hK⟩ := exists_lipschitz_entries hdiff hcs
  refine ⟨K, fun i j => ?_⟩
  have := (hK i j).add (LipschitzWith.const (α := (X d)) ((lam • (1 : Matrix (Fin d) (Fin d) ℝ)) i j))
  simpa using this

end CalderonN
