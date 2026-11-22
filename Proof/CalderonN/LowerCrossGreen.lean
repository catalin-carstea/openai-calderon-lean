module

public import Proof.CalderonN.ChartNormalization
public import Proof.CalderonN.GreenDistanceBound
import Proof.CalderonN.DilationGeometry
import Mathlib.Tactic

@[expose] public section

/- Port of the lower cross in FixedTube/CoarseGreenSeed from the 3D Theorem 3.1 release. -/
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace CalderonN
variable {n : ℕ}

/-- The off-diagonal cross with one factor in the strict lower strip. -/
def lowerCross (normal : I n) (B η : ℝ) : Set (X n × X n) :=
  OffDiagonal (ball 0 B) ∩ {q | q.2 normal < -η ∨ q.1 normal < -η}

theorem eventually_dilated_mem_side_of_negative_coordinate
    {normal : I n} {Ω W : Set (X n)} (hside : ContainsAlignedSide normal Ω W) (B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ x ∈ closedBall (0 : (X n)) B,
      x normal ≤ -η → lam • x ∈ W := by
  obtain ⟨V,s,hV,h₀V,_,hs,hs₀,hsD,hside⟩ := hside
  let K := closedBall (0 : (X n)) B ∩ {x | x normal ≤ -η}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le (EuclideanSpace.proj (𝕜 := ℝ) normal).continuous continuous_const)
  have hNeg (x : (X n)) (hx : x ∈ K) : fderiv ℝ s 0 x < 0 := by
    rw [hsD]
    exact (show x normal ≤ -η from hx.2).trans_lt (neg_neg_of_pos hη)
  have h := eventually_nhdsWithin_iff.mp
    (eventually_dilated_subset_of_negative_tangent hV h₀V hK
      ((hs.contDiffAt (hV.mem_nhds h₀V)).differentiableAt (by simp)) hs₀ hside hNeg)
  filter_upwards [h] with lam h hl x hx hNeg
  exact h hl x ⟨hx,hNeg⟩

theorem eventually_lowerCross_greenSolution
    (hn : 3 ≤ n) {normal : I n} {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : (MetricField n)} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    (M : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (lowerCross normal M η)
        (dilatedInitialGreen W G₁ G₂ lam) := by
  let : NeZero n := ⟨by omega⟩
  have hKnown := eventually_dilated_mem_side_of_negative_coordinate hside M hη
  obtain ⟨V,s,hV,h₀V,hVΩ,_,_,_,_⟩ := hside
  have hChart : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ x ∈ closedBall (0 : (X n)) M, lam • x ∈ Ω := by
    apply (isCompact_closedBall (0 : (X n)) M).eventually_forall_of_forall_eventually
    intro x _
    have hcont : ContinuousAt (fun q : ℝ × (X n) => q.1 • q.2) (0,x) :=
      (continuous_fst.smul continuous_snd).continuousAt
    exact hcont.preimage_mem_nhds (by simpa only [zero_smul] using hΩ.mem_nhds (hVΩ h₀V))
  filter_upwards [hChart,hKnown] with lam hLam hSide hpos
  refine (dilatedInitialGreen_productSolution (by omega : 2 ≤ n) hΩ hW hg₁ hg₂ hG₁ hG₂ hmetric hgreen hpos).mono ?_
  intro q hq
  have hx : q.1 ∈ closedBall (0 : (X n)) M := ball_subset_closedBall hq.1.1
  have hy : q.2 ∈ closedBall (0 : (X n)) M := ball_subset_closedBall hq.1.2.1
  refine ⟨⟨hLam _ hx,hLam _ hy,hq.1.2.2⟩,?_⟩
  rcases hq.2 with h | h
  · exact Or.inl (hSide hpos _ hy (show q.2 normal < -η from h).le)
  · exact Or.inr (hSide hpos _ hx (show q.1 normal < -η from h).le)

/-- Both prescribed Green pieces are uniformly bounded on each separated part of
the lower cross, on which the dilated mixed equations already hold. -/
theorem exists_uniform_lowerCross_greenSolution (hn : 3 ≤ n)
    {normal : I n} {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {G₁ G₂ : X n × X n → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    (B : ℝ) {d η : ℝ} (hd : 0 < d) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (lowerCross normal B η)
        (dilatedInitialGreen W G₁ G₂ lam) ∧
      ∀ q ∈ lowerCross normal B η, d ≤ dist q.1 q.2 →
        |dilatedInitialGreen W G₁ G₂ lam q| ≤ C := by
  let : NeZero n := ⟨by omega⟩
  have h₀ : (0 : X n) ∈ Ω := by
    obtain ⟨V,s,hV,h₀V,hVΩ,_,_,_,_⟩ := hside
    exact hVΩ h₀V
  obtain ⟨ρ₁,C₁,hρ₁,hC₁,h₁⟩ := exists_Green_distance_bound hn hΩ h₀ hg₁ hG₁
  obtain ⟨ρ₂,C₂,hρ₂,hC₂,h₂⟩ := exists_Green_distance_bound hn hΩ h₀ hg₂ hG₂
  have hBound := eventually_dilatedInitialGreen_distance_bound (W := W) hn hρ₁ hρ₂ h₁ h₂ B
  have hSol := eventually_lowerCross_greenSolution hn hΩ hW hside
    ⟨fun i j => (hg₁.1 i j).mono (subset_univ Ω), fun x _ => hg₁.2 x (mem_univ _)⟩
    ⟨fun i j => (hg₂.1 i j).mono (subset_univ Ω), fun x _ => hg₂.2 x (mem_univ _)⟩
    hG₁ hG₂ hmetric hgreen B hη
  have hC : 0 ≤ max C₁ C₂ := hC₁.trans (le_max_left _ _)
  refine ⟨max C₁ C₂ * d ^ (2 - (n : ℝ)), mul_nonneg hC (Real.rpow_nonneg hd.le _), ?_⟩
  filter_upwards [hBound, hSol] with lam hb hs hpos
  refine ⟨hs hpos, fun q hq hsep => ?_⟩
  have hn' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact (hb hpos q.1 (ball_subset_closedBall hq.1.1) q.2
    (ball_subset_closedBall hq.1.2.1) hq.1.2.2).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hd hsep (by linarith)) hC)

end CalderonN
