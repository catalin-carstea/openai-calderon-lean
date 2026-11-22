module

public import Proof.CalderonN.FixedTube.CoarseSeed
public import Proof.CalderonN.LowerCrossGreen

public import Proof.CalderonN.FixedTube.Initialization
import Proof.CalderonN.DilatedGreenBounds
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- The separated Green bound on the known cross gives uniformly
bounded coarse Green patches on each fixed separated range. -/
theorem exists_uniform_bounded_coarse_initialGreen (hn : 3 ≤ dim)
    {Ω W : Set (X dim)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1)
    {G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W)) :
    ∃ c > 0, ∀ B d η : ℝ, 0 < B → 0 < d → 0 < η →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∃ F,
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (coarseDomain normal B d c) F ∧
        EqOn F (dilatedInitialGreen W G₁ G₂ lam) (coarseDomain normal B d c ∩ lowerSidePairs normal η) ∧
        ∀ q ∈ coarseDomain normal B d c, |F q| ≤ C := by
  obtain ⟨c,hc,hseed⟩ := (exists_glued_coarse_seed_with_bound (normal := normal)) hg₁ hg₂ h₁ h₂
  refine ⟨c,hc,fun B d η hB hd hη => ?_⟩
  obtain ⟨M,η',hM,hη',hηη',C,hC,hBuild⟩ := hseed B d η hB hd hη
  obtain ⟨L,hL,hLower⟩ := exists_uniform_lowerCross_greenSolution hn hΩ hW hside
    hg₁ hg₂ hG₁ hG₂ hmetric hgreen M (d := (3/16 : ℝ)*d) (by positivity) hη'
  refine ⟨C*L,mul_nonneg hC hL,?_⟩
  filter_upwards [hBuild,hLower] with lam hExt hF hpos
  obtain ⟨hSol,hBnd⟩ := hF hpos
  obtain ⟨O,G,_,hCO,_,hSol,hAgree,hGB⟩ := hExt _ hSol
  refine ⟨G,hSol.mono hCO,?_,hGB L hL (fun q hq hp => hBnd q hq (by simpa only [dist_eq_norm] using hp))⟩
  intro q hq
  have hqsep : q.1 ≠ q.2 := by
    intro he
    have h := hq.1.2.2.1
    rw [he,sub_self,norm_zero] at h
    exact hd.not_gt h
  have hl : min (q.1 normal) (q.2 normal) < -η := hq.2
  exact hAgree ((lowerCross_mem_of_norm (normal := normal)) (hq.1.1.trans hM) (hq.1.2.1.trans hM) hqsep
    (show min (q.1 normal) (q.2 normal) < -η' from hl.trans_le (neg_le_neg hηη')))

/-- Uniform fixed-separation initialization for the actual dilated
Green kernels. Both lower pieces are inherited on the target range. -/
theorem exists_bounded_fixedSeparation_initialGreen (hn : 3 ≤ dim)
    {Ω W : Set (X dim)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1)
    {G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {B d η : ℝ} (hB : 0 < B) (hd : 0 < d) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ), IsOpen O ∧ fixedSeparationSet B d ⊆ O ∧
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O G ∧
        EqOn G (dilatedInitialGreen W G₁ G₂ lam) (fixedSeparationSet B d ∩ lowerSidePairs normal η) ∧
        ∀ q ∈ fixedSeparationSet B d, |G q| ≤ C := by
  obtain ⟨c,hc,hcoarse⟩ := (exists_uniform_bounded_coarse_initialGreen (normal := normal)) hn hΩ hW hside hg₁ hg₂ h₁ h₂
    hG₁ hG₂ hmetric hgreen
  let ε := min (1/10 : ℝ) (c/13)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  let P (lam B' d' : ℝ) (F : (X dim) × (X dim) → ℝ) :=
    EqOn F (dilatedInitialGreen W G₁ G₂ lam) (coarseDomain normal B' d' c ∩ lowerSidePairs normal η)
  have hp := exists_fixedSeparation_productSolution_of_coarse_with_bound (normal := normal) (M := B+4)
    hB.le hd hc hε (min_le_left _ _) (by linarith [min_le_right (1/10 : ℝ) (c/13)])
    (by linarith) hg₁ hg₂ h₁ h₂ P true
    (fun B' hB' d' hd' => by
      obtain ⟨C,hC,h⟩ := hcoarse B' d' η (hB.trans hB') hd'.1 hη
      refine ⟨C,hC,h.mono fun _ h hl => ?_⟩
      obtain ⟨F,hF,hEq,hB⟩ := h hl
      exact ⟨F,hF,hEq,fun _ => hB⟩)
  obtain ⟨B',hB',d',hd',C,hC,hSol⟩ := hp
  refine ⟨C,hC,?_⟩
  filter_upwards [hSol] with lam hLam hpos
  obtain ⟨O,F,G,hO,hSO,_,_,hG,hGF,hFP,hBd⟩ := hLam hpos
  refine ⟨O,G,hO,hSO,hG,?_,hBd rfl⟩
  intro q hq
  have hlo : min (q.1 normal) (q.2 normal) < -η := hq.2
  have hSep : 0 < ‖q.1-q.2‖ := hd.trans_le hq.1.2.2
  have hqC : q ∈ coarseDomain normal B' d' c :=
    ⟨hq.1.1.trans_lt hB',hq.1.2.1.trans_lt hB',hd'.2.trans_le hq.1.2.2,
      (hlo.trans (neg_neg_of_pos hη)).trans (mul_pos hc hSep)⟩
  exact (hGF hqC).trans (hFP ⟨hqC,hq.2⟩)


/-- Qualitative fixed-separation initialization for the actual dilated
Green kernels. Both lower pieces are inherited on the target range. -/
theorem exists_fixedSeparation_initialGreen (hn : 3 ≤ dim)
    {Ω W : Set (X dim)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1)
    {G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {B d η : ℝ} (hB : 0 < B) (hd : 0 < d) (hη : 0 < η) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ), IsOpen O ∧ fixedSeparationSet B d ⊆ O ∧
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O G ∧
        EqOn G (dilatedInitialGreen W G₁ G₂ lam) (fixedSeparationSet B d ∩ lowerSidePairs normal η) := by
  obtain ⟨_,_,h⟩ := (exists_bounded_fixedSeparation_initialGreen (normal := normal))
    hn hΩ hW hside hg₁ hg₂ h₁ h₂ hG₁ hG₂ hmetric hgreen hB hd hη
  exact h.mono fun _ h hp => by
    obtain ⟨O,G,hO,hSub,hG,hEq,_⟩ := h hp
    exact ⟨O,G,hO,hSub,hG,hEq⟩

end CalderonN.FixedTube
