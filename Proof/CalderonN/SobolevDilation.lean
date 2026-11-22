module

public import Proof.CalderonN.Coordinates
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Tactic

/-! Continuity of dilation in bulk L², adapted from
`CollaboratorSmoothDensityBallOct17` in the Theorem 3.1 release. -/

public section

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal Topology
namespace CalderonN

variable {dim : ℕ}

theorem tendsto_eLpNorm_comp_smul_sub_of_continuous {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : (X dim) → G} (hg : Continuous g) (hgc : HasCompactSupport g)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {c : ι → ℝ} (hc : Tendsto c l (𝓝 1)) :
    Tendsto (fun i => eLpNorm (fun x => g (c i • x) - g x) p volume) l (𝓝 0) := by
  obtain ⟨R0, hR0⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : (X dim))
  set R := max R0 0 with hRdef
  have hR : tsupport g ⊆ Metric.closedBall 0 R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR_nonneg : 0 ≤ R := le_max_right _ _
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hb : MemLp ((Metric.closedBall (0 : (X dim)) (2 * R)).indicator fun _ => (1 : ℝ)) p volume :=
    memLp_indicator_const p
      (Metric.isClosed_closedBall (x := (0 : (X dim))) (ε := 2 * R)).measurableSet.nullMeasurableSet (1 : ℝ)
      (Or.inr (measure_closedBall_lt_top (μ := volume)).ne)
  have hev : ∀ᶠ i in l, c i ∈ Ioo (1 / 2 : ℝ) 2 := hc (Ioo_mem_nhds (by norm_num) (by norm_num))
  have key := TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto hp0 hp
    (f := fun i x => g (c i • x)) (g := g)
    (Eventually.of_forall fun i => (hg.comp (continuous_const_smul _)).aestronglyMeasurable)
    hg.aestronglyMeasurable hb (C := Real.toNNReal (2 * M))
    (hev.mono fun i hi => Eventually.of_forall fun x => by
      by_cases hx : x ∈ Metric.closedBall (0 : (X dim)) (2 * R)
      · rw [indicator_of_mem hx, enorm_one, mul_one, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (by linarith [hM (c i • x), hM x]))
      · have hx' : R < ‖x‖ := by
          simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx; linarith
        have h1 : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => by
          have := hR h; simp only [Metric.mem_closedBall, dist_zero_right] at this; linarith
        have h2 : g (c i • x) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
          have := hR h
          simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (show (0 : ℝ) < c i by linarith [hi.1])] at this
          simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
          nlinarith [hi.1]
        simp [h1, h2])
    (Eventually.of_forall fun x => by
      have := (hg.tendsto _).comp (hc.smul_const x)
      simpa [Function.comp_def] using this)
  exact key

theorem eLpNorm_comp_smul_le {G : Type*} [NormedAddCommGroup G] (h : (X dim) → G) {p : ℝ≥0∞}
    {c : ℝ} (hc : 1 / 2 < c) :
    eLpNorm (fun x => h (c • x)) p volume ≤
      ENNReal.ofReal ((2 : ℝ)^dim) ^ (1 / p).toReal * eLpNorm h p volume := by
  have hc0 : c ≠ 0 := by intro h0; rw [h0] at hc; norm_num at hc
  rw [show (fun x => h (c • x)) = h ∘ (fun x : (X dim) => c • x) from rfl,
    ← (measurableEmbedding_const_smul₀ hc0).eLpNorm_map_measure,
    Measure.map_addHaar_smul volume hc0]
  by_cases h0 : ENNReal.ofReal |(c ^ Module.finrank ℝ (X dim))⁻¹| = 0
  · rw [h0, zero_smul, eLpNorm_measure_zero]; exact bot_le
  rw [eLpNorm_smul_measure_of_ne_zero h0, smul_eq_mul]
  gcongr
  rw [finrank_euclideanSpace_fin]
  have hcpos : 0 < c := by linarith
  rw [abs_of_pos (by positivity)]
  have hpow : ((1 / 2 : ℝ) ^ dim) ≤ c ^ dim :=
    pow_le_pow_left₀ (by norm_num) hc.le _
  calc
    (c ^ dim)⁻¹ ≤ ((1 / 2 : ℝ) ^ dim)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow
    _ = (2 : ℝ)^dim := by rw [one_div, inv_pow, inv_inv]

theorem tendsto_eLpNorm_comp_smul_sub {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : (X dim) → G} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hF : MemLp F p volume)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {c : ι → ℝ} (hc : Tendsto c l (𝓝 1)) :
    Tendsto (fun i => eLpNorm (fun x => F (c i • x) - F x) p volume) l (𝓝 0) := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ)^dim) ^ (1 / p).toReal with hKdef
  have hKtop : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hK2 : K + 2 ≠ ⊤ := by finiteness
  have hK0 : K + 2 ≠ 0 := by positivity
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set δ := ε / (K + 2) with hδdef
  have hδ : 0 < δ := ENNReal.div_pos hε.ne' hK2
  obtain ⟨g, hgc, hFg, hgcont, hgmem⟩ :=
    MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le hp hF hδ.ne'
  have hconv := tendsto_eLpNorm_comp_smul_sub_of_continuous hgcont hgc hp0 hp hc
  have hev : ∀ᶠ i in l, c i ∈ Ioo (1 / 2 : ℝ) 2 := hc (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hev, (ENNReal.tendsto_nhds_zero.1 hconv) δ hδ] with i hi hgi
  have hsplit : (fun x => F (c i • x) - F x) =
      (fun x => (F - g) (c i • x)) + (fun x => g (c i • x) - g x) + (g - F) := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply]; abel
  calc eLpNorm (fun x => F (c i • x) - F x) p volume
      ≤ eLpNorm (fun x => (F - g) (c i • x)) p volume +
          eLpNorm (fun x => g (c i • x) - g x) p volume + eLpNorm (g - F) p volume := by
        rw [hsplit]
        refine (eLpNorm_add_le hp1).trans ?_
        gcongr
        exact eLpNorm_add_le hp1
    _ ≤ K * δ + δ + δ := by
        gcongr
        · exact (eLpNorm_comp_smul_le _ hi.1).trans (by gcongr)
        · rw [eLpNorm_sub_comm]; exact hFg
    _ = (K + 2) * δ := by ring
    _ = ε := ENNReal.mul_div_cancel hK0 hK2

end CalderonN
