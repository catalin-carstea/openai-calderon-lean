module

public import Proof.CalderonN.MovingSphere.UniformStrict
public import Proof.CalderonN.NormalCoordinates
public import Proof.CalderonN.CylinderCutoff
public import Proof.CalderonN.SmoothMetricFrame
public import Proof.CalderonN.MovingSphere.GreenContinuation
public import Proof.Manuscript.LocalGreenChart
public import Proof.Manuscript.SphereChartLocality
import Proof.CalderonN.SoftplusProfile
import Proof.CalderonN.HorizontalRepresentative
import Proof.CalderonN.MetricPair
import all Proof.CalderonN.Coordinates
import Mathlib.Tactic

public section

open Filter Metric Set CalderonN CalderonPaper.SphereLocality
open scoped ContDiff Topology

namespace CalderonPaper.SphereChoices

variable {n : ℕ}

section RadiusBounds

variable [NeZero n]

/-- A compact conformal family has uniformly bounded canonical frames on
the base before the sphere degree or amplitude is chosen. -/
private theorem compact_frame_bound {K : Set (X n)} (hK : IsCompact K)
    {g : ℝ → MetricField n}
    (hg : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X n => g q.1 q.2 i j))
    (hPos : ∀ l y, (g l y).PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ l in 𝓝 (0 : ℝ), 0 < l →
      ∀ y ∈ K, ∀ i j, |smoothMetricFrame (g l y) i j| ≤ C := by
  let S := Icc (-1 : ℝ) 1
  let T := S ×ˢ K
  have hT : IsCompact T := isCompact_Icc.prod hK
  have hEntry (ij : I n × I n) :
      Continuous (fun q : ℝ × X n => smoothMetricFrame (g q.1 q.2) ij.1 ij.2) := by
    have hC := contDiffOn_smoothMetricFrame (U := univ)
      (fun i j => (hg i j).contDiffOn) (fun (q : ℝ × X n) _ => hPos q.1 q.2) ij.1
    exact (EuclideanSpace.proj ij.2 : X n →L[ℝ] ℝ).continuous.comp
      (contDiffOn_univ.mp hC).continuous
  choose A hA using fun ij : I n × I n => hT.exists_bound_of_continuousOn (hEntry ij).continuousOn
  let C := ∑ ij, max 0 (A ij)
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => le_max_left _ _
  refine ⟨C,hC,?_⟩
  have hS : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hS] with l hl _ y hy i j
  exact (hA (i,j) (l,y) ⟨hl,hy⟩).trans ((le_max_right 0 (A (i,j))).trans
    (Finset.single_le_sum (f := fun ij => max 0 (A ij)) (fun _ _ => le_max_left _ _)
      (Finset.mem_univ (i,j))))

/-- The radius envelope is independent of both dilation and regularization.
Its amplitude threshold can be intersected with the strictness threshold. -/
theorem uniform_conformal_radius_caps (normal : I n) {K : Set (X n)} (hK : IsCompact K)
    {g : MetricField n} (hg : SmoothMetric univ g) (hunit : g 0 = 1) {ρ : ℝ} (hρ : 0 < ρ) :
    let t := conformalDepth normal 4
    let γ := conformalReference (depthScale normal 4) g
    ∃ Rcap : ℕ → ℝ → ℝ,
      (∀ p ≥ 2, ∀ ε > 0, 0 < Rcap p ε) ∧
      ∀ p ≥ 2, ∀ ε > 0, ∀ R ∈ Ioc (0 : ℝ) (Rcap p ε),
        (∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ K, shrinkingRadius R p t δ y ≤ ρ / 2) ∧
        ∀ᶠ l in 𝓝 (0 : ℝ), 0 < l →
          ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ K,
            shrinkingRadius R p t δ y * (beta (γ l) (shrinkingRadius R p t δ) y)^2 ≤ ε := by
  intro t γ
  let e : ℝ → Frame n := fun l y => smoothMetricFrame (γ l y)
  have hγ (i j : I n) : ContDiff ℝ ∞ (fun q : ℝ × X n => γ q.1 q.2 i j) := by
    apply contDiffOn_univ.mp
    simpa only [mem_univ,ofPred_true] using
      contDiffOn_conformalReference_family_entry hg (contDiff_depthScale (normal := normal) 4) i j
  have hPos (l : ℝ) (y : X n) : (γ l y).PosDef :=
    (hg.2 _ (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)
  obtain ⟨E,hE,hFrame⟩ := compact_frame_bound hK hγ hPos
  obtain ⟨c,c₀,M,T,hc,hc₀,hM,Cj,hProfile⟩ :=
    exists_conformal_shrinkingRadius_profile (normal := normal) hK hg hunit e hE hFrame
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn
    ((contDiff_conformalDepth (normal := normal) 4).continuous.continuousOn)
  let S := Real.log (1 + Real.exp A)
  let Z (p : ℕ) := (p : ℝ)^2 * M^2 * (Real.log (1 + Real.exp T))^(p-2)
  let Rcap (p : ℕ) (ε : ℝ) := min ((ρ/2) / S^p) (ε / Z p)
  have hS : 0 < S := Real.log_pos (by linarith [Real.exp_pos A])
  have hZ (p : ℕ) (hp : 2 ≤ p) : 0 < Z p := by
    have ht := Real.log_pos (by linarith [Real.exp_pos T] : 1 < 1 + Real.exp T)
    have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    dsimp only [Z]
    positivity
  refine ⟨Rcap,fun p hp ε hε => lt_min (div_pos (half_pos hρ) (pow_pos hS _))
    (div_pos hε (hZ p hp)),?_⟩
  intro p hp ε hε R hR
  have hRS : R * S^p ≤ ρ/2 := (le_div_iff₀ (pow_pos hS _)).mp
    (hR.2.trans (min_le_left _ _))
  have hRZ : R * Z p ≤ ε := (le_div_iff₀ (hZ p hp)).mp (hR.2.trans (min_le_right _ _))
  refine ⟨?_, ?_⟩
  · intro δ hδ y hy
    have ht : t y ≤ A := (le_abs_self _).trans (hA y hy)
    have hs : softplus δ (t y) ≤ S := SoftplusProfile.softplus_le_log_exp_upper δ _ _ hδ.1 hδ.2 ht
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (softplus_pos hδ.1 _).le hs p) hR.1.le).trans hRS
  · filter_upwards [hProfile] with l hl hlPos δ hδ y hy
    exact ((hl hlPos δ hδ hp R hR.1).2 y hy).trans (by simpa only [Z,mul_assoc] using hRZ)

end RadiusBounds

/-- Uniform chart locality on a signed interval that includes zero. -/
theorem exists_compact_interval_dilatesInto {D : Set (X n)} (hD : IsOpen D)
    (h0 : (0 : X n) ∈ D) (B : ℝ) :
    ∃ (τ : ℝ), 0 < τ ∧ τ ≤ 1 ∧
       ∀ l ∈ Icc (-τ) τ, MapsTo (fun x : X n => l • x) (closedBall 0 B) D := by
  obtain ⟨a, ha, hsub⟩ := Metric.mem_nhds_iff.mp (eventually_dilated_closedBall_mapsTo hD h0 B)
  let τ := min (a/2) 1
  have ht : 0 < τ := lt_min (half_pos ha) zero_lt_one
  refine ⟨τ, ht, min_le_right _ _, fun l hl => hsub ?_⟩
  exact mem_ball_zero_iff.mpr
    ((abs_le.mpr hl).trans_lt ((min_le_left (a/2) (1:ℝ)).trans_lt (half_lt_self ha)))

/-- The two cap metrics produce the same normalized dilation in the local
chart. -/
theorem eqOn_dilatedMetric_of_mapsTo {D U : Set (X n)} {g g' : MetricField n} {l : ℝ}
    (hg : EqOn g g' D) (h : MapsTo (fun x : X n => l • x) U D) :
    EqOn (dilatedMetric g l) (dilatedMetric g' l) U :=
  fun _ hx => hg (h hx)

theorem eqOn_conformalReference_of_dilation {D : Set (X n)} {g g' : MetricField n} {l : ℝ}
    (c : X n → ℝ) (hg : EqOn (dilatedMetric g l) (dilatedMetric g' l) D) :
    EqOn (conformalReference c g l) (conformalReference c g' l) D := by
  intro x hx
  exact congrArg (c x • ·) (hg hx)

theorem beta_eq_of_metric_eq_at {g g' : MetricField n} {y : X n} {r : X n → ℝ} (h : g y = g' y) :
    beta g r y = beta g' r y := by rw [beta,beta,h]

/-- Closed-base points of an actual normal sphere remain in the
normal-pair domain, and hence inside the geodesic chart. -/
theorem endpoint_mem_normalPairDomain
    {Y : Set (X n)} {g : MetricField n} {E : X n × X n → X n} {ρ : ℝ}
    {r : X n → ℝ} {w : X n × X n} (hw : w ∈ bundle Y g)
    (hr : 0 ≤ r w.1) (hρ : r w.1 < ρ) :
    (endpoint E r w, w.1) ∈ normalPairDomain Y g ρ E := by
  refine ⟨(w.1, r w.1 • w.2), ⟨hw.1, ?_⟩, rfl⟩
  change metricPair g w.1 (r w.1 • w.2) (r w.1 • w.2) < ρ^2
  rw [metricPair_smul_same, show metricPair g w.1 w.2 w.2 = 1 from hw.2, mul_one]
  exact pow_lt_pow_left₀ hρ hr two_ne_zero

/-- A framed sphere point represents every unit velocity in the
intrinsic bundle. -/
theorem exists_frame_representation
    {Y : Set (X n)} {g : MetricField n} {e : Frame n}
    (hOrth : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {w : X n × X n} (hw : w ∈ bundle Y g) :
    ∃ z : ↥(standardSphere n), frameVector e w.1 (z : X n) = w.2 := by
  exact exists_unitSphere_frameVector g e w.1 (hOrth _ hw.1) w.2 hw.2

theorem conformalFamily_contDiff (normal : I n) {g : MetricField n}
    (hg : SmoothMetric univ g) (i j : I n) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => conformalReference (depthScale normal 4) g q.1 q.2 i j) := by
  apply contDiffOn_univ.mp
  simpa only [mem_univ,ofPred_true] using
    contDiffOn_conformalReference_family_entry hg (contDiff_depthScale (normal := normal) 4) i j

theorem conformalFamily_posDef (normal : I n) {g : MetricField n} (hg : SmoothMetric univ g)
    (lam : ℝ) (y : X n) :
    (conformalReference (depthScale normal 4) g lam y).PosDef :=
  (hg.2 _ (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)

variable [NeZero n] in
theorem canonicalFrames_contDiff (normal : I n) {g : MetricField n} (hg : SmoothMetric univ g) (i : I n) :
    ContDiff ℝ ∞ (fun q : ℝ × X n =>
      smoothMetricFrame (conformalReference (depthScale normal 4) g q.1 q.2) i) :=
  contDiffOn_univ.mp (contDiffOn_smoothMetricFrame (fun j k => (conformalFamily_contDiff normal hg j k).contDiffOn)
    (fun q _ => conformalFamily_posDef normal hg q.1 q.2) i)

/-- The actual fixed compact choices used by the sweep also give the
signed (including zero) metric normal-coordinate witness. -/
theorem exists_actual_compact_normalRoom
    (normal : I n) {D : Set (X n)} (hD : IsOpen D) (h0 : (0 : X n) ∈ D)
    {g q : MetricField n} (hq : SmoothMetric univ q) (he : EqOn q g D) :
    let Z := closedBall (0 : X n) (5/2)
    let B := ball (0 : X n) 3
    ∃ (ρ τ : ℝ) (E : ℝ → X n × X n → X n),
      0 < ρ ∧ 0 < τ ∧ τ ≤ 1 ∧ ContDiff ℝ ∞ (fun p : ℝ × (X n × X n) => E p.1 p.2) ∧
      (∀ l ∈ Icc (-τ) τ, MapsTo (fun x : X n => l • x) (closedBall 0 5) D) ∧
      (∀ l ∈ Icc (-1 : ℝ) 1,
        NormalCoordinates Z B (conformalReference (depthScale normal 4) q l) (E l) (fun _ => ρ)) ∧
      (∀ l ∈ Icc (-τ) τ,
        NormalCoordinates Z B (conformalReference (depthScale normal 4) g l) (E l) (fun _ => ρ)) := by
  intro Z B
  have hZB : Z ⊆ B := closedBall_subset_ball (by norm_num)
  obtain ⟨ρ,E,hρ,hE,hN⟩ := exists_uniform_normalCoordinates
    (conformalFamily_contDiff normal hq) (conformalFamily_posDef normal hq)
    (isCompact_closedBall (0 : X n) (5/2)) isOpen_ball hZB
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
  obtain ⟨τ,hτ,hτ1,hDil⟩ := exists_compact_interval_dilatesInto hD h0 5
  refine ⟨ρ,τ,E,hρ,hτ,hτ1,hE,hDil,hN,?_⟩
  intro l hl
  have hl1 : l ∈ Icc (-1 : ℝ) 1 := ⟨(neg_le_neg hτ1).trans hl.1, hl.2.trans hτ1⟩
  have hB5 : B ⊆ closedBall (0 : X n) 5 := ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by norm_num))
  have hEq := eqOn_conformalReference_of_dilation (depthScale normal 4)
    (eqOn_dilatedMetric_of_mapsTo he ((hDil l hl).mono_left hB5))
  exact normalCoordinates_congrOn isOpen_ball hZB hEq (hN l hl1)

end CalderonPaper.SphereChoices
