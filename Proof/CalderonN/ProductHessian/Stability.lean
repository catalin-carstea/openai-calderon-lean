module

public import Proof.CalderonN.ProductMetricHessian

import Proof.CalderonN.MetricPair
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem continuousAt_metricPair_of_entries
    {D : Type*} [TopologicalSpace D] {p : D} {M : D → (Mat dim)} {v w : D → (X dim)}
    (hM : ∀ i j, ContinuousAt (fun q => M q i j) p)
    (hv : ContinuousAt v p) (hw : ContinuousAt w p) :
    ContinuousAt (fun q => metricPair (fun _ => M q) 0 (v q) (w q)) p := by
  have hv' (i : (I dim)) : ContinuousAt (fun q => v q i) p :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).continuous.continuousAt).comp hv
  have hw' (j : (I dim)) : ContinuousAt (fun q => w q j) p :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j : (X dim) →L[ℝ] ℝ).continuous.continuousAt).comp hw
  simp only [metricPair]
  fun_prop

/-- Nearby chart matrices retain a uniform lower bound on their quadratic forms. -/
theorem eventually_metricPair_lower_of_identity
    {D : Type*} [TopologicalSpace D] {p₀ : D} {M : D → (Mat dim)}
    (hM : ∀ i j, ContinuousAt (fun p => M p i j) p₀) (hM₀ : M p₀ = 1) :
    ∀ᶠ p in 𝓝 p₀, ∀ v : (X dim), ‖v‖ ^ 2 / 2 ≤ metricPair (fun _ => M p) 0 v v := by
  have hunit : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ sphere (0 : (X dim)) 1,
      1 / 2 < metricPair (fun _ => M p) 0 v v := by
    apply (isCompact_sphere (0 : (X dim)) 1).eventually_forall_of_forall_eventually
    intro v hv
    have h := continuousAt_metricPair_of_entries (p := (p₀,v))
      (M := fun q : D × (X dim) => M q.1) (v := Prod.snd) (w := Prod.snd)
      (fun i j => by
        change ContinuousAt ((fun p => M p i j) ∘ Prod.fst) (p₀,v)
        exact (hM i j).comp continuous_fst.continuousAt)
      continuous_snd.continuousAt continuous_snd.continuousAt
    apply h.preimage_mem_nhds
    apply Ioi_mem_nhds
    rw [hM₀, metricPair_one, mem_sphere_zero_iff_norm.mp hv]
    norm_num
  filter_upwards [hunit] with p hp v
  by_cases hv : v = 0
  · simp [hv, metricPair]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hw : ‖v‖⁻¹ • v ∈ sphere (0 : (X dim)) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv,
      Real.norm_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hn]
  have h := (hp _ hw).le
  rw [metricPair_smul_same, inv_pow] at h
  have he : (1 / 2 : ℝ) ≤ metricPair (fun _ => M p) 0 v v / ‖v‖ ^ 2 := by
    simpa only [div_eq_inv_mul] using h
  have h' := (le_div_iff₀' (pow_pos (norm_pos_iff.mpr hv) 2)).mp he
  linarith

private def strictPairTest {D : Type*} (M₁ M₂ : D → (Mat dim)) (b₁ b₂ a₁ a₂ : D → (X dim))
    (H : D → ((X dim) × (X dim)) → ((X dim) × (X dim)) → ℝ) (p : D) (v : (X dim) × (X dim)) : Prop :=
  let E₁ := metricPair (fun _ => M₁ p) 0
  let E₂ := metricPair (fun _ => M₂ p) 0
  E₁ (b₁ p) v.1 = 0 → E₁ v.1 v.1 = E₁ (a₁ p) (a₁ p) →
  E₂ (b₂ p) v.2 = 0 → E₂ v.2 v.2 = E₂ (a₂ p) (a₂ p) →
  0 < H p (a₁ p,-a₂ p) (a₁ p,-a₂ p) + H p v v

set_option maxHeartbeats 900000 in
private theorem eventually_strictPairTest
    {D : Type*} [TopologicalSpace D] {p₀ : D}
    (M₁ M₂ : D → (Mat dim)) (b₁ b₂ a₁ a₂ : D → (X dim)) (H : D → ((X dim) × (X dim)) → ((X dim) × (X dim)) → ℝ)
    (hM₁ : M₁ p₀ = 1) (hM₂ : M₂ p₀ = 1)
    (hcM₁ : ∀ i j, ContinuousAt (fun p => M₁ p i j) p₀)
    (hcM₂ : ∀ i j, ContinuousAt (fun p => M₂ p i j) p₀)
    (hb₁ : ContinuousAt b₁ p₀) (hb₂ : ContinuousAt b₂ p₀)
    (ha₁ : ContinuousAt a₁ p₀) (ha₂ : ContinuousAt a₂ p₀)
    (hH : ∀ v w : (X dim) × (X dim), ContinuousAt (fun q : D × ((X dim) × (X dim)) × ((X dim) × (X dim)) =>
      H q.1 q.2.1 q.2.2) (p₀,v,w))
    (htest : ∀ v, strictPairTest M₁ M₂ b₁ b₂ a₁ a₂ H p₀ v) :
    ∀ᶠ p in 𝓝 p₀, ∀ v, strictPairTest M₁ M₂ b₁ b₂ a₁ a₂ H p v := by
  let E₁ (p : D) (v w : (X dim)) := metricPair (fun _ => M₁ p) 0 v w
  let E₂ (p : D) (v w : (X dim)) := metricPair (fun _ => M₂ p) 0 v w
  let A (p : D) := (a₁ p,-a₂ p)
  have hA : ContinuousAt A p₀ := ha₁.prodMk ha₂.neg
  let C := max (E₁ p₀ (a₁ p₀) (a₁ p₀)) (E₂ p₀ (a₂ p₀) (a₂ p₀)) + 1
  have hC₁ : E₁ p₀ (a₁ p₀) (a₁ p₀) < C := lt_of_le_of_lt (le_max_left _ _) (lt_add_of_pos_right _ one_pos)
  have hC₂ : E₂ p₀ (a₂ p₀) (a₂ p₀) < C := lt_of_le_of_lt (le_max_right _ _) (lt_add_of_pos_right _ one_pos)
  let K := closedBall (0 : (X dim)) (Real.sqrt (2 * C)) ×ˢ closedBall (0 : (X dim)) (Real.sqrt (2 * C))
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have bound {s : (X dim)} (hs : ‖s‖ ^ 2 / 2 ≤ C) : s ∈ closedBall (0 : (X dim)) (Real.sqrt (2 * C)) := by
    rw [mem_closedBall, dist_zero_right, ← Real.sqrt_sq (norm_nonneg s)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hgood : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ K, strictPairTest M₁ M₂ b₁ b₂ a₁ a₂ H p v := by
    apply hK.eventually_forall_of_forall_eventually
    intro v _
    change ∀ᶠ q : D × ((X dim) × (X dim)) in 𝓝 (p₀,v), strictPairTest M₁ M₂ b₁ b₂ a₁ a₂ H q.1 q.2
    have cE₁ {u w : D × ((X dim) × (X dim)) → (X dim)} (hu : ContinuousAt u (p₀,v))
        (hw : ContinuousAt w (p₀,v)) :
        ContinuousAt (fun q => E₁ q.1 (u q) (w q)) (p₀,v) :=
      continuousAt_metricPair_of_entries (p := (p₀,v)) (M := fun q : D × ((X dim) × (X dim)) => M₁ q.1) (v := u) (w := w)
        (fun i j => by
          change ContinuousAt ((fun p => M₁ p i j) ∘ Prod.fst) (p₀,v)
          exact (hcM₁ i j).comp continuous_fst.continuousAt) hu hw
    have cE₂ {u w : D × ((X dim) × (X dim)) → (X dim)} (hu : ContinuousAt u (p₀,v))
        (hw : ContinuousAt w (p₀,v)) :
        ContinuousAt (fun q => E₂ q.1 (u q) (w q)) (p₀,v) :=
      continuousAt_metricPair_of_entries (p := (p₀,v)) (M := fun q : D × ((X dim) × (X dim)) => M₂ q.1) (v := u) (w := w)
        (fun i j => by
          change ContinuousAt ((fun p => M₂ p i j) ∘ Prod.fst) (p₀,v)
          exact (hcM₂ i j).comp continuous_fst.continuousAt) hu hw
    have ca : ContinuousAt (fun q : D × ((X dim) × (X dim)) => A q.1) (p₀,v) :=
      hA.comp (continuous_fst.continuousAt : ContinuousAt Prod.fst (p₀,v))
    let N (q : D × ((X dim) × (X dim))) := (q.1,A q.1,A q.1)
    let V (q : D × ((X dim) × (X dim))) := (q.1,q.2,q.2)
    have cN : ContinuousAt N (p₀,v) := continuous_fst.continuousAt.prodMk (ca.prodMk ca)
    have cV : ContinuousAt V (p₀,v) :=
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_snd)).continuousAt
    let eval (q : D × ((X dim) × (X dim)) × ((X dim) × (X dim))) := H q.1 q.2.1 q.2.2
    have ceN : ContinuousAt eval (N (p₀,v)) := hH (A p₀) (A p₀)
    have ceV : ContinuousAt eval (V (p₀,v)) := hH v v
    have cp := (ceN.comp cN).add (ceV.comp cV)
    have c1 := cE₁ (hb₁.comp continuous_fst.continuousAt) continuous_snd.fst.continuousAt
    have c2 := cE₁ continuous_snd.fst.continuousAt continuous_snd.fst.continuousAt
    have c3 := cE₂ (hb₂.comp continuous_fst.continuousAt) continuous_snd.snd.continuousAt
    have c4 := cE₂ continuous_snd.snd.continuousAt continuous_snd.snd.continuousAt
    have ca₁' := ha₁.comp (continuous_fst.continuousAt : ContinuousAt Prod.fst (p₀,v))
    have ca₂' := ha₂.comp (continuous_fst.continuousAt : ContinuousAt Prod.fst (p₀,v))
    by_cases e1 : E₁ p₀ (b₁ p₀) v.1 = 0
    · by_cases e2 : E₁ p₀ v.1 v.1 = E₁ p₀ (a₁ p₀) (a₁ p₀)
      · by_cases e3 : E₂ p₀ (b₂ p₀) v.2 = 0
        · by_cases e4 : E₂ p₀ v.2 v.2 = E₂ p₀ (a₂ p₀) (a₂ p₀)
          · have he : ∀ᶠ q : D × ((X dim) × (X dim)) in 𝓝 (p₀,v),
                0 < H q.1 (A q.1) (A q.1) + H q.1 q.2 q.2 :=
              cp.preimage_mem_nhds (Ioi_mem_nhds (htest v e1 e2 e3 e4))
            exact he.mono (fun _ h _ _ _ _ => h)
          · exact ((c4.sub (cE₂ ca₂' ca₂')).eventually_ne (sub_ne_zero.mpr e4)).mono
              (fun _ h _ _ _ he => (h (sub_eq_zero.mpr he)).elim)
        · exact (c3.eventually_ne e3).mono (fun _ h _ _ he _ => (h he).elim)
      · exact ((c2.sub (cE₁ ca₁' ca₁')).eventually_ne (sub_ne_zero.mpr e2)).mono
          (fun _ h _ he _ _ => (h (sub_eq_zero.mpr he)).elim)
    · exact (c1.eventually_ne e1).mono (fun _ h he _ _ _ => (h he).elim)
  have hB₁ := eventually_metricPair_lower_of_identity hcM₁ hM₁
  have hB₂ := eventually_metricPair_lower_of_identity hcM₂ hM₂
  have hE₁ := (continuousAt_metricPair_of_entries hcM₁ ha₁ ha₁).preimage_mem_nhds (Iio_mem_nhds hC₁)
  have hE₂ := (continuousAt_metricPair_of_entries hcM₂ ha₂ ha₂).preimage_mem_nhds (Iio_mem_nhds hC₂)
  filter_upwards [hgood, hB₁, hB₂, hE₁, hE₂] with p hgood hB₁ hB₂ hE₁ hE₂ v
  intro hv hvn hw hwn
  have hvK := bound ((hB₁ v.1).trans (hvn.trans_le (le_of_lt hE₁)))
  have hwK := bound ((hB₂ v.2).trans (hwn.trans_le (le_of_lt hE₂)))
  exact hgood v ⟨hvK,hwK⟩ hv hvn hw hwn

set_option maxHeartbeats 1200000 in
/-- The strict test persists near identity metric data when the actual partial
covectors, metric gradients, and covariant Hessian vary continuously. -/
theorem eventually_productStrictHessianAt
    {D : Type*} [TopologicalSpace D] {p₀ : D}
    (g₁ g₂ : D → (MetricField dim)) (ρ : D → (X dim) × (X dim) → ℝ) (z : D → (X dim) × (X dim))
    (h₀ : ProductStrictHessianAt (g₁ p₀) (g₂ p₀) (ρ p₀) (z p₀))
    (hM₁ : g₁ p₀ (z p₀).1 = 1) (hM₂ : g₂ p₀ (z p₀).2 = 1)
    (hcM₁ : ∀ i j, ContinuousAt (fun p => g₁ p (z p).1 i j) p₀)
    (hcM₂ : ∀ i j, ContinuousAt (fun p => g₂ p (z p).2 i j) p₀)
    (hd₁ : ∀ i, ContinuousAt (fun p => coordDeriv i (fun x => ρ p (x,(z p).2)) (z p).1) p₀)
    (hd₂ : ∀ i, ContinuousAt (fun p => coordDeriv i (fun y => ρ p ((z p).1,y)) (z p).2) p₀)
    (hb₁ : ContinuousAt (fun p => chartMetricGradient (g₁ p) (fun x => ρ p (x,(z p).2)) (z p).1) p₀)
    (hb₂ : ContinuousAt (fun p => chartMetricGradient (g₂ p) (fun y => ρ p ((z p).1,y)) (z p).2) p₀)
    (hP₁ : ∀ᶠ p in 𝓝 p₀, (g₁ p (z p).1).PosDef)
    (hP₂ : ∀ᶠ p in 𝓝 p₀, (g₂ p (z p).2).PosDef)
    (hH : ∀ v w : (X dim) × (X dim), ContinuousAt (fun q : D × ((X dim) × (X dim)) × ((X dim) × (X dim)) =>
      productMetricHessian (g₁ q.1) (g₂ q.1) (ρ q.1) (z q.1) q.2.1 q.2.2) (p₀,v,w)) :
    ∀ᶠ p in 𝓝 p₀, ProductStrictHessianAt (g₁ p) (g₂ p) (ρ p) (z p) := by
  let M₁ (p : D) := g₁ p (z p).1
  let M₂ (p : D) := g₂ p (z p).2
  let E₁ (p : D) (v w : (X dim)) := metricPair (fun _ => M₁ p) 0 v w
  let E₂ (p : D) (v w : (X dim)) := metricPair (fun _ => M₂ p) 0 v w
  let f₁ (p : D) (x : (X dim)) := ρ p (x,(z p).2)
  let f₂ (p : D) (y : (X dim)) := ρ p ((z p).1,y)
  let d₁ (p : D) (i : (I dim)) := coordDeriv i (f₁ p) (z p).1
  let d₂ (p : D) (i : (I dim)) := coordDeriv i (f₂ p) (z p).2
  let b₁ (p : D) := chartMetricGradient (g₁ p) (f₁ p) (z p).1
  let b₂ (p : D) := chartMetricGradient (g₂ p) (f₂ p) (z p).2
  let n₁ (p : D) := E₁ p (b₁ p) (b₁ p)
  let n₂ (p : D) := E₂ p (b₂ p) (b₂ p)
  let a₁ (p : D) : (X dim) := (n₁ p)⁻¹ • b₁ p
  let a₂ (p : D) : (X dim) := (n₂ p)⁻¹ • b₂ p
  let A (p : D) := (a₁ p,-a₂ p)
  let H (p : D) := productMetricHessian (g₁ p) (g₂ p) (ρ p) (z p)
  have ncovs (p : D) (hp₁ : (M₁ p).PosDef) (hp₂ : (M₂ p).PosDef) :
      n₁ p = covectorSq (g₁ p) (f₁ p) (z p).1 ∧ n₂ p = covectorSq (g₂ p) (f₂ p) (z p).2 :=
    ⟨metricPair_gradient_self _ _ _ hp₁, metricPair_gradient_self _ _ _ hp₂⟩
  have hconvert (p : D) (hp₁ : (M₁ p).PosDef) (hp₂ : (M₂ p).PosDef) :
      ProductStrictHessianAt (g₁ p) (g₂ p) (ρ p) (z p) ↔
      d₁ p ≠ 0 ∧ d₂ p ≠ 0 ∧ ∀ v w : (X dim),
        E₁ p (b₁ p) v = 0 → E₁ p v v = E₁ p (a₁ p) (a₁ p) →
        E₂ p (b₂ p) w = 0 → E₂ p w w = E₂ p (a₂ p) (a₂ p) →
        0 < H p (A p) (A p) + H p (v,w) (v,w) := by
    simp only [ProductStrictHessianAt, A, a₁, a₂, (ncovs p hp₁ hp₂).1, (ncovs p hp₁ hp₂).2]
    rfl
  have hp₁ : (M₁ p₀).PosDef := by rw [show M₁ p₀ = 1 from hM₁]; exact Matrix.PosDef.one
  have hp₂ : (M₂ p₀).PosDef := by rw [show M₂ p₀ = 1 from hM₂]; exact Matrix.PosDef.one
  obtain ⟨h₁,h₂,htest⟩ := (hconvert p₀ hp₁ hp₂).mp h₀
  have pick {c : (I dim) → ℝ} (h : c ≠ 0) : ∃ i, c i ≠ 0 := by
    by_contra! he
    exact h (funext he)
  obtain ⟨i,hi⟩ := pick h₁
  obtain ⟨j,hj⟩ := pick h₂
  have ha₁ : ContinuousAt a₁ p₀ := by
    have hn : 0 < n₁ p₀ := by
      rw [(ncovs p₀ hp₁ hp₂).1]
      exact covectorSq_pos hp₁ hi
    exact ((continuousAt_metricPair_of_entries hcM₁ hb₁ hb₁).inv₀ hn.ne').smul hb₁
  have ha₂ : ContinuousAt a₂ p₀ := by
    have hn : 0 < n₂ p₀ := by
      rw [(ncovs p₀ hp₁ hp₂).2]
      exact covectorSq_pos hp₂ hj
    exact ((continuousAt_metricPair_of_entries hcM₂ hb₂ hb₂).inv₀ hn.ne').smul hb₂
  have hs := eventually_strictPairTest M₁ M₂ b₁ b₂ a₁ a₂ H hM₁ hM₂ hcM₁ hcM₂ hb₁ hb₂ ha₁ ha₂ hH
    (fun v => htest v.1 v.2)
  filter_upwards [hs, hP₁, hP₂, (hd₁ i).eventually_ne hi, (hd₂ j).eventually_ne hj]
    with p hs hp₁ hp₂ hni hnj
  exact (hconvert p hp₁ hp₂).mpr
    ⟨fun h => hni (congrFun h i), fun h => hnj (congrFun h j), fun v w => hs (v,w)⟩

end CalderonN
