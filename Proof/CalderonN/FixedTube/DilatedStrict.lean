module

public import Proof.CalderonN.FixedTube.CompactSweep
public import Proof.CalderonN.FixedTube.DilatedGeometry

import Proof.CalderonN.FixedTube.JetContinuity
import Proof.CalderonN.ProductHessian.Stability
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- Chart point of the product tube, parametrized by level, center and direction. -/
@[expose] def tubePoint (normal : I dim) (M e0 σ : ℝ) (q : ℝ × (X dim) × (X dim)) : (X dim) × (X dim) :=
  (q.2.1 + tubeRadius normal M e0 q.1 σ q.2.1 • q.2.2,q.2.1)

theorem continuous_tubePoint (M e0 σ : ℝ) (hσ : 0 ≤ σ) : Continuous (tubePoint normal M e0 σ) :=
  (tubeEndpoint_continuous (normal := normal) M e0 σ hσ).prodMk continuous_snd.fst

set_option maxHeartbeats 600000 in
/-- One dilation threshold preserves the actual strict product Hessian at
all points of a compact fixed-separation sweep. -/
theorem eventually_dilated_tube_strict {M e0 σ : ℝ} (hσ : 0 ≤ σ)
    {K : Set (ℝ × (X dim) × (X dim))} (hK : IsCompact K)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁0 : g₁ 0 = 1) (hg₂0 : g₂ 0 = 1)
    (ht : ∀ q ∈ K, 0 < tubeHeight normal M e0 q.2.1)
    (hstrict : ∀ q ∈ K, ProductStrictHessianAt (fun _ => (1 : (Mat dim))) (fun _ => (1 : (Mat dim)))
      (tubePhase normal M e0 q.1 σ) (tubePoint normal M e0 σ q)) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ q ∈ K,
      ProductStrictHessianAt (dilatedMetric g₁ lam) (dilatedMetric g₂ lam)
        (tubePhase normal M e0 q.1 σ) (tubePoint normal M e0 σ q) := by
  apply hK.eventually_forall_of_forall_eventually
  intro q hq
  let D := ℝ × (ℝ × (X dim) × (X dim))
  let p₀ : D := (0,q)
  let z (p : D) := tubePoint normal M e0 σ p.2
  let a (p : D) := p.2.1
  let ρ (p : D) := tubePhase normal M e0 (a p) σ
  let A₁ (p : D) := dilatedMetric g₁ p.1
  let A₂ (p : D) := dilatedMetric g₂ p.1
  have cZ : Continuous z := (continuous_tubePoint (normal := normal) M e0 σ hσ).comp continuous_snd
  have ca : Continuous a := continuous_snd.fst
  have h0₁ : A₁ p₀ = fun _ => (1 : (Mat dim)) := by
    funext x
    change g₁ ((0 : ℝ) • x) = _
    rwa [zero_smul]
  have h0₂ : A₂ p₀ = fun _ => (1 : (Mat dim)) := by
    funext x
    change g₂ ((0 : ℝ) • x) = _
    rwa [zero_smul]
  have hu : 0 < tubeHeight normal M e0 (z p₀).2 := ht q hq
  have hE := ((contDiff_tubeHeight (normal := normal) M e0).continuous.comp cZ.snd).continuousAt.preimage_mem_nhds
    (Ioi_mem_nhds hu)
  have d₁ (i : (I dim)) : ContinuousAt (fun p => coordDeriv i (fun x => ρ p (x,(z p).2)) (z p).1) p₀ := by
    have c := continuousAt_tubePhase_fderiv_apply (normal := normal) (σ := σ) (v := fun _ : D => (axis i,0))
      ca.continuousAt cZ.continuousAt continuousAt_const hu
    apply c.congr_of_eventuallyEq
    filter_upwards [hE] with p hp
    exact (slice_coordDeriv (ρ p) (z p) (tube_phase_fderiv_apply M e0 (a p) σ hp).1 i).1
  have d₂ (i : (I dim)) : ContinuousAt (fun p => coordDeriv i (fun y => ρ p ((z p).1,y)) (z p).2) p₀ := by
    have c := continuousAt_tubePhase_fderiv_apply (normal := normal) (σ := σ) (v := fun _ : D => (0,axis i))
      ca.continuousAt cZ.continuousAt continuousAt_const hu
    apply c.congr_of_eventuallyEq
    filter_upwards [hE] with p hp
    exact (slice_coordDeriv (ρ p) (z p) (tube_phase_fderiv_apply M e0 (a p) σ hp).1 i).2
  have hH (v w : (X dim) × (X dim)) : ContinuousAt
      (fun j : D × ((X dim) × (X dim)) × ((X dim) × (X dim)) =>
        productMetricHessian (A₁ j.1) (A₂ j.1) (ρ j.1) (z j.1) j.2.1 j.2.2) (p₀,v,w) := by
    let P := D × ((X dim) × (X dim)) × ((X dim) × (X dim))
    let u : P := (p₀,v,w)
    have cz : ContinuousAt (fun j : P => z j.1) u := (cZ.comp continuous_fst).continuousAt
    have cp : ContinuousAt (fun j : P => a j.1) u := (ca.comp continuous_fst).continuousAt
    have cl : ContinuousAt (fun j : P => j.1.1) u := continuous_fst.fst.continuousAt
    have cv : ContinuousAt (Prod.fst ∘ Prod.snd : P → (X dim) × (X dim)) u := continuous_snd.fst.continuousAt
    have cw : ContinuousAt (Prod.snd ∘ Prod.snd : P → (X dim) × (X dim)) u := continuous_snd.snd.continuousAt
    have c₁ := continuousAt_dilatedMetric_connection hg₁ cl cz.fst cv.fst cw.fst
    have c₂ := continuousAt_dilatedMetric_connection hg₂ cl cz.snd cv.snd cw.snd
    exact (continuousAt_tubePhase_second_apply (normal := normal) cp cz cv cw hu).sub
      (continuousAt_tubePhase_fderiv_apply (normal := normal) cp cz (c₁.prodMk c₂) hu)
  have hbase : ProductStrictHessianAt (A₁ p₀) (A₂ p₀) (ρ p₀) (z p₀) := by
    rw [h0₁,h0₂]
    exact hstrict q hq
  have hM₁ (i j : (I dim)) : ContinuousAt (fun p : D => A₁ p (z p).1 i j) p₀ :=
    (contDiff_dilatedMetric_entry hg₁ i j).continuous.continuousAt.comp
      (continuous_fst.prodMk cZ.fst).continuousAt
  have hM₂ (i j : (I dim)) : ContinuousAt (fun p : D => A₂ p (z p).2 i j) p₀ :=
    (contDiff_dilatedMetric_entry hg₂ i j).continuous.continuousAt.comp
      (continuous_fst.prodMk cZ.snd).continuousAt
  have hB₁ := continuousAt_dilatedMetric_gradient hg₁ continuous_fst.continuousAt cZ.fst.continuousAt d₁
  have hB₂ := continuousAt_dilatedMetric_gradient hg₂ continuous_fst.continuousAt cZ.snd.continuousAt d₂
  exact eventually_productStrictHessianAt A₁ A₂ ρ z hbase
    (congrFun h0₁ _) (congrFun h0₂ _) hM₁ hM₂ d₁ d₂ hB₁ hB₂
    (Eventually.of_forall fun p : D => hg₁.2 (p.1 • (z p).1) (mem_univ _))
    (Eventually.of_forall fun p : D => hg₂.2 (p.1 • (z p).2) (mem_univ _)) hH

/-- Parameters for a compact sweep can be chosen before the metric dilation. -/
theorem exists_compact_dilated_tube_strict {c0 η d B M : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hB : 0 ≤ B) (hM : B + 3 < M)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁0 : g₁ 0 = 1) (hg₂0 : g₂ 0 = 1) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < e0 ∧ e0 ≤ 1 ∧ M + B + B ^ 2 < T0 ∧
      1 < c0 * min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) * T0 ^ σ ∧
      ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ q : ℝ × (X dim) × (X dim),
        ‖q.2.2‖ = 1 → -B - 1 ≤ q.2.1 normal → tubeHeight normal M e0 q.2.1 ≤ T0 →
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ q.1 → q.1 ≤ 2 / c0 + 1 →
        c0 * ‖(tubePoint normal M e0 σ q).1 - q.2.1‖ ≤ min ((tubePoint normal M e0 σ q).1 normal) (q.2.1 normal) →
        ProductStrictHessianAt (dilatedMetric g₁ lam) (dilatedMetric g₂ lam)
          (tubePhase normal M e0 q.1 σ) (tubePoint normal M e0 σ q) := by
  obtain ⟨σ,T0,e0,hσ,hσ1,he0,he01,hcap,hseed,hK,hS⟩ := tube_native_strict_sweep_set (normal := normal) hc0 hη hη10 hc0η hd hB hM
  refine ⟨σ,T0,e0,hσ,hσ1,he0,he01,hcap,hseed,?_⟩
  have h := eventually_dilated_tube_strict (normal := normal) hσ.le hK hg₁ hg₂ hg₁0 hg₂0
    (fun q hq => zero_lt_one.trans_le (tube_base_height he0.le hM hq.2.1 hq.2.2.1).1) hS
  exact h.mono fun _ h q hw hy ht ha ha' hs => h q ⟨hw,hy,ht,ha,ha',hs⟩

end CalderonN.FixedTube
