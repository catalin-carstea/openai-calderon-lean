module

public import Proof.CalderonN.NormalCoordinates
public import Mathlib.LinearAlgebra.Matrix.PosDef

import Proof.CalderonN.CompactBounds
import Proof.CalderonN.MetricPair
import Mathlib.Tactic

public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN.MovingSphere

variable {dim : ℕ} [NeZero dim]

set_option maxHeartbeats 500000 in
/-- An entire closed normal annulus stays a fixed positive chart distance
from its center, uniformly in the compact metric parameter. -/
theorem exists_uniform_normal_endpoint_separation
    {A : Set ℝ} (hA : IsCompact A) {Y Ω : Set (X dim)} (hY : IsCompact Y)
    {γ : ℝ → (MetricField dim)}
    (hγ : ∀ i j : (I dim), ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hp : ∀ lam ∈ A, ∀ y ∈ Y, (γ lam y).PosDef)
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {ρ r₀ : ℝ} (hr₀ : 0 < r₀)
    (hN : ∀ lam ∈ A, NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ)) :
    ∃ d > 0, ∀ lam ∈ A, ∀ y ∈ Y, ∀ v : (X dim),
      r₀^2 ≤ metricPair (γ lam) y v v → v ∈ disk (γ lam) y ρ →
      d ≤ ‖E lam (y,v)-y‖ := by
  obtain ⟨c,C,hc,hC,hMetric⟩ := exists_uniform_metric_comparison (hA.prod hY)
    (fun i j => (hγ i j).continuous.continuousOn) (fun z hz => hp z.1 hz.1 z.2 hz.2)
  let J (z : ℝ × (X dim) × (X dim)) := metricPair (γ z.1) z.2.1 z.2.2 z.2.2
  have hJ : Continuous J := by
    have hEntry (i j : (I dim)) : Continuous (fun z : ℝ × (X dim) × (X dim) => γ z.1 z.2.1 i j) :=
      (hγ i j).continuous.comp (continuous_fst.prodMk continuous_snd.fst)
    have hV (i : (I dim)) : Continuous (fun z : ℝ × (X dim) × (X dim) => z.2.2 i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_snd.snd
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hEntry i j).mul (hV i)).mul (hV j)
  let B := Real.sqrt (ρ^2/c)
  let K := (A ×ˢ (Y ×ˢ closedBall (0 : (X dim)) B)) ∩ {z | r₀^2 ≤ J z ∧ J z ≤ ρ^2}
  have hK : IsCompact K :=
    (hA.prod (hY.prod (isCompact_closedBall _ _))).inter_right
      ((isClosed_le continuous_const hJ).inter (isClosed_le hJ continuous_const))
  let F (z : ℝ × (X dim) × (X dim)) := ‖E z.1 z.2 - z.2.1‖
  have hF : Continuous F := (hE.continuous.sub continuous_snd.fst).norm
  obtain ⟨d,hd,hBound⟩ := Carleman.exists_pos_lower_of_compact hK hF.continuousOn (by
    intro z hz
    have hvDisk : z.2.2 ∈ disk (γ z.1) z.2.1 ρ := hz.2.2
    have h0Disk : (0 : (X dim)) ∈ disk (γ z.1) z.2.1 ρ := by simp [disk,metricPair,sq_nonneg]
    have hLoc := (hN z.1 hz.1.1).2 z.2.1 hz.1.2.1
    have hZero : E z.1 (z.2.1,0) = z.2.1 := by
      simpa only [zero_smul] using (hLoc.2.2 (0 : (X dim)) h0Disk).2.2.1
    apply norm_pos_iff.mpr
    intro he
    have hEzero : E z.1 z.2 = E z.1 (z.2.1,0) :=
      (sub_eq_zero.mp he).trans hZero.symm
    have hv := hLoc.2.1 hvDisk h0Disk hEzero
    have hR := hz.2.1
    change r₀^2 ≤ metricPair (γ z.1) z.2.1 z.2.2 z.2.2 at hR
    rw [hv] at hR
    simp [metricPair,(pow_pos hr₀ 2).not_ge] at hR)
  refine ⟨d,hd,fun lam hlam y hy v hlo hv => hBound (lam,y,v) ?_⟩
  refine ⟨⟨hlam,hy,?_⟩,hlo,hv⟩
  have huv : c*‖v‖^2 ≤ ρ^2 := ((hMetric (lam,y) ⟨hlam,hy⟩ v).1).trans hv
  have hs : ‖v‖^2 ≤ ρ^2/c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using huv)
  exact mem_closedBall_zero_iff.mpr (by
    simpa only [Real.sqrt_sq (norm_nonneg v)] using Real.sqrt_le_sqrt hs)

end CalderonN.MovingSphere
