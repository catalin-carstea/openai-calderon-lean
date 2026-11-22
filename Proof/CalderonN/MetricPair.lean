module

public import Proof.CalderonN.Chart

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set Matrix Metric
open scoped BigOperators ContDiff

namespace CalderonN

variable {dim : ℕ}

theorem metricPair_eq_dotProduct (g : (MetricField dim)) (y u v : (X dim)) :
    metricPair g y u v = (fun i => u i) ⬝ᵥ (g y *ᵥ (fun i => v i)) := by
  simp only [metricPair, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem metricPair_comm {g : (MetricField dim)} {x : (X dim)} (hg : (g x).PosDef) (v w : (X dim)) :
    metricPair g x v w = metricPair g x w v := by
  rw [metricPair_eq_dotProduct, metricPair_eq_dotProduct, dotProduct_mulVec, ← mulVec_transpose,
    hg.isHermitian.isSymm.eq, dotProduct_comm]

theorem metricPair_pos_of_posDef {g : (MetricField dim)} {y : (X dim)} (hg : (g y).PosDef)
    {v : (X dim)} (hv : v ≠ 0) : 0 < metricPair g y v v := by
  rw [metricPair_eq_dotProduct]
  apply hg.dotProduct_mulVec_pos
  intro hz
  apply hv
  ext i
  exact congrFun hz i

theorem metricPair_nonneg_of_posDef {g : (MetricField dim)} {y : (X dim)} (hg : (g y).PosDef) (v : (X dim)) :
    0 ≤ metricPair g y v v := by
  by_cases h : v = 0
  · simp [h, metricPair]
  · exact (metricPair_pos_of_posDef hg h).le

theorem metricPair_smul_metric (g : (MetricField dim)) (c : (X dim) → ℝ) (y u v : (X dim)) :
    metricPair (fun z => c z • g z) y u v = c y * metricPair g y u v := by
  simp only [metricPair, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem metricPair_smul_same (g : (MetricField dim)) (y v : (X dim)) (c : ℝ) :
    metricPair g y (c • v) (c • v) = c ^ 2 * metricPair g y v v := by
  simp only [metricPair, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem metricPair_one (y v : (X dim)) :
    metricPair (fun _ => (1 : (Mat dim))) y v v = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [metricPair, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, pow_two]

/-- Uniform comparison with the coordinate Euclidean norm on a compact
family of positive definite matrices. -/
theorem exists_uniform_metric_comparison {P : Type*} [TopologicalSpace P]
    {K : Set P} (hK : IsCompact K) {g : P → (Mat dim)}
    (hg : ∀ i j, ContinuousOn (fun q => g q i j) K) (hpos : ∀ q ∈ K, (g q).PosDef) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ q ∈ K, ∀ v : (X dim),
      c * ‖v‖^2 ≤ metricPair (fun _ => g q) 0 v v ∧
        metricPair (fun _ => g q) 0 v v ≤ C * ‖v‖^2 := by
  let S := sphere (0 : (X dim)) 1
  let Q (p : P × (X dim)) := metricPair (fun _ => g p.1) 0 p.2 p.2
  have hc : ContinuousOn Q (K ×ˢ S) := by
    unfold Q metricPair
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    have hcoord (a : (I dim)) : Continuous (fun p : P × (X dim) => p.2 a) :=
      (EuclideanSpace.proj a : (X dim) →L[ℝ] ℝ).continuous.comp continuous_snd
    exact (((hg i j).comp continuous_fst.continuousOn (fun _ hp => hp.1)).mul
      (hcoord i).continuousOn).mul (hcoord j).continuousOn
  have hcK : IsCompact (K ×ˢ S) := hK.prod (isCompact_sphere _ _)
  obtain ⟨c, hcpos, hlo⟩ := hcK.exists_forall_le' hc (a := (0 : ℝ)) (by
    intro p hp
    apply metricPair_pos_of_posDef (hpos _ hp.1)
    have hn := mem_sphere_zero_iff_norm.mp hp.2
    exact norm_ne_zero_iff.mp (hn.trans_ne one_ne_zero))
  obtain ⟨C₀, hC₀⟩ := hcK.exists_bound_of_continuousOn hc
  let C := max C₀ 0
  refine ⟨c, C, hcpos, le_max_right _ _, fun q hq v => ?_⟩
  by_cases hv : v = 0
  · simp [hv, metricPair]
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hunit : ‖v‖⁻¹ • v ∈ S := by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm]
    let t : P × (X dim) := (q, ‖v‖⁻¹ • v)
    have ht : t ∈ K ×ˢ S := ⟨hq, hunit⟩
    have ha := hlo t ht
    have hb : Q t ≤ C := by
      calc
        Q t ≤ |Q t| := le_abs_self _
        _ ≤ C₀ := hC₀ t ht
        _ ≤ C := le_max_left _ _
    change c ≤ metricPair (fun _ => g q) 0 (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) at ha
    change metricPair (fun _ => g q) 0 (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) ≤ C at hb
    rw [metricPair_smul_same] at ha hb
    have ha' := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖v‖)
    have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
    have he : ‖v‖⁻¹ ^ 2 * metricPair (fun _ => g q) 0 v v * ‖v‖ ^ 2 =
        metricPair (fun _ => g q) 0 v v := by
      rw [mul_right_comm, ← mul_pow, inv_mul_cancel₀ hnorm, one_pow, one_mul]
    rw [he] at hb'
    exact ⟨ha'.trans_eq he, hb'⟩

end CalderonN
