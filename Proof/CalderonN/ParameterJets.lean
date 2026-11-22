module

public import Proof.CalderonN.Chart

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricCalculus

@[expose] public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ}

/-- A derivative in a spatial coordinate with the dilation parameter held fixed. -/
@[expose] def baseCoordDeriv (i : (I dim)) (F : ℝ × (X dim) → ℝ) (q : ℝ × (X dim)) : ℝ :=
  fderiv ℝ F q (0, axis i)

def baseChartPartial (a : I dim → ℕ) (F : ℝ × X dim → ℝ) : ℝ × X dim → ℝ :=
  (List.ofFn fun i : I dim => (baseCoordDeriv i)^[a i]).foldr (fun D u => D u) F

theorem contDiffOn_baseCoordDeriv {U : Set (ℝ × (X dim))} (hU : IsOpen U)
    {F : ℝ × (X dim) → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i : (I dim)) :
    ContDiffOn ℝ ∞ (baseCoordDeriv i F) U :=
  (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem contDiffOn_baseIterate {U : Set (ℝ × (X dim))} (hU : IsOpen U)
    {F : ℝ × (X dim) → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i : (I dim)) (n : ℕ) :
    ContDiffOn ℝ ∞ ((baseCoordDeriv i)^[n] F) U := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact contDiffOn_baseCoordDeriv hU ih i

theorem contDiffOn_baseChartPartial {U : Set (ℝ × X dim)} (hU : IsOpen U)
    {F : ℝ × X dim → ℝ} (hF : ContDiffOn ℝ ∞ F U) (a : I dim → ℕ) :
    ContDiffOn ℝ ∞ (baseChartPartial a F) U := by
  unfold baseChartPartial
  refine List.foldrRecOn (motive := fun u => ContDiffOn ℝ ∞ u U)
    (List.ofFn fun i : I dim => (baseCoordDeriv i)^[a i]) (fun D u => D u) hF ?_
  intro u hu d hd
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
  exact contDiffOn_baseIterate hU hu i (a i)

theorem baseCoordDeriv_eq {U : Set (ℝ × (X dim))} (hU : IsOpen U)
    {F : ℝ × (X dim) → ℝ} (hF : ContDiffOn ℝ ∞ F U) {lam : ℝ} {y : (X dim)}
    (hy : (lam, y) ∈ U) (i : (I dim)) :
    baseCoordDeriv i F (lam, y) = coordDeriv i (fun z => F (lam, z)) y := by
  let L : (X dim) →L[ℝ] ℝ × (X dim) := ContinuousLinearMap.inr ℝ ℝ (X dim)
  have hL : HasFDerivAt (fun z : (X dim) => (lam, z)) L y :=
    (hasFDerivAt_const lam y).prodMk (hasFDerivAt_id y)
  have hF' := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
  have hc := hF'.hasFDerivAt.comp y hL
  unfold coordDeriv baseCoordDeriv
  change fderiv ℝ F (lam, y) (0, axis i) =
    fderiv ℝ (F ∘ (fun z : (X dim) => (lam, z))) y (axis i)
  rw [hc.fderiv]
  rfl

private theorem baseIterate_eqOn_slice {U : Set (ℝ × (X dim))} (hU : IsOpen U)
    {F : ℝ × (X dim) → ℝ} (hF : ContDiffOn ℝ ∞ F U) {lam : ℝ} {f : (X dim) → ℝ}
    (heq : EqOn (fun z => F (lam, z)) f {z | (lam, z) ∈ U}) (i : (I dim)) (n : ℕ) :
    EqOn (fun z => ((baseCoordDeriv i)^[n] F) (lam, z))
      ((coordDeriv i)^[n] f) {z | (lam, z) ∈ U} := by
  have hs : IsOpen {z : (X dim) | (lam, z) ∈ U} := hU.preimage (continuous_const.prodMk continuous_id)
  induction n with
  | zero => exact heq
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    intro y hy
    calc
      _ = coordDeriv i (fun z => ((baseCoordDeriv i)^[n] F) (lam, z)) y :=
        baseCoordDeriv_eq hU (contDiffOn_baseIterate hU hF i n) hy i
      _ = _ := eqOn_coordDeriv hs ih i hy

/-- The joint formula differentiates in the spatial variable alone and
agrees with the released coordinate partials on each admissible slice. -/
theorem baseChartPartial_eq_slice {U : Set (ℝ × X dim)} (hU : IsOpen U)
    {F : ℝ × X dim → ℝ} (hF : ContDiffOn ℝ ∞ F U) {lam : ℝ} {y : X dim}
    (hy : (lam, y) ∈ U) (a : I dim → ℕ) :
    baseChartPartial a F (lam, y) = chartPartial a (fun z => F (lam, z)) y := by
  let Q := List.ofFn (fun i : I dim => i)
  have hf (s : List (I dim)) :
      ContDiffOn ℝ ∞ (s.foldr (fun i u => (baseCoordDeriv i)^[a i] u) F) U ∧
        EqOn (fun z => s.foldr (fun i u => (baseCoordDeriv i)^[a i] u) F (lam,z))
          (s.foldr (fun i u => (coordDeriv i)^[a i] u) (fun z => F (lam,z)))
          {z | (lam,z) ∈ U} := by
    induction s with
    | nil => exact ⟨hF,fun _ _ => rfl⟩
    | cons i s ih =>
      simp only [List.foldr_cons]
      exact ⟨contDiffOn_baseIterate hU ih.1 i (a i), baseIterate_eqOn_slice hU ih.1 ih.2 i (a i)⟩
  have hbase : (List.ofFn fun i : I dim => (baseCoordDeriv i)^[a i]) =
      Q.map (fun i : I dim => (baseCoordDeriv i)^[a i]) := by simp [Q, Function.comp_def]
  have hchart : (List.ofFn fun i : I dim => (coordDeriv (E := ℝ) i)^[a i]) =
      Q.map (fun i : I dim => (coordDeriv i)^[a i]) := by simp [Q, Function.comp_def]
  rw [baseChartPartial, chartPartial, hbase, hchart, List.foldr_map, List.foldr_map]
  exact (hf Q).2 hy

end CalderonN
