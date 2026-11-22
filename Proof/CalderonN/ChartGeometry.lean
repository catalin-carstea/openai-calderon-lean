module

public import Proof.CalderonN.Chart

import Mathlib.Analysis.Calculus.LocalExtr.Basic

public section

/- Port of the 3D Theorem 3.1 release (check 55d37bfe), same module name
   under Proof.LocalMetricExtension. -/

open Set Filter
open scoped ContDiff Topology BigOperators

namespace CalderonN

variable {n : ℕ}

/-- The regular level condition makes the matching side accumulate at zero. -/
theorem ContainsSmoothSide.mem_closure {Ω W : Set (X n)}
    (hside : ContainsSmoothSide Ω W) : (0 : X n) ∈ closure W := by
  obtain ⟨V, s, hV, hzero, _, _, hs0, hderiv, hside⟩ := hside
  by_contra hout
  rw [mem_closure_iff_frequently, not_frequently] at hout
  have hmin : IsLocalMin s 0 := by
    filter_upwards [hV.mem_nhds hzero, hout] with x hx hnot
    rw [hs0]
    exact le_of_not_gt fun hneg => hnot (hside ⟨hx, hneg⟩)
  exact hderiv hmin.fderiv_eq_zero

/-- Value equality at the contact point follows from continuity from the known side. -/
theorem eq_at_origin_of_eqOn_side {F : Type*} [TopologicalSpace F] [T2Space F]
    {Ω W : Set (X n)} (hside : ContainsSmoothSide Ω W) {f g : X n → F}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0) (heq : EqOn f g W) :
    f 0 = g 0 := by
  let : (𝓝[W] (0 : X n)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hside.mem_closure
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.tendsto.mono_left nhdsWithin_le_nhds) (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_mem_nhdsWithin.mono heq)

theorem eqOn_coordDeriv {V : Set (X n)} (hV : IsOpen V) {f g : X n → ℝ} (heq : EqOn f g V)
    (i : I n) : EqOn (coordDeriv i f) (coordDeriv i g) V := by
  intro x hx
  have hfg : f =ᶠ[𝓝 x] g := Filter.mem_of_superset (hV.mem_nhds hx) heq
  exact congrArg (fun L : X n →L[ℝ] ℝ => L (axis i)) hfg.fderiv_eq

theorem eqOn_iterate_coordDeriv {V : Set (X n)} (hV : IsOpen V) {f g : X n → ℝ}
    (heq : EqOn f g V) (i : I n) (j : ℕ) :
    EqOn ((coordDeriv i)^[j] f) ((coordDeriv i)^[j] g) V := by
  induction j with
  | zero => exact heq
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact eqOn_coordDeriv hV ih i

theorem chartPartial_eq_zero_of_eqOn_zero {V : Set (X n)} (hV : IsOpen V) {f : X n → ℝ}
    (heq : EqOn f 0 V) (a : I n → ℕ) : EqOn (chartPartial a f) 0 V := by
  have hz (i : I n) (j : ℕ) : (coordDeriv i)^[j] (0 : X n → ℝ) = 0 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      ext x
      simp [coordDeriv]
  unfold chartPartial
  refine List.foldrRecOn (motive := fun u => EqOn u 0 V)
    (List.ofFn fun i : I n => (coordDeriv i)^[a i]) (fun D u => D u) heq ?_
  intro u hu d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  simpa only [hz] using eqOn_iterate_coordDeriv hV hu i (a i)

/-- Match the first jets before subtracting a common affine function. -/
theorem fderiv_eq_at_origin_of_eqOn_side {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hside : ContainsSmoothSide Ω W)
    {f g : X n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) (heq : EqOn f g W) :
    fderiv ℝ f 0 = fderiv ℝ g 0 := by
  have hzero : (0 : X n) ∈ Ω := by
    obtain ⟨_, _, _, hx, hsub, _⟩ := hside
    exact hsub hx
  apply eq_at_origin_of_eqOn_side hside
  · exact ((hf.fderiv_of_isOpen hΩ (m := 0) (by simp)).continuousOn.continuousAt
      (hΩ.mem_nhds hzero))
  · exact ((hg.fderiv_of_isOpen hΩ (m := 0) (by simp)).continuousOn.continuousAt
      (hΩ.mem_nhds hzero))
  · intro x hx
    have hfg : f =ᶠ[𝓝 x] g := Filter.mem_of_superset (hW.mem_nhds hx) heq
    exact Filter.EventuallyEq.fderiv_eq hfg

theorem coordDeriv_coordinate (i j : I n) (x : X n) :
    coordDeriv i (fun y : X n => y j) x = if i = j then 1 else 0 := by
  change (fderiv ℝ (EuclideanSpace.proj j : X n →L[ℝ] ℝ) x) (axis i) = _
  rw [ContinuousLinearMap.fderiv]
  change (axis i) j = _
  simp [axis, PiLp.single_apply, eq_comm]

private theorem coordDeriv_const (i : I n) (c : ℝ) (x : X n) :
    coordDeriv i (fun _ => c) x = 0 := by
  simp [coordDeriv]

theorem laplace_coordinate (g : MetricField n) (x : X n) (k : I n) :
    laplace g (fun y => y k) x = -(∑ i, ∑ j, (g x)⁻¹ i j * christoffel g x k i j) := by
  have hcoord (j : I n) : coordDeriv j (fun y : X n => y k) =
      fun _ => if j = k then 1 else 0 := funext (coordDeriv_coordinate j k)
  simp only [laplace, hcoord, coordDeriv_const, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_sub, mul_neg, Finset.sum_neg_distrib]

theorem contracted_christoffel_eq_zero {Ω : Set (X n)} {g : MetricField n}
    (hchart : HarmonicCoordinates Ω g) {x : X n} (hx : x ∈ Ω) (k : I n) :
    ∑ i, ∑ j, (g x)⁻¹ i j * christoffel g x k i j = 0 := by
  have h := (hchart k).2 x hx
  rw [laplace_coordinate, neg_eq_zero] at h
  exact h

/-- In common harmonic coordinates the first-order Christoffel term vanishes. -/
theorem laplace_eq_hessian_contraction {Ω : Set (X n)} {g : MetricField n}
    (hchart : HarmonicCoordinates Ω g) {x : X n} (hx : x ∈ Ω) (u : X n → ℝ) :
    laplace g u x = ∑ i, ∑ j, (g x)⁻¹ i j * hessian u x i j := by
  have hdrift : (∑ i, ∑ j, (g x)⁻¹ i j *
      ∑ k, christoffel g x k i j * coordDeriv k u x) = 0 := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    calc
      _ = ∑ i, ∑ k, ∑ j, (g x)⁻¹ i j * christoffel g x k i j * coordDeriv k u x :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (g x)⁻¹ i j * christoffel g x k i j * coordDeriv k u x :=
        Finset.sum_comm
      _ = 0 := by
        simp_rw [← Finset.sum_mul, contracted_christoffel_eq_zero hchart hx, zero_mul,
          Finset.sum_const_zero]
  simp only [laplace, hessian, mul_sub, Finset.sum_sub_distrib, hdrift, sub_zero]

end CalderonN
