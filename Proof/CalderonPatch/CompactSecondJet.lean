module

public import Proof.CalderonPatch.HarmonicJets
public import Proof.CalderonPatch.HomogeneousTests
public import Proof.CalderonN.Hessian

import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Filter Matrix Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace CalderonPatch

open CalderonN (I X Mat axis coordDeriv hessian chartDerivativeWord)

variable {n : ℕ} [NeZero n]

/-- A scalar second jet in a chosen open chart. -/
def smoothSecondJet {U : Set (X n)} (hU : IsOpen U) {x : X n} (hx : x ∈ U)
    (f : X n → ℝ) (hf : ContDiffOn ℝ ∞ f U) : ScalarSecondJet n :=
  secondJet f x (CalderonN.hessian_transpose hU hf hx)

theorem smoothSecondJet_laplace {U : Set (X n)} (hU : IsOpen U) {x : X n} (hx : x ∈ U)
    (γ : CalderonN.MetricField n) (f : X n → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
    laplaceOnSecondJet γ x (smoothSecondJet hU hx f hf) = CalderonN.laplace γ f x :=
  laplaceOnSecondJet_secondJet γ x _ _

theorem smoothSecondJet_congr_germ {U V : Set (X n)} (hU : IsOpen U) (hV : IsOpen V)
    {x : X n} (hx : x ∈ U) (hxV : x ∈ V) {f g : X n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) (h : f =ᶠ[𝓝 x] g) :
    smoothSecondJet hU hx f hf = smoothSecondJet hV hxV g hg := by
  refine Prod.ext h.eq_of_nhds (Prod.ext (funext fun i => ?_) (Subtype.ext (Matrix.ext fun i j => ?_)))
  · exact (chartDerivativeWord_congr_germ [i] h).eq_of_nhds
  · exact (chartDerivativeWord_congr_germ [i,j] h).eq_of_nhds

/-- A smooth compactly supported chart test evaluated as a second jet. -/
def compactSecondJet {K : Compacts (X n)} (f : 𝓓_{K}(X n, ℝ)) : ScalarSecondJet n :=
  smoothSecondJet isOpen_univ (mem_univ (0 : X n)) f f.contDiff.contDiffOn

private def covectorOfComponents (v : I n → ℝ) : X n →L[ℝ] ℝ :=
  ∑ i : I n, v i • EuclideanSpace.proj i

private theorem covectorOfComponents_axis (v : I n → ℝ) (i : I n) :
    covectorOfComponents v (axis i) = v i := by
  simp only [covectorOfComponents, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  change (∑ j : I n, v j * (axis i) j) = v i
  simp [axis, PiLp.single_apply, mul_ite, Finset.sum_ite_eq']

private def chartBilinear (H : Mat n) : X n →L[ℝ] X n →L[ℝ] ℝ :=
  ∑ i : I n, (EuclideanSpace.proj i).smulRight (covectorOfComponents (H i))

private theorem chartBilinear_axes (H : Mat n) (i j : I n) : chartBilinear H (axis i) (axis j) = H i j := by
  simp only [chartBilinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, covectorOfComponents_axis]
  change (∑ k : I n, (axis i) k * H k j) = H i j
  simp [axis, PiLp.single_apply, ite_mul, Finset.sum_ite_eq']

/-- Cutoff quadratic polynomials realize every scalar second jet by an
actual test function supported in the prescribed compact neighborhood. -/
theorem surjective_compactSecondJet {K : Compacts (X n)} (hK : (K : Set (X n)) ∈ 𝓝 0) :
    Function.Surjective (compactSecondJet (K := K)) := by
  intro v
  let B := chartBilinear v.2.2.val
  let l := covectorOfComponents v.2.1
  let p : X n → ℝ := fun x => v.1 + (l x + (1 / 2 : ℝ) * B x x)
  have hp : ContDiff ℝ ∞ p := contDiff_const.add
    (l.contDiff.add (contDiff_const.mul (B.contDiff.clm_apply contDiff_id)))
  let D (j : I n) := (1 / 2 : ℝ) • ((ContinuousLinearMap.apply ℝ ℝ (axis j)).comp B + B (axis j))
  have hDiff (j : I n) : coordDeriv j p = fun x => v.2.1 j + D j x := by
    funext x
    change fderiv ℝ (fun y => v.1 + (l y + (1 / 2 : ℝ) * B y y)) x (axis j) = _
    rw [fderiv_const_add, fderiv_fun_add l.differentiableAt (by fun_prop), l.fderiv,
      fderiv_const_mul (by fun_prop), fderiv_clm_apply (u := fun y => y) B.differentiableAt differentiableAt_id,
      B.fderiv, fderiv_fun_id]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      D, ContinuousLinearMap.apply_apply, l, covectorOfComponents_axis, add_comm]
  have hH (i j : I n) : hessian p 0 i j = v.2.2.val i j := by
    change fderiv ℝ (coordDeriv j p) 0 (axis i) = _
    rw [hDiff, fderiv_const_add, (D j).fderiv]
    simp only [D, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, B, chartBilinear_axes]
    have hsym := congrArg (fun H : Mat n => H i j) v.2.2.property
    change v.2.2.val j i = v.2.2.val i j at hsym
    rw [hsym]
    ring
  obtain ⟨f, hf⟩ := exists_compactTest_germ hK hp
  refine ⟨f, ?_⟩
  rw [compactSecondJet, smoothSecondJet_congr_germ isOpen_univ isOpen_univ (mem_univ _) (mem_univ _)
    f.contDiff.contDiffOn hp.contDiffOn hf]
  refine Prod.ext (by change p 0 = v.1; simp [p]) (Prod.ext (funext fun i => ?_)
    (Subtype.ext (Matrix.ext hH)))
  change coordDeriv i p 0 = v.2.1 i
  rw [hDiff]
  simp

/-- Vanishing derivatives through order two force the second jet to vanish. -/
theorem compactSecondJet_eq_zero_of_flat {K : Compacts (X n)} (f : 𝓓_{K}(X n, ℝ))
    (hf : ∀ j ≤ 2, iteratedFDeriv ℝ j f 0 = 0) : compactSecondJet f = 0 := by
  have hWord {j : ℕ} (hj : j ≤ 2) (idx : Fin j → I n) : chartDerivativeWord (List.ofFn idx) f 0 = 0 := by
    rw [congrFun (CalderonN.chartDerivativeWord_ofFn j idx f.contDiff) 0, hf j hj]
    rfl
  refine Prod.ext ?_ (Prod.ext (funext fun i => ?_) (Subtype.ext (Matrix.ext fun i j => ?_)))
  · exact hWord (j := 0) (by decide) Fin.elim0
  · change chartDerivativeWord [i] f 0 = 0
    simpa only [List.ofFn_succ, List.ofFn_zero] using hWord (j := 1) (by decide) (fun _ => i)
  · change chartDerivativeWord [i,j] f 0 = 0
    simpa only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one]
      using hWord (j := 2) (by decide) ![i,j]

end CalderonPatch
