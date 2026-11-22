module

public import Proof.CalderonN.MetricDivergence

import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The Wronskian as a chart vector density. Its outward flux gives the
Green transfer with the Riemannian volume and first metric. -/
@[expose] def wronskianFlux (g : (MetricField dim)) (u k : (X dim) → ℝ) (x : (X dim)) : (X dim) :=
  WithLp.toLp 2 fun i => k x * divergenceFlux g u x i - u x * divergenceFlux g k x i

theorem contDiffOn_wronskianFlux {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {u k : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hk : ContDiffOn ℝ ∞ k U) :
    ContDiffOn ℝ ∞ (wronskianFlux g u k) U := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  exact (hk.mul (contDiffOn_divergenceFlux hU hg hu i)).sub
    (hu.mul (contDiffOn_divergenceFlux hU hg hk i))

/-- The mixed first-derivative terms cancel by symmetry of the
volume-weighted inverse first metric. -/
theorem divergence_wronskianFlux {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {u k : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hk : ContDiffOn ℝ ∞ k U) {x : (X dim)} (hx : x ∈ U) :
    (∑ i, coordDeriv i (fun z => wronskianFlux g u k z i) x) =
      k x * (chartVolume g x * laplace g u x) - u x * (chartVolume g x * laplace g k x) := by
  let A (w : (X dim) → ℝ) (i : (I dim)) := fun z => divergenceFlux g w z i
  have hkd := (hk.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hud := (hu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hA {w : (X dim) → ℝ} (hw : ContDiffOn ℝ ∞ w U) (i : (I dim)) : DifferentiableAt ℝ (A w i) x :=
    ((contDiffOn_divergenceFlux hU hg hw i).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hDer (i : (I dim)) :
      coordDeriv i (fun z => wronskianFlux g u k z i) x =
        (k x * coordDeriv i (A u i) x + coordDeriv i k x * A u i x) -
        (u x * coordDeriv i (A k i) x + coordDeriv i u x * A k i x) := by
    change fderiv ℝ (fun z => k z * A u i z-u z * A k i z) x (axis i) = _
    have hKu : DifferentiableAt ℝ (fun z => k z * A u i z) x := hkd.mul (hA hu i)
    have hUk : DifferentiableAt ℝ (fun z => u z * A k i z) x := hud.mul (hA hk i)
    rw [fderiv_fun_sub hKu hUk,
      fderiv_fun_mul hkd (hA hu i),fderiv_fun_mul hud (hA hk i)]
    simp only [coordDeriv,sub_apply,add_apply,smul_apply,smul_eq_mul]
    ring
  have hSym : (∑ i, coordDeriv i k x * A u i x) = ∑ i, coordDeriv i u x * A k i x := by
    simp only [A,divergenceFlux,Finset.mul_sum]
    rw [Finset.sum_comm (f := fun i j => coordDeriv i k x * (divergenceCoeff g x i j * coordDeriv j u x))]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [divergenceCoeff_symm hg hx j i]
      ring
  simp_rw [hDer,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hSym]
  dsimp only [A]
  rw [← chartVolume_mul_laplace_eq_divergence hU hg hu hx,← chartVolume_mul_laplace_eq_divergence hU hg hk hx]
  ring

end CalderonN
