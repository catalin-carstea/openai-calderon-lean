module

public import Proof.CalderonN.Chart

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

noncomputable section
open Set Filter
open scoped ContDiff BigOperators Topology

namespace CalderonN

variable {n : ℕ}

/- Port of the chart dilation from the 3D Theorem 3.1 release (55d37bfe).
Coordinate and Hessian regularity helpers retain their earlier proof bodies. -/

@[expose] def dilatedMetric (g : MetricField n) (lam : ℝ) (y : X n) : Mat n :=
  g (lam • y)

theorem hessian_sub {Ω : Set (X n)} (hΩ : IsOpen Ω) {u v : X n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω) {x : X n} (hx : x ∈ Ω) :
    hessian (fun z => u z - v z) x = hessian u x - hessian v x := by
  have hsub {f g : X n → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : I n) :
      coordDeriv i (fun z => f z - g z) x = coordDeriv i f x - coordDeriv i g x := by
    simp only [coordDeriv, fderiv_fun_sub hf hg, sub_apply]
  have hfirst (j : I n) : coordDeriv j (fun z => u z - v z) =ᶠ[𝓝 x]
      fun z => coordDeriv j u z - coordDeriv j v z := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    have hu' := (hu.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
    have hv' := (hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
    simp only [coordDeriv, fderiv_fun_sub hu' hv', sub_apply]
  have hs (j : I n) : DifferentiableAt ℝ (coordDeriv j u) x ∧ DifferentiableAt ℝ (coordDeriv j v) x :=
    ⟨((contDiffOn_coordDeriv hu hΩ j).differentiableOn (by simp)).differentiableAt
      (hΩ.mem_nhds hx),
     ((contDiffOn_coordDeriv hv hΩ j).differentiableOn (by simp)).differentiableAt
      (hΩ.mem_nhds hx)⟩
  ext i j
  change coordDeriv i (coordDeriv j (fun z => u z - v z)) x =
    coordDeriv i (coordDeriv j u) x - coordDeriv i (coordDeriv j v) x
  calc
    _ = coordDeriv i (fun z => coordDeriv j u z - coordDeriv j v z) x :=
      congrArg (fun L : X n →L[ℝ] ℝ => L (axis i)) (hfirst j).fderiv_eq
    _ = _ := hsub (hs j).1 (hs j).2 i

theorem coordDeriv_dilated {f : X n → ℝ} {lam : ℝ} {y : X n}
    (hf : DifferentiableAt ℝ f (lam • y)) (i : I n) :
    coordDeriv i (fun z => f (lam • z)) y = lam * coordDeriv i f (lam • y) := by
  let L : X n →L[ℝ] X n := lam • ContinuousLinearMap.id ℝ (X n)
  have h := hf.hasFDerivAt.comp y (L.hasFDerivAt (x := y))
  change fderiv ℝ (f ∘ (fun z : X n => lam • z)) y (axis i) = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, L, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul, coordDeriv]

theorem contDiffOn_dilation {f : X n → ℝ} {Ω : Set (X n)}
    (hf : ContDiffOn ℝ ∞ f Ω) (lam : ℝ) :
    ContDiffOn ℝ ∞ (fun z => f (lam • z)) {z | lam • z ∈ Ω} := by
  have hlin : ContDiff ℝ ∞ (fun z : X n => lam • z) :=
    (lam • ContinuousLinearMap.id ℝ (X n)).contDiff
  exact hf.comp hlin.contDiffOn (fun _ hz => hz)

theorem smoothMetric_dilated {Ω : Set (X n)} {g : MetricField n}
    (hg : SmoothMetric Ω g) (lam : ℝ) :
    SmoothMetric {z | lam • z ∈ Ω} (dilatedMetric g lam) :=
  ⟨fun i j => contDiffOn_dilation (hg.1 i j) lam, fun y hy => hg.2 (lam • y) hy⟩

theorem christoffel_dilated {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n}
    (hg : SmoothMetric Ω g) {lam : ℝ} {y : X n} (hy : lam • y ∈ Ω) (k i j : I n) :
    christoffel (dilatedMetric g lam) y k i j = lam * christoffel g (lam • y) k i j := by
  have hp (a b c : I n) : coordDeriv a (fun z => dilatedMetric g lam z b c) y =
      lam * coordDeriv a (fun z => g z b c) (lam • y) :=
    coordDeriv_dilated (((hg.1 b c).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)) a
  calc
    _ = (∑ l, lam * ((g (lam • y))⁻¹ k l *
      (coordDeriv i (fun z => g z l j) (lam • y) + coordDeriv j (fun z => g z i l) (lam • y) -
        coordDeriv l (fun z => g z i j) (lam • y)))) / 2 := by
      simp only [christoffel, hp]
      congr 1
      apply Finset.sum_congr rfl fun l _ => ?_
      change (g (lam • y))⁻¹ k l * _ = _
      ring
    _ = _ := by rw [← Finset.mul_sum, mul_div_assoc]; rfl

/-- Harmonic charts remain harmonic under a common spatial dilation. -/
theorem harmonicCoordinates_dilated {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n}
    (hg : SmoothMetric Ω g) (hchart : HarmonicCoordinates Ω g) (lam : ℝ) :
    HarmonicCoordinates {z | lam • z ∈ Ω} (dilatedMetric g lam) := by
  intro k
  refine ⟨(EuclideanSpace.proj k : X n →L[ℝ] ℝ).contDiff.contDiffOn, ?_⟩
  intro y hy
  rw [laplace_coordinate, neg_eq_zero]
  calc
    _ = lam * ∑ i, ∑ j, (g (lam • y))⁻¹ i j * christoffel g (lam • y) k i j := by
      simp only [christoffel_dilated hΩ hg hy, dilatedMetric, Finset.mul_sum]
      apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = 0 := by rw [contracted_christoffel_eq_zero hchart hy, mul_zero]

theorem hessian_dilated {Ω : Set (X n)} (hΩ : IsOpen Ω) {u : X n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {lam : ℝ} {y : X n} (hy : lam • y ∈ Ω) :
    hessian (fun z => u (lam • z)) y = (lam ^ 2) • hessian u (lam • y) := by
  let U : Set (X n) := {z | lam • z ∈ Ω}
  have hlin : Continuous (fun z : X n => lam • z) :=
    (lam • ContinuousLinearMap.id ℝ (X n)).continuous
  have hU : IsOpen U := hΩ.preimage hlin
  have hfirst (j : I n) : EqOn (coordDeriv j (fun z => u (lam • z)))
      (fun z => lam * coordDeriv j u (lam • z)) U := by
    intro z hz
    exact coordDeriv_dilated ((hu.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hz)) j
  ext i j
  let F := fun z : X n => coordDeriv j u (lam • z)
  have hF : DifferentiableAt ℝ F y := by
    have hsm := contDiffOn_dilation (contDiffOn_coordDeriv hu hΩ j) lam
    exact (hsm.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
  have hF' : DifferentiableAt ℝ (coordDeriv j u) (lam • y) :=
    ((contDiffOn_coordDeriv hu hΩ j).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
  have hmul : coordDeriv i (fun z => lam * F z) y = lam * coordDeriv i F y := by
    simp only [coordDeriv, fderiv_const_mul hF, smul_apply, smul_eq_mul]
  calc
    _ = coordDeriv i (fun z => lam * F z) y := eqOn_coordDeriv hU (hfirst j) i hy
    _ = lam * (lam * coordDeriv i (coordDeriv j u) (lam • y)) := by
      rw [hmul, coordDeriv_dilated hF' i]
    _ = _ := by simp only [pow_two, hessian, Matrix.smul_apply, smul_eq_mul, mul_assoc]

theorem harmonic_dilated {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n} (hg : SmoothMetric Ω g)
    (hchart : HarmonicCoordinates Ω g) {u : X n → ℝ} (hu : Harmonic Ω g u) (lam : ℝ) :
    Harmonic {z | lam • z ∈ Ω} (dilatedMetric g lam) (fun z => u (lam • z)) := by
  refine ⟨contDiffOn_dilation hu.1 lam, fun y hy => ?_⟩
  rw [laplace_eq_hessian_contraction (harmonicCoordinates_dilated hΩ hg hchart lam) hy,
    hessian_dilated hΩ hu.1 hy]
  have hsum : (∑ i, ∑ j, (g (lam • y))⁻¹ i j * hessian u (lam • y) i j) = 0 :=
    (laplace_eq_hessian_contraction hchart hy u).symm.trans (hu.2 (lam • y) hy)
  calc
    _ = lam ^ 2 * ∑ i, ∑ j, (g (lam • y))⁻¹ i j * hessian u (lam • y) i j := by
      simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, dilatedMetric]
      apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = 0 := by rw [hsum, mul_zero]

/-- The common affine part is subtracted before the quadratic rescaling. -/
@[expose] def renormalizedHarmonic (c : ℝ) (L : X n →L[ℝ] ℝ) (u : X n → ℝ) (lam : ℝ) (y : X n) : ℝ :=
  (lam ^ 2)⁻¹ * (u (lam • y) - (c + lam * L y))

theorem hessian_const_mul {U : Set (X n)} (hU : IsOpen U) {f : X n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {y : X n} (hy : y ∈ U) (a : ℝ) :
    hessian (fun z => a * f z) y = a • hessian f y := by
  have hderiv {F : X n → ℝ} {z : X n} (hF : DifferentiableAt ℝ F z) (i : I n) :
      coordDeriv i (fun x => a * F x) z = a * coordDeriv i F z := by
    simp only [coordDeriv, fderiv_const_mul hF, smul_apply, smul_eq_mul]
  ext i j
  have heq : EqOn (coordDeriv j (fun z => a * f z)) (fun z => a * coordDeriv j f z) U :=
    fun z hz => hderiv ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)) j
  have hDf := (contDiffOn_coordDeriv hf hU j).differentiableOn (by simp)
  change coordDeriv i (coordDeriv j (fun z => a * f z)) y =
    a * coordDeriv i (coordDeriv j f) y
  rw [eqOn_coordDeriv hU heq i hy, hderiv (hDf.differentiableAt (hU.mem_nhds hy)) i]

theorem laplace_const_mul {U : Set (X n)} (hU : IsOpen U) {f : X n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {y : X n} (hy : y ∈ U) (g : MetricField n) (a : ℝ) :
    laplace g (fun z => a * f z) y = a * laplace g f y := by
  have hder (k : I n) : coordDeriv k (fun z => a * f z) y = a * coordDeriv k f y := by
    have hd := (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
    simp only [coordDeriv, fderiv_const_mul hd, smul_apply, smul_eq_mul]
  change (∑ i, ∑ j, (g y)⁻¹ i j * (hessian (fun z => a * f z) y i j -
    ∑ k, christoffel g y k i j * coordDeriv k (fun z => a * f z) y)) = _
  rw [hessian_const_mul hU hf hy]
  simp only [laplace, Matrix.smul_apply, smul_eq_mul, hder, Finset.mul_sum]
  apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (∑ k, christoffel g y k i j * (a * coordDeriv k f y)) =
      a * ∑ k, christoffel g y k i j * coordDeriv k f y by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring]
  simp only [hessian]
  ring

theorem laplace_dilated {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n} (hg : SmoothMetric Ω g)
    {f : X n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) {lam : ℝ} {y : X n} (hy : lam • y ∈ Ω) :
    laplace (dilatedMetric g lam) (fun z => f (lam • z)) y = lam^2 * laplace g f (lam • y) := by
  have hder (i : I n) : coordDeriv i (fun z => f (lam • z)) y = lam * coordDeriv i f (lam • y) :=
    coordDeriv_dilated ((hf.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)) i
  change (∑ i, ∑ j, (g (lam • y))⁻¹ i j * (hessian (fun z => f (lam • z)) y i j -
    ∑ k, christoffel (dilatedMetric g lam) y k i j * coordDeriv k (fun z => f (lam • z)) y)) = _
  rw [hessian_dilated hΩ hf hy]
  simp only [laplace, Matrix.smul_apply, smul_eq_mul, christoffel_dilated hΩ hg hy, hder, Finset.mul_sum]
  apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (∑ k, lam * christoffel g (lam • y) k i j * (lam * coordDeriv k f (lam • y))) =
      lam^2 * ∑ k, christoffel g (lam • y) k i j * coordDeriv k f (lam • y) by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring]
  simp only [hessian]
  ring

private theorem hessian_affine (c lam : ℝ) (L : X n →L[ℝ] ℝ) (y : X n) :
    hessian (fun z => c + lam * L z) y = 0 := by
  have hconst (j : I n) : coordDeriv j (fun z => c + lam * L z) = fun _ => (lam • L) (axis j) := by
    funext z
    have h := ((lam • L).hasFDerivAt (x := z)).const_add c
    exact congrArg (fun M : X n →L[ℝ] ℝ => M (axis j)) h.fderiv
  ext i j
  change coordDeriv i (coordDeriv j (fun z => c + lam * L z)) y = 0
  rw [hconst j]
  simp [coordDeriv]

theorem contDiffOn_renormalizedHarmonic {Ω : Set (X n)} {u : X n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (c : ℝ) (L : X n →L[ℝ] ℝ) (lam : ℝ) :
    ContDiffOn ℝ ∞ (renormalizedHarmonic c L u lam) {y | lam • y ∈ Ω} :=
  contDiffOn_const.mul ((contDiffOn_dilation hu lam).sub
    (contDiffOn_const.add ((lam • L).contDiff.contDiffOn)))

theorem hessian_renormalizedHarmonic {Ω : Set (X n)} (hΩ : IsOpen Ω) {u : X n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (c : ℝ) (L : X n →L[ℝ] ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    {y : X n} (hy : lam • y ∈ Ω) :
    hessian (renormalizedHarmonic c L u lam) y = hessian u (lam • y) := by
  let U : Set (X n) := {z | lam • z ∈ Ω}
  have hU : IsOpen U := hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X n)).continuous)
  have hmain := contDiffOn_dilation hu lam
  have hlin : ContDiffOn ℝ ∞ (fun z : X n => c + lam * L z) U :=
    contDiffOn_const.add ((lam • L).contDiff.contDiffOn)
  unfold renormalizedHarmonic
  rw [hessian_const_mul hU (hmain.sub hlin) hy, hessian_sub hU hmain hlin hy,
    hessian_affine, sub_zero, hessian_dilated hΩ hu hy, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hlam),
    one_smul]

theorem harmonic_renormalizedHarmonic {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n}
    (hg : SmoothMetric Ω g) (hchart : HarmonicCoordinates Ω g)
    {u : X n → ℝ} (hu : Harmonic Ω g u) (c : ℝ) (L : X n →L[ℝ] ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    Harmonic {y | lam • y ∈ Ω} (dilatedMetric g lam) (renormalizedHarmonic c L u lam) := by
  refine ⟨contDiffOn_renormalizedHarmonic hu.1 c L lam, fun y hy => ?_⟩
  rw [laplace_eq_hessian_contraction (harmonicCoordinates_dilated hΩ hg hchart lam) hy,
    hessian_renormalizedHarmonic hΩ hu.1 c L hlam hy]
  exact (laplace_eq_hessian_contraction hchart hy u).symm.trans (hu.2 (lam • y) hy)

end CalderonN
