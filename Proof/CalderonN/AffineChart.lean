module

public import Proof.CalderonN.MetricDivergence
public import Proof.CalderonN.DilationHarmonic
import Mathlib.Tactic

public section

/- Affine metric and Laplace changes of variables from the 3D Theorem 3.1
   release (55d37bfe), with the same affine chart and normalization. -/
noncomputable section
open Set
open scoped ContDiff

namespace CalderonN
variable {n : ℕ}

@[expose] def affineChartMap (c : (X n)) (s : ℝ) (x : (X n)) : (X n) := c+s • x

/-- The translated and dilated coefficient field. The constant metric
factor from the homothety cancels in the equation with zero right side. -/
@[expose] def affineChartMetric (g : (MetricField n)) (p : (X n) × ℝ) : (MetricField n) :=
  fun x => g (affineChartMap p.1 p.2 x)

@[expose] def affineChartProduct (c : (X n)) (s : ℝ) (q : (X n) × (X n)) : (X n) × (X n) :=
  (affineChartMap c s q.1,affineChartMap c s q.2)

theorem contDiff_affineChartMap (c : (X n)) (s : ℝ) : ContDiff ℝ ∞ (affineChartMap c s) :=
  contDiff_const.add ((s • ContinuousLinearMap.id ℝ (X n)).contDiff)

theorem contDiff_affineChartProduct (c : (X n)) (s : ℝ) : ContDiff ℝ ∞ (affineChartProduct c s) :=
  ((contDiff_affineChartMap c s).comp contDiff_fst).prodMk
    ((contDiff_affineChartMap c s).comp contDiff_snd)

theorem affineChartMap_inverse (c : (X n)) {s : ℝ} (hs : s ≠ 0) (x : (X n)) :
    affineChartMap (-(s⁻¹ • c)) s⁻¹ (affineChartMap c s x) = x := by
  simp [affineChartMap,smul_add,smul_smul,inv_mul_cancel₀ hs]

theorem affineChartMap_inverse_right (c : (X n)) {s : ℝ} (hs : s ≠ 0) (x : (X n)) :
    affineChartMap c s (affineChartMap (-(s⁻¹ • c)) s⁻¹ x) = x := by
  simp [affineChartMap,smul_add,smul_smul,mul_inv_cancel₀ hs]

theorem affineChartProduct_inverse (c : (X n)) {s : ℝ} (hs : s ≠ 0) (q : (X n) × (X n)) :
    affineChartProduct (-(s⁻¹ • c)) s⁻¹ (affineChartProduct c s q) = q := by
  exact Prod.ext (affineChartMap_inverse c hs q.1) (affineChartMap_inverse c hs q.2)

theorem affineChartProduct_inverse_right (c : (X n)) {s : ℝ} (hs : s ≠ 0) (q : (X n) × (X n)) :
    affineChartProduct c s (affineChartProduct (-(s⁻¹ • c)) s⁻¹ q) = q := by
  exact Prod.ext (affineChartMap_inverse_right c hs q.1) (affineChartMap_inverse_right c hs q.2)

theorem smoothMetric_affineChartMetric {g : (MetricField n)} (hg : SmoothMetric univ g) (p : (X n) × ℝ) :
    SmoothMetric univ (affineChartMetric g p) :=
  ⟨fun i j => ((contDiffOn_univ.mp (hg.1 i j)).comp (contDiff_affineChartMap p.1 p.2)).contDiffOn,
    fun x _ => hg.2 (affineChartMap p.1 p.2 x) (mem_univ _)⟩

theorem contDiff_affineChartMetric_divergenceCoeff {g : (MetricField n)} (hg : SmoothMetric univ g)
    (i j : (I n)) :
    ContDiff ℝ ∞ (fun z : ((X n) × ℝ) × (X n) => divergenceCoeff (affineChartMetric g z.1) z.2 i j) :=
  (contDiffOn_univ.mp (contDiffOn_divergenceCoeff hg i j)).comp
    (contDiff_fst.fst.add (contDiff_fst.snd.smul contDiff_snd))

theorem affineChartMetric_zero {g : (MetricField n)} (hg₀ : g 0 = 1) :
    affineChartMetric g (0,0) = fun _ => (1 : (Mat n)) := by
  funext x
  simp [affineChartMetric,affineChartMap,hg₀]

theorem affineChartMetric_dilatedMetric (g : (MetricField n)) (lam : ℝ) (c : (X n)) (s : ℝ) :
    affineChartMetric (dilatedMetric g lam) (c,s) = affineChartMetric g (lam • c,lam*s) := by
  funext x
  simp [affineChartMetric,affineChartMap,dilatedMetric,smul_add,smul_smul]

private theorem coordDeriv_translate (c : (X n)) (f : (X n) → ℝ) (i : (I n)) :
    coordDeriv i (fun z => f (c+z)) = fun x => coordDeriv i f (c+x) := by
  funext x
  unfold coordDeriv
  rw [fderiv_comp_add_left]

theorem laplace_translate (g : (MetricField n)) (f : (X n) → ℝ) (c x : (X n)) :
    laplace (fun z => g (c+z)) (fun z => f (c+z)) x = laplace g f (c+x) := by
  have hc (i j k : (I n)) : coordDeriv k (fun z => g (c+z) i j) x =
      coordDeriv k (fun z => g z i j) (c+x) :=
    congrFun (coordDeriv_translate c (fun z => g z i j) k) x
  simp only [laplace,christoffel,coordDeriv_translate,hc]

theorem laplace_affineChart {U : Set (X n)} (hU : IsOpen U) {g : (MetricField n)}
    (hg : SmoothMetric U g) {f : (X n) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (c : (X n)) (s : ℝ) {x : (X n)} (hx : affineChartMap c s x ∈ U) :
    laplace (affineChartMetric g (c,s)) (f ∘ affineChartMap c s) x =
      s^2 * laplace g f (affineChartMap c s x) := by
  let V := (fun z : (X n) => c+z) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hgt : SmoothMetric V (fun z => g (c+z)) :=
    ⟨fun i j => (hg.1 i j).comp (contDiff_const.add contDiff_id).contDiffOn
      (fun _ hz => hz),fun y hy => hg.2 (c+y) hy⟩
  have hft : ContDiffOn ℝ ∞ (fun z => f (c+z)) V :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hz => hz)
  have h := laplace_dilated hV hgt hft (lam := s) (y := x) hx
  rw [laplace_translate] at h
  exact h

end CalderonN
