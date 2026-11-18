import Proof.CoordinateTensors
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open Set
namespace ShrinkingSpheres

lemma metric_square_fderiv {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) {y : X} (hy : y ∈ Ω) (w a b : X) :
    fderiv ℝ (fun p : X × X => metricPair g p.1 p.2 p.2) (y,w) (a,b) =
      metricDifferential g y a w w + metricPair g y b w + metricPair g y w b := by
  have hfst := hasFDerivAt_fst (𝕜 := ℝ) (p := (y,w))
  have hsnd := hasFDerivAt_snd (𝕜 := ℝ) (p := (y,w))
  have hG (i j : I) := (((h.1 i j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt
    (by simp)).hasFDerivAt.comp (y,w) hfst
  have hW (i : I) := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp (y,w) hsnd
  have hterm (i j : I) := ((hG i j).mul (hW i)).mul (hW j)
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u := Finset.univ) (fun j _ => hterm i j))
  have hfun : (fun p : X × X => metricPair g p.1 p.2 p.2) =
      (∑ i, ∑ j, ((fun y => g y i j) ∘ Prod.fst) *
        ((EuclideanSpace.proj i) ∘ Prod.snd) * ((EuclideanSpace.proj j) ∘ Prod.snd)) := by
    funext p
    simp [metricPair, PiLp.proj_apply]
  rw [hfun, hsum.fderiv]
  simp only [_root_.sum_apply, ContinuousLinearMap.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_apply, Pi.mul_apply,
    PiLp.proj_apply, smul_eq_mul, metricDifferential_apply, metricPair]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Horizontal transport is tangent to the unit tangent sphere. -/
lemma horizontal_metric_square {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (w a : X) :
    horizontal g (fun p => metricPair g p.1 p.2 p.2) y w a = 0 := by
  rw [horizontal, metric_square_fderiv hΩ h hy]
  have hm := connection_metric hΩ h hK hy a w w
  rw [← connectionBilinear_apply, ← metricBilinear_apply, ← metricBilinear_apply,
    ]
  simp only [map_neg, _root_.neg_apply]
  rw [← connectionBilinear_apply, ← metricBilinear_apply, ← metricBilinear_apply] at hm
  linarith

end ShrinkingSpheres
