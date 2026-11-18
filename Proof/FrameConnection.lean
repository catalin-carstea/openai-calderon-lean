import Proof.HorizontalGeometry

noncomputable section
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma metric_pair_fderiv {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) {y : X} (hy : y ∈ Ω) (U V : X → X)
    (hU : DifferentiableAt ℝ U y) (hV : DifferentiableAt ℝ V y) (a : X) :
    fderiv ℝ (fun x => metricPair g x (U x) (V x)) y a =
      metricDifferential g y a (U y) (V y) +
        metricPair g y (fderiv ℝ U y a) (V y) + metricPair g y (U y) (fderiv ℝ V y a) := by
  have hG (i j : I) := (((h.1 i j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hU' (i : I) := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y hU.hasFDerivAt
  have hV' (i : I) := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y hV.hasFDerivAt
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u := Finset.univ) (fun j _ => ((hG i j).mul (hU' i)).mul (hV' j)))
  have hfun : (fun x => metricPair g x (U x) (V x)) =
      (∑ i, ∑ j, (fun x => g x i j) * ((EuclideanSpace.proj i) ∘ U) *
        ((EuclideanSpace.proj j) ∘ V)) := by
    funext x
    simp [metricPair, PiLp.proj_apply]
  rw [hfun, hsum.fderiv]
  simp only [_root_.sum_apply, ContinuousLinearMap.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply, Pi.mul_apply, PiLp.proj_apply,
    smul_eq_mul, metricDifferential_apply, metricPair]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_symm (g : MetricField) (y u v : X) (hs : (g y).transpose = g y) :
    metricPair g y u v = metricPair g y v u := by
  unfold metricPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij := congrArg (fun M : Mat => M i j) hs
  change g y j i = g y i j at hij
  rw [hij]
  ring

def covariantFrameVector (g : MetricField) (e : Frame) (y a : X) (i : I) : X :=
  fderiv ℝ (fun x => e x i) y a + connection g y a (e y i)

def frameConnectionCoefficient (g : MetricField) (e : Frame) (y a : X) (i j : I) : ℝ :=
  metricPair g y (covariantFrameVector g e y a i) (e y j)

/-- The connection matrix of a smooth orthonormal frame is skew-symmetric. -/
lemma frameConnection_skew {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {y : X} (hy : y ∈ Ω) (a : X) (i j : I) :
    frameConnectionCoefficient g e y a i j = -frameConnectionCoefficient g e y a j i := by
  have hU := ((he i).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hV := ((he j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hconst : (fun x => metricPair g x (e x i) (e x j)) =ᶠ[nhds y]
      (fun _ => if i = j then (1:ℝ) else 0) := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact hframe x hx i j
  have hzero := congrArg (fun L : X →L[ℝ] ℝ => L a) hconst.fderiv_eq
  simp only [fderiv_const_apply, zero_apply] at hzero
  rw [metric_pair_fderiv hΩ h hy _ _ hU hV] at hzero
  have hcomp := connection_metric hΩ h hK hy a (e y i) (e y j)
  have hs := metricPair_symm g y (covariantFrameVector g e y a j) (e y i) (h.2 y hy).1
  unfold covariantFrameVector at hs
  simp only [frameConnectionCoefficient, covariantFrameVector, ← metricBilinear_apply,
    map_add, _root_.add_apply] at hs ⊢
  simp only [← metricBilinear_apply] at hzero hcomp
  linarith

end ShrinkingSpheres
