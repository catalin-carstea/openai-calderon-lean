import Proof.Curvature
import Proof.PolynomialConnection

noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

lemma contDiffAt_metric_square {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) {y : X} (hy : y ∈ Ω) (w : X) :
    ContDiffAt ℝ ∞ (fun z : X × X => metricPair g z.1 z.2 z.2) (y,w) := by
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
    ((((h.1 i j).contDiffAt (hΩ.mem_nhds hy)).comp (y,w) contDiffAt_fst).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp (y,w) contDiffAt_snd)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp (y,w) contDiffAt_snd)))

def curvatureLinear (Γ : X → X →L[ℝ] X →L[ℝ] X) (y a b : X) : X →L[ℝ] X :=
  (fderiv ℝ Γ y a) b - (fderiv ℝ Γ y b) a + (Γ y a).comp (Γ y b) - (Γ y b).comp (Γ y a)

lemma curvatureLinear_apply (Γ : X → X →L[ℝ] X →L[ℝ] X) (y a b w : X) :
    curvatureLinear Γ y a b w = coordinateCurvature Γ y a b w := by
  simp [curvatureLinear, coordinateCurvature]

lemma metricCurvature_self_pair_zero {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a b w : X) :
    metricPair g y (metricCurvature g y a b w) w = 0 := by
  let u : X × X → ℝ := fun z => metricPair g z.1 z.2 z.2
  have hn : (Prod.fst ⁻¹' Ω : Set (X × X)) ∈ nhds (y,w) :=
    (hΩ.preimage continuous_fst).mem_nhds hy
  have hzero (V : X → X) :
      vectorFieldDeriv (horizontalVectorField (connectionBilinear g) V) u =ᶠ[nhds (y,w)] (fun _ => 0) := by
    filter_upwards [hn] with z hz
    simpa only [vectorFieldDeriv, horizontalVectorField, connectionBilinear_apply, u, horizontal] using
      horizontal_metric_square hΩ h hK hz z.2 (V z.1)
  have hd (V W : X → X) : vectorFieldDeriv (horizontalVectorField (connectionBilinear g) V)
      (vectorFieldDeriv (horizontalVectorField (connectionBilinear g) W) u) (y,w) = 0 := by
    change fderiv ℝ (vectorFieldDeriv (horizontalVectorField (connectionBilinear g) W) u)
      (y,w) (horizontalVectorField (connectionBilinear g) V (y,w)) = 0
    rw [(hzero W).fderiv_eq]
    simp
  have hh := metric_horizontal_commutator hΩ h hK (fun _ => a) (fun _ => b)
    contDiffOn_const contDiffOn_const u hy w (contDiffAt_metric_square hΩ h hy w)
  rw [hd, hd, (hzero _).eq_of_nhds] at hh
  change (0:ℝ) - 0 - 0 = fderiv ℝ (fun z : X × X => metricPair g z.1 z.2 z.2)
    (y,w) (0, -metricCurvature g y a b w) at hh
  rw [metric_square_fderiv hΩ h hy] at hh
  have hs := metricPair_symm g y w (metricCurvature g y a b w) (h.2 y hy).1
  simp only [map_zero, zero_apply, ← metricBilinear_apply, map_neg, _root_.neg_apply] at hh hs ⊢
  linarith

/-- Curvature of the actual metric connection is skew for the same metric pairing. -/
theorem metricCurvature_skew {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a b u v : X) :
    metricPair g y (metricCurvature g y a b u) v +
      metricPair g y u (metricCurvature g y a b v) = 0 := by
  have hu := metricCurvature_self_pair_zero hΩ h hK hy a b u
  have hv := metricCurvature_self_pair_zero hΩ h hK hy a b v
  have huv := metricCurvature_self_pair_zero hΩ h hK hy a b (u+v)
  have hs := metricPair_symm g y (metricCurvature g y a b v) u (h.2 y hy).1
  simp only [metricCurvature, ← curvatureLinear_apply, ← metricBilinear_apply,
    map_add, _root_.add_apply] at hu hv huv hs ⊢
  linarith

def frameCurvatureCoefficient (g : MetricField) (e : Frame) (y a b : X) (i j : I) : ℝ :=
  metricPair g y (metricCurvature g y a b (e y i)) (e y j)

lemma frameCurvatureCoefficient_skew {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame) {y : X} (hy : y ∈ Ω) (a b : X) (i j : I) :
    frameCurvatureCoefficient g e y a b i j = -frameCurvatureCoefficient g e y a b j i := by
  have hh := metricCurvature_skew hΩ h hK hy a b (e y i) (e y j)
  rw [metricPair_symm g y (e y i) _ (h.2 y hy).1] at hh
  exact eq_neg_of_add_eq_zero_left hh

def curvaturePolynomialAction (g : MetricField) (e : Frame) (y a b : X) (p : MvPolynomial I ℝ) :
    MvPolynomial I ℝ := polynomialConnectionAction (frameCurvatureCoefficient g e y a b) p

lemma curvaturePolynomialAction_skew {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame) {y : X} (hy : y ∈ Ω)
    (a b : X) (p q : MvPolynomial I ℝ) :
    fischerInner (curvaturePolynomialAction g e y a b p) q =
      -fischerInner p (curvaturePolynomialAction g e y a b q) :=
  polynomialConnectionAction_skew _ (frameCurvatureCoefficient_skew hΩ h hK e hy a b) p q

lemma curvaturePolynomialAction_harmonic {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame) {y : X} (hy : y ∈ Ω)
    (a b : X) (p : MvPolynomial I ℝ) (hp : laplacian p = 0) :
    laplacian (curvaturePolynomialAction g e y a b p) = 0 :=
  polynomialConnectionAction_harmonic _ (frameCurvatureCoefficient_skew hΩ h hK e hy a b) p hp

end ShrinkingSpheres
