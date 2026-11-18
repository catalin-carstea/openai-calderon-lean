import Proof.CurvatureSkew
import Proof.FrameBasis
import Proof.Archive.PolynomialEvaluation

noncomputable section
open Set MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

def movingFrameCoordinate (g : MetricField) (e : Frame) (i : I) (z : X × X) : ℝ :=
  metricPair g z.1 z.2 (e z.1 i)

lemma contDiffAt_movingFrameCoordinate {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (e : Frame) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {y : X} (hy : y ∈ Ω) (w : X) (i : I) : ContDiffAt ℝ ∞ (movingFrameCoordinate g e i) (y,w) := by
  change ContDiffAt ℝ ∞ (fun z : X × X => ∑ a : I, ∑ b : I, g z.1 a b * z.2 a * e z.1 i b) (y,w)
  exact ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ =>
    ((((h.1 a b).contDiffAt (hΩ.mem_nhds hy)).comp (y,w) contDiffAt_fst).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.contDiffAt.comp (y,w) contDiffAt_snd)).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) b).contDiff.contDiffAt.comp y
        ((he i).contDiffAt (hΩ.mem_nhds hy))).comp (y,w) contDiffAt_fst)))

lemma fderiv_movingFrameCoordinate {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (e : Frame) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {y : X} (hy : y ∈ Ω) (w a b : X) (i : I) :
    fderiv ℝ (movingFrameCoordinate g e i) (y,w) (a,b) =
      metricDifferential g y a w (e y i) + metricPair g y b (e y i) +
        metricPair g y w (fderiv ℝ (fun x => e x i) y a) := by
  have hfst := hasFDerivAt_fst (𝕜 := ℝ) (p := (y,w))
  have hsnd := hasFDerivAt_snd (𝕜 := ℝ) (p := (y,w))
  have hG (j k : I) := (((h.1 j k).contDiffAt (hΩ.mem_nhds hy)).differentiableAt
    (by simp)).hasFDerivAt.comp (y,w) hfst
  have hW (j : I) := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp (y,w) hsnd
  have hE (j : I) := ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp y
    (((he i).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt).comp (y,w) hfst
  have hh := HasFDerivAt.sum (u := Finset.univ) (fun j _ =>
    HasFDerivAt.sum (u := Finset.univ) (fun k _ => ((hG j k).mul (hW j)).mul (hE k)))
  have hfun : movingFrameCoordinate g e i =
      ∑ j, ∑ k, ((fun x => g x j k) ∘ Prod.fst) *
        ((EuclideanSpace.proj j) ∘ Prod.snd) * (((EuclideanSpace.proj k) ∘ (fun x => e x i)) ∘ Prod.fst) := by
    funext z
    simp [movingFrameCoordinate, metricPair, PiLp.proj_apply]
  rw [hfun, hh.fderiv]
  simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Function.comp_apply, Pi.mul_apply, PiLp.proj_apply, smul_eq_mul, metricDifferential_apply, metricPair]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma movingFrameCoordinate_horizontal {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {y : X} (hy : y ∈ Ω) (w a : X) (i : I) :
    fderiv ℝ (movingFrameCoordinate g e i) (y,w) (a, -connection g y a w) =
      metricPair g y w (covariantFrameVector g e y a i) := by
  rw [fderiv_movingFrameCoordinate hΩ h e he hy]
  have hh := connection_metric hΩ h hK hy a w (e y i)
  simp only [covariantFrameVector, ← metricBilinear_apply, map_add, _root_.add_apply,
    map_neg, _root_.neg_apply] at hh ⊢
  linarith

lemma movingFrameCoordinate_horizontal_sum {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {y : X} (hy : y ∈ Ω) (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (w a : X) (i : I) :
    fderiv ℝ (movingFrameCoordinate g e i) (y,w) (a, -connection g y a w) =
      ∑ j, frameConnectionCoefficient g e y a i j * movingFrameCoordinate g e j (y,w) := by
  rw [movingFrameCoordinate_horizontal hΩ h hK e he hy]
  have hh := (frameBasis g e y hframe).sum_repr (covariantFrameVector g e y a i)
  conv_lhs => rw [← hh]
  simp only [frameBasis_apply, frameBasis_repr, metricPair_sum_right, metricPair_smul_right,
    frameConnectionCoefficient, movingFrameCoordinate]

def movingFramePolynomial (g : MetricField) (e : Frame) (p : MvPolynomial I ℝ) (z : X × X) : ℝ :=
  eval (fun i => movingFrameCoordinate g e i z) p

lemma movingFramePolynomial_sub (g : MetricField) (e : Frame) (p q : MvPolynomial I ℝ) (z : X × X) :
    movingFramePolynomial g e (p-q) z = movingFramePolynomial g e p z - movingFramePolynomial g e q z := by
  simp only [movingFramePolynomial, map_sub]

lemma contDiffAt_movingFramePolynomial {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (e : Frame) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {y : X} (hy : y ∈ Ω) (w : X) (p : MvPolynomial I ℝ) :
    ContDiffAt ℝ ∞ (movingFramePolynomial g e p) (y,w) := by
  unfold movingFramePolynomial
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X × X => c) (y,w))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, eval_X] using hp.mul (contDiffAt_movingFrameCoordinate hΩ h e he hy w i)

lemma fderiv_movingFramePolynomial {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (e : Frame) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    {y : X} (hy : y ∈ Ω) (w a b : X) (p : MvPolynomial I ℝ) :
    fderiv ℝ (movingFramePolynomial g e p) (y,w) (a,b) =
      ∑ i, fderiv ℝ (movingFrameCoordinate g e i) (y,w) (a,b) *
        eval (fun j => movingFrameCoordinate g e j (y,w)) (pderiv i p) := by
  have hc := hasFDerivAt_pi.mpr (fun i =>
    ((contDiffAt_movingFrameCoordinate hΩ h e he hy w i).differentiableAt (by simp)).hasFDerivAt)
  have hp := (OAI.AnisotropicCalderon.GreenRadialTrace.hasFDerivAt_eval p
    (fun i => movingFrameCoordinate g e i (y,w))).comp (y,w) hc
  change HasFDerivAt (movingFramePolynomial g e p) _ (y,w) at hp
  rw [hp.fderiv, ContinuousLinearMap.comp_apply,
    OAI.AnisotropicCalderon.GreenRadialTrace.polynomialFDeriv_apply]
  rfl

/-- The polynomial covariant connection agrees with horizontal transport in the actual
    tangent bundle. -/
theorem movingFramePolynomial_horizontal {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {y : X} (hy : y ∈ Ω) (w a : X) (p : MvPolynomial I ℝ) :
    horizontal g (movingFramePolynomial g e p) y w a =
      movingFramePolynomial g e (polynomialConnectionAction (frameConnectionCoefficient g e y a) p) (y,w) := by
  rw [horizontal, fderiv_movingFramePolynomial hΩ h e he hy]
  simp_rw [movingFrameCoordinate_horizontal_sum hΩ h hK e he hy (hframe y hy)]
  simp only [movingFramePolynomial, polynomialConnectionAction, map_sum, map_mul, eval_C, eval_X,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [frameConnection_skew hΩ h hK e he hframe hy a j i]
  ring

end ShrinkingSpheres
