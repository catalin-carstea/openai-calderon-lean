module

public import Proof.CalderonN.Coercivity
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

set_option maxSynthPendingDepth 10

public section

/- CoordinateTensors, MetricConnection, HorizontalGeometry and FrameConnection
   from Proposition 5.3 check f308cb9d. The operations are the protected
   metric, connection and horizontal derivative in dimension n. -/
noncomputable section
open Set
open scoped ContDiff MatrixOrder Matrix.Norms.L2Operator
namespace CalderonN
variable {n : ℕ}

lemma Elliptic.posDef {Ω : Set (X n)} {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) : (g y).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · exact Matrix.isHermitian_iff_isSymm.mpr (h.2 y hy).1
  · intro v hv
    let w : (X n) := WithLp.toLp 2 v
    have hw : w ≠ 0 := by
      intro hzero
      apply hv
      exact congrArg WithLp.ofLp hzero
    have hp : 0 < K⁻¹ * ‖w‖^2 := mul_pos (inv_pos.mpr hK) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw))
    have ht := hp.trans_le ((h.2 y hy).2 w).1
    simpa only [metricPair, w, Matrix.mulVec, dotProduct, Finset.mul_sum, star_trivial, mul_assoc, mul_left_comm] using ht

/-- Lowering the upper connection index cancels the inverse metric in the Christoffel formula. -/
lemma lower_christoffel (g : (MetricField n)) (y : (X n)) (hg : (g y).PosDef) (l i j : (I n)) :
    (∑ k, g y l k * christoffel g y k i j) =
      (coordDeriv i (fun x => g x l j) y + coordDeriv j (fun x => g x i l) y -
        coordDeriv l (fun x => g x i j) y) / 2 := by
  let v : (I n) → ℝ := fun a => coordDeriv i (fun x => g x a j) y +
    coordDeriv j (fun x => g x i a) y - coordDeriv a (fun x => g x i j) y
  have hinv := Matrix.mul_nonsing_inv (g y) (isUnit_iff_ne_zero.mpr hg.det_pos.ne')
  have hv := congrArg (fun M : (Mat n) => (Matrix.mulVec M v) l) hinv
  rw [← Matrix.mulVec_mulVec] at hv
  simp only [Matrix.one_mulVec] at hv
  change (∑ k, g y l k * ∑ a, (g y)⁻¹ k a * v a) = v l at hv
  change (∑ k, g y l k * ((∑ a, (g y)⁻¹ k a * v a) / 2)) = v l / 2
  simp only [← mul_div_assoc, ← Finset.sum_div, hv]

/-- Symmetry of each coordinate derivative follows from symmetry throughout an open domain. -/
lemma metric_derivative_symmetric {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) {y : (X n)} (hy : y ∈ Ω) (i j a : (I n)) :
    coordDeriv a (fun x => g x i j) y = coordDeriv a (fun x => g x j i) y := by
  have heq : (fun x => g x i j) =ᶠ[nhds y] (fun x => g x j i) := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    have hh := congrArg (fun M : (Mat n) => M i j) (h.2 x hx).1
    exact hh.symm
  exact congrArg (fun L : (X n) →L[ℝ] ℝ => L (axis a)) heq.fderiv_eq

lemma connection_axis_components (g : (MetricField n)) (y : (X n)) (a i k : (I n)) :
    connection g y (axis a) (axis i) k = christoffel g y k a i := by
  simp [connection, axis]

lemma metricPair_axis_left (g : (MetricField n)) (y v : (X n)) (i : (I n)) :
    metricPair g y (axis i) v = ∑ j, g y i j * v j := by
  simp [metricPair, axis]

lemma metricPair_axis_right (g : (MetricField n)) (y v : (X n)) (j : (I n)) :
    metricPair g y v (axis j) = ∑ i, g y i j * v i := by
  simp [metricPair, axis]

/-- Levi–Civita compatibility in the coordinate basis, from the actual metric derivatives. -/
lemma connection_metric_basis {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (a i j : (I n)) :
    metricPair g y (connection g y (axis a) (axis i)) (axis j) +
      metricPair g y (axis i) (connection g y (axis a) (axis j)) =
        coordDeriv a (fun x => g x i j) y := by
  rw [metricPair_axis_right, metricPair_axis_left]
  simp_rw [connection_axis_components]
  have hs (k : (I n)) : g y k j = g y j k := by
    exact congrArg (fun M : (Mat n) => M j k) (h.2 y hy).1
  simp_rw [hs]
  rw [lower_christoffel g y (h.posDef hK hy), lower_christoffel g y (h.posDef hK hy),
    metric_derivative_symmetric hΩ h hy j i a]
  ring

/-- The coordinate metric as a continuous bilinear form. -/
@[expose] def metricBilinear (g : (MetricField n)) (y : (X n)) : (X n) →L[ℝ] (X n) →L[ℝ] ℝ :=
  ∑ i, ∑ j, (g y i j) • (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)

lemma metricBilinear_apply (g : (MetricField n)) (y u v : (X n)) :
    metricBilinear g y u v = metricPair g y u v := by
  simp only [metricBilinear, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, smul_eq_mul, metricPair]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The connection coefficients as a continuous bilinear map in its two vector arguments. -/
@[expose] def connectionBilinear (g : (MetricField n)) (y : (X n)) : (X n) →L[ℝ] (X n) →L[ℝ] (X n) :=
  ∑ i, ∑ j, ∑ k, (christoffel g y k i j) •
    (EuclideanSpace.proj i).smulRight ((EuclideanSpace.proj j).smulRight (axis k))

lemma connectionBilinear_apply (g : (MetricField n)) (y a v : (X n)) :
    connectionBilinear g y a v = connection g y a v := by
  ext l
  simp [connectionBilinear, connection, axis, smul_smul, Pi.single_apply]

/-- The spatial derivative of the metric with two fixed tangent vectors. -/
@[expose] def metricDifferential (g : (MetricField n)) (y : (X n)) : (X n) →L[ℝ] (X n) →L[ℝ] (X n) →L[ℝ] ℝ :=
  ∑ i, ∑ j, (fderiv ℝ (fun x => g x i j) y).smulRight
    ((EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j))

lemma metricDifferential_apply (g : (MetricField n)) (y a u v : (X n)) :
    metricDifferential g y a u v = ∑ i, ∑ j, (fderiv ℝ (fun x => g x i j) y a) * u i * v j := by
  simp only [metricDifferential, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, PiLp.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma axis_expansion (v : (X n)) : (∑ i, v i • axis i) = v := by
  simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, axis]
    using (EuclideanSpace.basisFun (I n) ℝ).sum_repr v

lemma connection_metric_basis_direction {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (a : (X n)) (i j : (I n)) :
    metricPair g y (connection g y a (axis i)) (axis j) +
      metricPair g y (axis i) (connection g y a (axis j)) =
        fderiv ℝ (fun x => g x i j) y a := by
  have hsum := axis_expansion a
  rw [← connectionBilinear_apply, ← connectionBilinear_apply,
    ← metricBilinear_apply, ← metricBilinear_apply]
  rw [← hsum]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_add, metricBilinear_apply, metricBilinear_apply,
    connectionBilinear_apply, connectionBilinear_apply, connection_metric_basis hΩ h hK hy]
  rfl

/-- Full metric compatibility, in the same ambient tangent coordinates as horizontal. -/
lemma connection_metric {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (a u v : (X n)) :
    metricPair g y (connection g y a u) v + metricPair g y u (connection g y a v) =
      metricDifferential g y a u v := by
  have basis (i j : (I n)) :
      metricBilinear g y (connectionBilinear g y a (axis i)) (axis j) +
        metricBilinear g y (axis i) (connectionBilinear g y a (axis j)) =
          metricDifferential g y a (axis i) (axis j) := by
    rw [metricBilinear_apply, metricBilinear_apply,
      connectionBilinear_apply, connectionBilinear_apply, connection_metric_basis_direction hΩ h hK hy]
    simp [metricDifferential_apply, axis]
  rw [← connectionBilinear_apply, ← connectionBilinear_apply,
    ← metricBilinear_apply, ← metricBilinear_apply]
  rw [← axis_expansion u, ← axis_expansion v]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hb := congrArg (fun z => v i * u j * z) (basis j i)
  nlinarith only [hb]

lemma metric_square_fderiv {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) {y : (X n)} (hy : y ∈ Ω) (w a b : (X n)) :
    fderiv ℝ (fun p : (X n) × (X n) => metricPair g p.1 p.2 p.2) (y,w) (a,b) =
      metricDifferential g y a w w + metricPair g y b w + metricPair g y w b := by
  have hfst := hasFDerivAt_fst (𝕜 := ℝ) (p := (y,w))
  have hsnd := hasFDerivAt_snd (𝕜 := ℝ) (p := (y,w))
  have hG (i j : (I n)) := (((h.1 i j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt
    (by simp)).hasFDerivAt.comp (y,w) hfst
  have hW (i : (I n)) := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp (y,w) hsnd
  have hterm (i j : (I n)) := ((hG i j).mul (hW i)).mul (hW j)
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u := Finset.univ) (fun j _ => hterm i j))
  have hfun : (fun p : (X n) × (X n) => metricPair g p.1 p.2 p.2) =
      (∑ i, ∑ j, ((fun y => g y i j) ∘ Prod.fst) *
        ((EuclideanSpace.proj i) ∘ Prod.snd) * ((EuclideanSpace.proj j) ∘ Prod.snd)) := by
    funext p
    simp [metricPair]
  rw [hfun, hsum.fderiv]
  simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_apply, Pi.mul_apply,
    PiLp.proj_apply, smul_eq_mul, metricDifferential_apply, metricPair]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Horizontal transport is tangent to the unit tangent sphere. -/
lemma horizontal_metric_square {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (w a : (X n)) :
    horizontal g (fun p => metricPair g p.1 p.2 p.2) y w a = 0 := by
  rw [horizontal, metric_square_fderiv hΩ h hy]
  have hm := connection_metric hΩ h hK hy a w w
  rw [← connectionBilinear_apply, ← metricBilinear_apply, ← metricBilinear_apply]
  simp only [map_neg, _root_.neg_apply]
  rw [← connectionBilinear_apply, ← metricBilinear_apply, ← metricBilinear_apply] at hm
  linarith

lemma metric_pair_fderiv {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) {y : (X n)} (hy : y ∈ Ω) (U V : (X n) → (X n))
    (hU : DifferentiableAt ℝ U y) (hV : DifferentiableAt ℝ V y) (a : (X n)) :
    fderiv ℝ (fun x => metricPair g x (U x) (V x)) y a =
      metricDifferential g y a (U y) (V y) +
        metricPair g y (fderiv ℝ U y a) (V y) + metricPair g y (U y) (fderiv ℝ V y a) := by
  have hG (i j : (I n)) := (((h.1 i j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hU' (i : (I n)) := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y hU.hasFDerivAt
  have hV' (i : (I n)) := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y hV.hasFDerivAt
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u := Finset.univ) (fun j _ => ((hG i j).mul (hU' i)).mul (hV' j)))
  have hfun : (fun x => metricPair g x (U x) (V x)) =
      (∑ i, ∑ j, (fun x => g x i j) * ((EuclideanSpace.proj i) ∘ U) *
        ((EuclideanSpace.proj j) ∘ V)) := by
    funext x
    simp [metricPair]
  rw [hfun, hsum.fderiv]
  simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply, Pi.mul_apply, PiLp.proj_apply,
    smul_eq_mul, metricDifferential_apply, metricPair]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_symm (g : (MetricField n)) (y u v : (X n)) (hs : (g y).transpose = g y) :
    metricPair g y u v = metricPair g y v u := by
  unfold metricPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij := congrArg (fun M : (Mat n) => M i j) hs
  change g y j i = g y i j at hij
  rw [hij]
  ring

@[expose] def covariantFrameVector (g : (MetricField n)) (e : (Frame n)) (y a : (X n)) (i : (I n)) : (X n) :=
  fderiv ℝ (fun x => e x i) y a + connection g y a (e y i)

@[expose] def frameConnectionCoefficient (g : (MetricField n)) (e : (Frame n)) (y a : (X n)) (i j : (I n)) : ℝ :=
  metricPair g y (covariantFrameVector g e y a i) (e y j)

/-- The connection matrix of a smooth orthonormal frame is skew-symmetric. -/
lemma frameConnection_skew {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {y : (X n)} (hy : y ∈ Ω) (a : (X n)) (i j : (I n)) :
    frameConnectionCoefficient g e y a i j = -frameConnectionCoefficient g e y a j i := by
  have hU := ((he i).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hV := ((he j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hconst : (fun x => metricPair g x (e x i) (e x j)) =ᶠ[nhds y]
      (fun _ => if i = j then (1:ℝ) else 0) := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact hframe x hx i j
  have hzero := congrArg (fun L : (X n) →L[ℝ] ℝ => L a) hconst.fderiv_eq
  simp only [fderiv_const_apply, zero_apply] at hzero
  rw [metric_pair_fderiv hΩ h hy _ _ hU hV] at hzero
  have hcomp := connection_metric hΩ h hK hy a (e y i) (e y j)
  have hs := metricPair_symm g y (covariantFrameVector g e y a j) (e y i) (h.2 y hy).1
  unfold covariantFrameVector at hs
  simp only [frameConnectionCoefficient, covariantFrameVector, ← metricBilinear_apply,
    map_add, _root_.add_apply] at hs ⊢
  simp only [← metricBilinear_apply] at hzero hcomp
  linarith

end CalderonN
