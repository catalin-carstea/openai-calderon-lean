module

public import Proof.CalderonN.CoordinateJacobi
public import Proof.CalderonN.ParallelFrameCalculus

import Proof.CalderonN.CovariantHessian
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The coordinate derivative of the Christoffel bilinear map in a base direction. -/
@[expose] def connectionDerivative (g : (MetricField dim)) (x d u v : (X dim)) : (X dim) :=
  WithLp.toLp 2 fun k => ∑ i, ∑ j,
    fderiv ℝ (fun y => christoffel g y k i j) x d * u i * v j

private theorem connection_add_right (g : (MetricField dim)) (x u v w : (X dim)) :
    connection g x u (v + w) = connection g x u v + connection g x u w := by
  ext k
  simp only [connection, PiLp.toLp_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib]

private theorem hasDerivAt_connection_curve
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {x u v : ℝ → (X dim)} {t : ℝ} {x' u' v' : (X dim)} (hxΩ : x t ∈ Ω)
    (hx : HasDerivAt x x' t) (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => connection g (x s) (u s) (v s))
      (connectionDerivative g (x t) x' (u t) (v t) +
        connection g (x t) u' (v t) + connection g (x t) (u t) v') t := by
  let target := connectionDerivative g (x t) x' (u t) (v t) +
    connection g (x t) u' (v t) + connection g (x t) (u t) v'
  let f (s : ℝ) (k : (I dim)) := ∑ i, ∑ j, christoffel g (x s) k i j * u s i * v s j
  have h (k : (I dim)) : HasDerivAt (fun s => f s k) (target k) t := by
    have hΓ (i j : (I dim)) : HasDerivAt (fun s => christoffel g (x s) k i j)
        (fderiv ℝ (fun y => christoffel g y k i j) (x t) x') t :=
      (((contDiffOn_christoffel hΩ hg k i j).contDiffAt
        (hΩ.mem_nhds hxΩ)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hx
    have hu' (i : (I dim)) : HasDerivAt (fun s => u s i) (u' i) t :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hu
    have hv' (j : (I dim)) : HasDerivAt (fun s => v s j) (v' j) t :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt t hv
    have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (I dim))) fun i _ =>
      HasDerivAt.fun_sum (u := (Finset.univ : Finset (I dim))) fun j _ =>
        ((hΓ i j).mul (hu' i)).mul (hv' j)
    convert hsum using 1
    simp only [target, connectionDerivative, connection, PiLp.add_apply,
      PiLp.toLp_apply, Pi.mul_apply, add_mul, Finset.sum_add_distrib]
  have hpi : HasDerivAt f (fun k => target k) t := hasDerivAt_pi.mpr h
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : (I dim) => ℝ)).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt t hpi

/-- The signed curvature term in the Jacobi equation for the covariant
acceleration of the variation. It is quadratic in the geodesic velocity. -/
@[expose] def jacobiCurvatureTerm (g : (MetricField dim)) (x v J : (X dim)) : (X dim) :=
  connectionDerivative g x v v J - connectionDerivative g x J v v -
    connection g x (connection g x v v) J + connection g x v (connection g x v J)

private theorem timeVelocity_variation_acceleration
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (hfamily : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      q (s,t) ∈ Ω ∧ timeVelocity (timeVelocity q) (s,t) =
        -connection g (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let x := q (0,t)
    let v := timeVelocity q (0,t)
    let J := pathVariation q (0,t)
    let J' := timeVelocity (pathVariation q) (0,t)
    timeVelocity (timeVelocity (pathVariation q)) (0,t) =
      -(connectionDerivative g x J v v + connection g x J' v + connection g x v J') := by
  ext k
  have h := coordinate_jacobi_equation hΩ hg hq hfamily ht k
  simp only [connectionDerivative, connection, PiLp.neg_apply, PiLp.add_apply]
  rw [h]
  simp only [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The ordinary derivative of the covariant variation velocity, with the
connection correction made explicit. -/
theorem hasDerivAt_variationCovariantTime
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (hfamily : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      q (s,t) ∈ Ω ∧ timeVelocity (timeVelocity q) (s,t) =
        -connection g (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => variationCovariantTime g q 0 s)
      (jacobiCurvatureTerm g (q (0,t)) (timeVelocity q (0,t)) (pathVariation q (0,t)) -
        connection g (q (0,t)) (timeVelocity q (0,t)) (variationCovariantTime g q 0 t)) t := by
  let x := q (0,t)
  let v := timeVelocity q (0,t)
  let J := pathVariation q (0,t)
  let J' := timeVelocity (pathVariation q) (0,t)
  obtain ⟨hxΩ,hacc⟩ := hfamily.self_of_nhds t ht
  have hx := hasDerivAt_geodesicTime (hq.differentiable (by simp) (0,t))
  have hv := hasDerivAt_geodesicTime ((contDiff_timeVelocity hq).differentiable (by simp) (0,t))
  have hJ := hasDerivAt_geodesicTime ((contDiff_pathVariation hq).differentiable (by simp) (0,t))
  have hJ' := hasDerivAt_geodesicTime
    ((contDiff_timeVelocity (contDiff_pathVariation hq)).differentiable (by simp) (0,t))
  have hD := hJ'.add (hasDerivAt_connection_curve hΩ hg hxΩ hx hv hJ)
  change HasDerivAt (fun s => variationCovariantTime g q 0 s)
    (timeVelocity (timeVelocity (pathVariation q)) (0,t) +
      (connectionDerivative g x v v J +
        connection g x (timeVelocity (timeVelocity q) (0,t)) J +
        connection g x v J')) t at hD
  have hJacc := timeVelocity_variation_acceleration hΩ hg hq hfamily ht
  change timeVelocity (timeVelocity (pathVariation q)) (0,t) =
    -(connectionDerivative g x J v v + connection g x J' v + connection g x v J') at hJacc
  change timeVelocity (timeVelocity q) (0,t) = -connection g x v v at hacc
  rw [hJacc,hacc] at hD
  have hneg (a b : (X dim)) : connection g x (-a) b = -connection g x a b := by
    ext k
    simp only [connection, PiLp.toLp_apply, PiLp.neg_apply, mul_neg, neg_mul,
      Finset.sum_neg_distrib]
  rw [hneg, connection_comm hΩ hg hxΩ J' v] at hD
  convert hD using 1
  change jacobiCurvatureTerm g x v J - connection g x v (J' + connection g x v J) = _
  rw [jacobiCurvatureTerm, connection_add_right]
  abel

/-- The second derivative of the Jacobi coordinates in the transported
frame is exactly the signed curvature term in that frame. -/
theorem sum_deriv_deriv_smul_parallelFrame_eq_jacobiCurvature
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (hfamily : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      q (s,t) ∈ Ω ∧ timeVelocity (timeVelocity q) (s,t) =
        -connection g (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)))
    (F : ℝ → (I dim) → (X dim)) {Z : ℝ → (X dim)} (hZ : ContDiff ℝ ∞ Z)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hF : ∀ᶠ s in 𝓝 t,
      (∀ i, HasDerivAt (fun r => F r i)
        (-connection g (q (0,s)) (timeVelocity q (0,s)) (F s i)) s) ∧
      pathVariation q (0,s) = ∑ i, Z s i • F s i) :
    (∑ i, deriv (deriv Z) t i • F t i) =
      jacobiCurvatureTerm g (q (0,t)) (timeVelocity q (0,t)) (pathVariation q (0,t)) := by
  have hZD (s : ℝ) : HasDerivAt Z (deriv Z s) s :=
    (hZ.differentiable (by simp) s).hasDerivAt
  have hZ' : ContDiff ℝ ∞ (deriv Z) := (hZ.of_le (show ∞ + 1 ≤ ∞ by simp)).deriv'
  have he : (fun s => variationCovariantTime g q 0 s) =ᶠ[𝓝 t]
      fun s => ∑ i, deriv Z s i • F s i := by
    filter_upwards [hF.eventually_nhds] with s hs
    exact variationCovariantTime_parallelFrame g hq F Z (hZD s) hs.self_of_nhds.1
      (hs.mono fun _ h => h.2)
  have ha := hasDerivAt_parallelFrame_sum g (q (0,t)) (timeVelocity q (0,t))
    F (deriv Z) ((hZ'.differentiable (by simp) t).hasDerivAt) hF.self_of_nhds.1
  have eq := (ha.congr_of_eventuallyEq he).unique
    (hasDerivAt_variationCovariantTime hΩ hg hq hfamily ht)
  rw [← he.eq_of_nhds] at eq
  exact sub_left_inj.mp eq

end CalderonN
