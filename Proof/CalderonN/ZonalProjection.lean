module

public import Proof.CalderonN.GaussianSphere
public import Proof.CalderonN.ZonalNormalization
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

import Mathlib.Tactic

@[expose] public section

/- Port of the pointwise projector comparison from Proposition 5.3 check f308cb9d.
   The finite-dimensional harmonic subspace admits an orthogonal projection directly. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped InnerProductSpace

namespace CalderonN
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ}

theorem finiteDimensional_harmonicHomogeneous (n k : ℕ) :
    FiniteDimensional ℝ (harmonicHomogeneous n k) := by
  let : Module.Finite ℝ (homogeneousSubmodule (Fin n) ℝ k) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin n) ℝ k)
  have hle : harmonicHomogeneous n k ≤ homogeneousSubmodule (Fin n) ℝ k :=
    fun _ hp => hp.1
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

variable [NeZero n]

instance (k : ℕ) : FiniteDimensional ℝ (harmonicSphereSubspace n k) := by
  let := finiteDimensional_harmonicHomogeneous n k
  change FiniteDimensional ℝ ((harmonicHomogeneous n k).map polynomialSphereL2)
  infer_instance

def harmonicProjection (k : ℕ) : SphereL2 n →L[ℝ] harmonicSphereSubspace n k :=
  (harmonicSphereSubspace n k).orthogonalProjectionOnto

theorem exists_harmonicProjectionPolynomial (k : ℕ) (u : SphereL2 n) :
    ∃ p : harmonicHomogeneous n k,
      polynomialSphereL2 p.val = (harmonicProjection k u : SphereL2 n) := by
  obtain ⟨p, hp, he⟩ := (harmonicProjection k u).property
  exact ⟨⟨p, hp⟩, he⟩

def harmonicProjectionPolynomial (k : ℕ) (u : SphereL2 n) : harmonicHomogeneous n k :=
  Classical.choose (exists_harmonicProjectionPolynomial k u)

theorem polynomialSphereL2_harmonicProjectionPolynomial (k : ℕ) (u : SphereL2 n) :
    polynomialSphereL2 (harmonicProjectionPolynomial k u).val = (harmonicProjection k u : SphereL2 n) :=
  Classical.choose_spec (exists_harmonicProjectionPolynomial k u)

omit [NeZero n] in
theorem unitSphere_sum_sq (w : UnitSphere n) : ∑ i, (w.val i)^2 = 1 := by
  have hw : ‖w.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  rw [← EuclideanSpace.real_norm_sq_eq, hw, one_pow]

theorem sphere_zonal_integral_eq_inner (w : UnitSphere n) (k : ℕ) (u : SphereL2 n) :
    (∫ z : UnitSphere n, zonal n (∑ i, w.val i * z.val i) k * u z ∂unitSphereProbability n) =
      ⟪polynomialSphereL2 (zonalPolynomial (w.val : I n → ℝ) k), u⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(polynomialSphere (zonalPolynomial (w.val : I n → ℝ) k)).coeFn_toLp
      (p := 2) (𝕜 := ℝ) (unitSphereProbability n)] with z hz
  change (polynomialSphereL2 (zonalPolynomial (w.val : I n → ℝ) k)) z =
    eval (z.val : I n → ℝ) (zonalPolynomial (w.val : I n → ℝ) k) at hz
  rw [hz, eval_zonalPolynomial_of_unit _ _ (unitSphere_sum_sq z)]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]

/-- The exact Gegenbauer kernel used in the statement represents the Hilbert
degree projection, evaluated in its harmonic polynomial representative. -/
theorem sphere_zonal_projection_Lp (hn : 3 ≤ n) (w : UnitSphere n) (k : ℕ) (u : SphereL2 n) :
    (harmonicMultiplicity n k : ℝ) *
      (∫ z : UnitSphere n, zonal n (∑ i, w.val i * z.val i) k * u z ∂unitSphereProbability n) =
      eval (w.val : I n → ℝ) (harmonicProjectionPolynomial k u).val := by
  let Z := zonalPolynomial (w.val : I n → ℝ) k
  have hZ : Z ∈ harmonicHomogeneous n k :=
    ⟨zonalPolynomial_homogeneous _ k, zonalPolynomial_harmonic hn _ (unitSphere_sum_sq w) k⟩
  let a : harmonicSphereSubspace n k := ⟨polynomialSphereL2 Z, polynomialSphereL2_mem k Z hZ⟩
  have ha : ⟪polynomialSphereL2 Z, u⟫_ℝ =
      ⟪polynomialSphereL2 Z, (harmonicProjection k u : SphereL2 n)⟫_ℝ :=
    ((harmonicSphereSubspace n k).inner_orthogonalProjectionOnto_eq_of_mem_left a u).symm
  rw [sphere_zonal_integral_eq_inner]
  change (harmonicMultiplicity n k : ℝ) * ⟪polynomialSphereL2 Z, u⟫_ℝ = _
  rw [ha, ← polynomialSphereL2_harmonicProjectionPolynomial]
  rw [sphereFischerInner n k Z _ hZ (harmonicProjectionPolynomial k u).property]
  exact weighted_normalizedFischer_zonalPolynomial hn _ k _
    (harmonicProjectionPolynomial k u).property.1 (harmonicProjectionPolynomial k u).property.2

end CalderonN
