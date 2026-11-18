import Proof.UniformAngularCoercivity
import Proof.Archive.SphereSobolevCompletion

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial Filter
open scoped InnerProductSpace Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SphereHilbertDecomposition
open OAI.AnisotropicCalderon.SpectralCoreRegularity

def harmonicProjection (k : ℕ) : SphereL2 →L[ℝ] harmonicSphereSubspace k :=
  sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k

lemma inner_harmonicProjection (k : ℕ) (v : harmonicSphereSubspace k) (u : SphereL2) :
    ⟪(v : SphereL2),u⟫_ℝ = ⟪(v : SphereL2),(harmonicProjection k u : SphereL2)⟫_ℝ := by
  classical
  rw [inner_sphereHarmonicDecomposition orthogonalSphereHarmonics denseSphereHarmonics,
    sphereHarmonicDecomposition_subtype orthogonalSphereHarmonics denseSphereHarmonics k v]
  rw [tsum_eq_single k]
  · rw [lp.single_apply_self]
    rfl
  · intro j hj
    rw [lp.single_apply_ne (E:=fun k => harmonicSphereSubspace k) 2 k v hj]
    exact inner_zero_left _

lemma exists_harmonicProjectionPolynomial (k : ℕ) (u : SphereL2) :
    ∃ p : harmonicHomogeneous k,polynomialSphereL2 p.val = (harmonicProjection k u : SphereL2) := by
  obtain ⟨p,hp,heq⟩ := (harmonicProjection k u).property
  exact ⟨⟨p,hp⟩,heq⟩

def harmonicProjectionPolynomial (k : ℕ) (u : SphereL2) : harmonicHomogeneous k :=
  Classical.choose (exists_harmonicProjectionPolynomial k u)

lemma polynomialSphereL2_harmonicProjectionPolynomial (k : ℕ) (u : SphereL2) :
    polynomialSphereL2 (harmonicProjectionPolynomial k u).val = (harmonicProjection k u : SphereL2) :=
  Classical.choose_spec (exists_harmonicProjectionPolynomial k u)

lemma sphere_legendre_integral_Lp_eq_inner (v : UnitSphere) (k : ℕ) (u : SphereL2) :
    (∫ z : UnitSphere,legendre (∑ i,v.val i*z.val i) k*u z ∂sphereProbability) =
      ⟪polynomialSphereL2 (zonalPolynomial (v.val : I → ℝ) k),u⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(polynomialSphere (zonalPolynomial (v.val : I → ℝ) k)).coeFn_toLp (p:=2) (𝕜:=ℝ) sphereProbability] with z hz
  change legendre (∑ i,v.val i*z.val i) k*u z = _
  change (polynomialSphereL2 (zonalPolynomial (v.val : I → ℝ) k)) z =
    eval (z.val : I → ℝ) (zonalPolynomial (v.val : I → ℝ) k) at hz
  rw [hz,eval_zonalPolynomial_unitSphere]
  simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial,mul_comm]

/-- The literal Legendre kernel is the Hilbert harmonic projection for every L2 datum,
    rather than only for a finite polynomial input. -/
theorem sphere_legendre_projection_Lp (v : UnitSphere) (k : ℕ) (u : SphereL2) :
    (2*(k : ℝ)+1)*(∫ z : UnitSphere,legendre (∑ i,v.val i*z.val i) k*u z ∂sphereProbability) =
      eval (v.val : I → ℝ) (harmonicProjectionPolynomial k u).val := by
  let Z := zonalPolynomial (v.val : I → ℝ) k
  have hZ : Z ∈ harmonicHomogeneous k :=
    ⟨zonalPolynomial_homogeneous _ k,zonalPolynomial_harmonic _ (unitSphere_sum_sq v) k⟩
  let a : harmonicSphereSubspace k := ⟨polynomialSphereL2 Z,polynomialSphereL2_mem k Z hZ⟩
  rw [sphere_legendre_integral_Lp_eq_inner]
  have hh := inner_harmonicProjection k a u
  change ⟪polynomialSphereL2 Z,u⟫_ℝ = ⟪polynomialSphereL2 Z,(harmonicProjection k u : SphereL2)⟫_ℝ at hh
  rw [hh,← polynomialSphereL2_harmonicProjectionPolynomial k u]
  simpa [Z] using sphere_legendre_inner_projection v k k
    (harmonicProjectionPolynomial k u).val (harmonicProjectionPolynomial k u).property.1
      (harmonicProjectionPolynomial k u).property.2

end ShrinkingSpheres
