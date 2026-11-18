import Proof.PhysicalAngularModelData
import Proof.PolynomialShiftIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

/-- The actual weighted finite polynomial field has exactly the harmonic coefficient of
    the smooth signed horizontal/degree field. The logarithmic coefficient is localized
    only outside the common compact support, where both sides vanish. -/
theorem polynomialSphereL2_weighted_coordinates {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : smoothNear φ (bundle Y g)) (E : HarmonicTestExpansion Y g e φ)
    (r : X → ℝ) (L : ℂ →L[ℝ] ℝ) (H : X × X → ℝ) (hH : ContDiff ℝ ∞ H) (i : I) (k : ℕ) (c : X → Fin (E.dimension k) → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcs : tsupport c ⊆ E.supportSet)
    (hcrep : ∀ x,polynomialSphereL2 (finitePolynomialField (E.basis k) c x) =
      (harmonicProjection (k+1) (ambientSphereL2 (fun p => L (E.representative p))
        (L.contDiff.comp E.representativeSmooth) x) : SphereL2))
    (hHrep : ∀ y ∈ Y,∀ v : UnitSphere,H (y,v.val) = L (horizontal g φ y (frameVector e y v.val) (e y i)))
    (hHz : ∀ y ∉ E.supportSet,∀ v : UnitSphere,H (y,v.val) = 0)
    (b : X → ℝ) (hb : ∀ y ∈ E.supportSet,b y = fderiv ℝ (fun x => Real.log (r x)) y (e y i))
    (s : ℝ) {y : X} (hy : y ∈ Y) :
    polynomialSphereL2 (weightedPolynomialDerivative g e (E.basis k) c (fun x => Real.log (r x))
      (k+1) s y (e y i)) =
      (harmonicProjection (k+1) (weightedAngularSection H (fun p => L (E.representative p)) hH
        (L.contDiff.comp E.representativeSmooth) b s y) : SphereL2) := by
  let G : X × X → ℝ := fun p => L (E.representative p)
  have hG : ContDiff ℝ ∞ G := L.contDiff.comp E.representativeSmooth
  by_cases hys : y ∈ E.supportSet
  · have hHL : ambientSphereL2 H hH y =ᵐ[sphereProbability]
        (fun v : UnitSphere => L (horizontal g φ y (frameVector e y v.val) (e y i))) := by
      apply (ambientSphereL2_ae H hH y).trans
      exact Filter.Eventually.of_forall (fun v => hHrep y hy v)
    have hU : ContDiff ℝ ∞ (fun x => harmonicProjection (k+1) (ambientSphereL2 G hG x)) :=
      (harmonicProjection (k+1)).contDiff.comp (contDiff_ambientSphereL2 G hG)
    have hcov : polynomialSphereL2 (covariantPolynomialDerivative g e (E.basis k) c y (e y i)) =
        (harmonicProjection (k+1) (ambientSphereL2 H hH y) : SphereL2) := by
      rw [polynomialSphereL2_covariantDerivative hY h hK e he hframe (k+1) (E.basis k)
        (E.basisHarmonic k) c _ hc hU hcrep hy (e y i),
        harmonicProjection_horizontal_component hY h hK e he hframe φ hφ E.representative
          E.representativeSmooth E.representativeEq L hy (e y i) (ambientSphereL2 H hH y) hHL (k+1)]
    unfold weightedPolynomialDerivative weightedAngularSection
    rw [map_add,← smul_eq_C_mul,← smul_eq_C_mul,map_smul,map_smul,hcov,hcrep y,
      map_add,map_smul,map_smul,harmonicProjection_ambientDegree,hb y hys]
    simp only [Submodule.coe_add,Submodule.coe_smul,smul_smul]
    congr 1
    congr 1
    push_cast
    ring
  · have hnc : y ∉ tsupport c := fun hs => hys (hcs hs)
    have hHzero := ambientSphereL2_eq_zero H hH y (hHz y hys)
    have hGz : ∀ x ∉ E.supportSet,∀ v : UnitSphere,G (x,v.val) = 0 := by
      intro x hx v
      simp only [G,E.representativeZero x hx v,map_zero]
    have hDzero := ambientDegreeField_zero G hG E.supportSet hGz hys
    unfold weightedPolynomialDerivative weightedAngularSection
    rw [covariantPolynomialDerivative_zero_outside g e (E.basis k) c hnc,
      finitePolynomialField_zero_outside (E.basis k) c hnc,hHzero,hDzero]
    simp only [mul_zero,add_zero,map_zero,smul_zero,Submodule.coe_zero]

end ShrinkingSpheres
