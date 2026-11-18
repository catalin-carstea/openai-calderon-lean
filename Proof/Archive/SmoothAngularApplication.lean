/- Adopted from the selected ZIP, lean/Calderon/SmoothAngularApplication.lean.
   Initial generic Bessel graph, smoothness and compact-support lemmas before memLp_ambientBesselField; specialized reference-density applications omitted, proof bodies preserved.
-/
import Proof.Archive.SmoothAmbientAngularCasimir
import Proof.Archive.BoundedSpectralMultiplier

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.SmoothAngularApplication
open SphereHarmonic SmoothSphereFields SmoothAmbientAngularCasimir
  SpectralCoreRegularity SpectralWeightedGraph SpectralWeightComparison
  BoundedSpectralMultiplier

def ambientShiftedCasimirField (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  ambientSphereL2 (ambientShiftedAngularCasimirIterate 1 G)
    (contDiff_ambientShiftedAngularCasimirIterate 1 G hG)

def ambientBesselField (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : s ≤ 2) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => casimirBesselMultiplier hO hD s hs (ambientShiftedCasimirField G hG x)

theorem ambientShiftedCasimirField_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x,ambientShiftedCasimirField G hG x) ∈
      spectralGraph hO hD casimirWeight := by
  intro k
  simpa only [ambientShiftedCasimirField,pow_one,casimirWeight] using
    sphereHarmonicCoordinate_angularCasimirLift hO hD 1 k G hG x

theorem ambientBesselField_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    (ambientSphereL2 G hG x,ambientBesselField hO hD s hs G hG x) ∈
      sphereBesselGraph hO hD s :=
  casimirBesselMultiplier_graph hO hD s hs _ _ (ambientShiftedCasimirField_graph hO hD G hG x)

lemma contDiff_ambientBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientBesselField hO hD s hs G hG) :=
  contDiff_casimirBesselMultiplier hO hD s hs _ (contDiff_angularCasimirLift 1 G hG)

lemma ambientBesselField_eq_zero (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (x : R3) (hx : x ∉ K) :
    ambientBesselField hO hD s hs G hG x = 0 := by
  have he : ambientShiftedCasimirField G hG x = 0 :=
    ambientSphereL2_eq_zero _ (contDiff_ambientShiftedAngularCasimirIterate 1 G hG) x
      (ambientShiftedAngularCasimirIterate_sphere_zero 1 G hG K hz x hx)
  change casimirBesselMultiplier hO hD s hs (ambientShiftedCasimirField G hG x) = 0
  rw [he,map_zero]

lemma hasCompactSupport_ambientBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    HasCompactSupport (ambientBesselField hO hD s hs G hG) :=
  hasCompactSupport_casimirBesselMultiplier hO hD s hs _
    (hasCompactSupport_angularCasimirLift 1 G hG K hK hz)

lemma tsupport_ambientBesselField_subset (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) :
    tsupport (ambientBesselField hO hD s hs G hG) ⊆ K := by
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hxK
  change ambientBesselField hO hD s hs G hG x ≠ 0 at hx
  exact hx (ambientBesselField_eq_zero hO hD s hs G hG K hz x hxK)

lemma tsupport_pureDerivative_ambientBesselField_subset (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (X : R3) :
    tsupport (fun x => fderiv ℝ (ambientBesselField hO hD s hs G hG) x X) ⊆ K :=
  (tsupport_fderiv_apply_subset ℝ X).trans
    (tsupport_ambientBesselField_subset hO hD s hs G hG K hK hz)

lemma tsupport_secondPureDerivative_ambientBesselField_subset (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ u : UnitSphere, G (x,u.val)=0) (X Y : R3) :
    tsupport (fun x => fderiv ℝ (fun y => fderiv ℝ (ambientBesselField hO hD s hs G hG) y X) x Y) ⊆ K :=
  (tsupport_fderiv_apply_subset ℝ Y).trans
    (tsupport_pureDerivative_ambientBesselField_subset hO hD s hs G hG K hK hz X)

lemma fderiv_ambientBesselField (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (s : ℝ) (hs : s ≤ 2)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    fderiv ℝ (ambientBesselField hO hD s hs G hG) x =
      (casimirBesselMultiplier hO hD s hs).comp (fderiv ℝ (ambientShiftedCasimirField G hG) x) :=
  fderiv_casimirBesselMultiplier hO hD s hs _ x
    ((contDiff_angularCasimirLift 1 G hG).differentiable (by simp) x)


end OAI.AnisotropicCalderon.SmoothAngularApplication
