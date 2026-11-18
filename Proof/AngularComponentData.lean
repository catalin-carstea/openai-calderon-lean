import Proof.PhysicalAngularModelData
import Proof.PolynomialOutputIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

/-- One real linear component of the physical complex model, using the expansion's actual
    harmonic basis and compact support. Real and imaginary components share their radius data. -/
structure AngularComponentData {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}
    (E : HarmonicTestExpansion Y g e φ) (r : X → ℝ) (L : ℂ →L[ℝ] ℝ) where
  horizontalRepresentative : I → X × X → ℝ
  horizontalSmooth : ∀ i,ContDiff ℝ ∞ (horizontalRepresentative i)
  horizontalEq : ∀ i,∀ y ∈ Y,∀ v : UnitSphere,horizontalRepresentative i (y,v.val) = L (horizontal g φ y (frameVector e y v.val) (e y i))
  horizontalZero : ∀ i,∀ y ∉ E.supportSet,∀ v : UnitSphere,horizontalRepresentative i (y,v.val) = 0
  coefficient : I → X → ℝ
  coefficientSmooth : ∀ i,ContDiff ℝ ∞ (coefficient i)
  coefficientEq : ∀ i,∀ y ∈ E.supportSet,coefficient i y = fderiv ℝ (fun x => Real.log (r x)) y (e y i)
  coordinates : (k : ℕ) → X → Fin (E.dimension k) → ℝ
  coordinatesSmooth : ∀ k,ContDiff ℝ ∞ (coordinates k)
  coordinatesSupport : ∀ k,tsupport (coordinates k) ⊆ E.supportSet
  coordinatesEq : ∀ k x,polynomialSphereL2 (finitePolynomialField (E.basis k) (coordinates k) x) =
    (harmonicProjection (k+1) (ambientSphereL2 (fun p => L (E.representative p))
      (L.contDiff.comp E.representativeSmooth) x) : SphereL2)
  zeroDegree : ∀ x,harmonicProjection 0 (ambientSphereL2 (fun p => L (E.representative p))
    (L.contDiff.comp E.representativeSmooth) x) = 0

namespace AngularModelData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ} {r : X → ℝ}

def realComponent (D : AngularModelData E r) : AngularComponentData E r Complex.reCLM where
  horizontalRepresentative := D.realHorizontal
  horizontalSmooth := D.realSmooth
  horizontalEq := by intro i y hy v; simpa only [Complex.reCLM_apply] using D.realEq i y hy v
  horizontalZero := D.realZero
  coefficient := D.coefficient
  coefficientSmooth := D.coefficientSmooth
  coefficientEq := D.coefficientEq
  coordinates := E.realCoefficients
  coordinatesSmooth := E.realSmooth
  coordinatesSupport := E.realSupport
  coordinatesEq := by intro k x; simpa only [Complex.reCLM_apply] using E.realCoordinates k x
  zeroDegree := by intro x; simpa only [Complex.reCLM_apply] using E.zeroDegreeReal x

def imagComponent (D : AngularModelData E r) : AngularComponentData E r Complex.imCLM where
  horizontalRepresentative := D.imagHorizontal
  horizontalSmooth := D.imagSmooth
  horizontalEq := by intro i y hy v; simpa only [Complex.imCLM_apply] using D.imagEq i y hy v
  horizontalZero := D.imagZero
  coefficient := D.coefficient
  coefficientSmooth := D.coefficientSmooth
  coefficientEq := D.coefficientEq
  coordinates := E.imagCoefficients
  coordinatesSmooth := E.imagSmooth
  coordinatesSupport := E.imagSupport
  coordinatesEq := by intro k x; simpa only [Complex.imCLM_apply] using E.imagCoordinates k x
  zeroDegree := by intro x; simpa only [Complex.imCLM_apply] using E.zeroDegreeImag x

lemma realComponent_coordinates (D : AngularModelData E r) : D.realComponent.coordinates = E.realCoefficients := rfl
lemma imagComponent_coordinates (D : AngularModelData E r) : D.imagComponent.coordinates = E.imagCoefficients := rfl

end AngularModelData

namespace AngularComponentData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ}
  {r : X → ℝ} {L : ℂ →L[ℝ] ℝ}

def raisingOutput (Q : AngularComponentData E r L) : X → SphereL2 :=
  angularRaisingSum Q.horizontalRepresentative (fun p => L (E.representative p)) Q.horizontalSmooth
    (L.contDiff.comp E.representativeSmooth) Q.coefficient

def loweringOutput (Q : AngularComponentData E r L) : X → SphereL2 :=
  angularLoweringSum Q.horizontalRepresentative (fun p => L (E.representative p)) Q.horizontalSmooth
    (L.contDiff.comp E.representativeSmooth) Q.coefficient

lemma source_zero (Q : AngularComponentData E r L) :
    ∀ y ∉ E.supportSet,∀ v : UnitSphere,L (E.representative (y,v.val)) = 0 := by
  intro y hy v
  rw [E.representativeZero y hy v,map_zero]

lemma contDiff_raisingOutput (Q : AngularComponentData E r L) : ContDiff ℝ ∞ Q.raisingOutput :=
  contDiff_angularRaisingSum _ _ Q.horizontalSmooth _ _ Q.coefficientSmooth

lemma contDiff_loweringOutput (Q : AngularComponentData E r L) : ContDiff ℝ ∞ Q.loweringOutput :=
  contDiff_angularLoweringSum _ _ Q.horizontalSmooth _ _ Q.coefficientSmooth

lemma raisingOutput_zero (Q : AngularComponentData E r L) {y : X} (hy : y ∉ E.supportSet) : Q.raisingOutput y = 0 :=
  angularRaisingSum_zero _ _ Q.horizontalSmooth _ _ E.supportSet Q.horizontalZero Q.source_zero hy

lemma loweringOutput_zero (Q : AngularComponentData E r L) {y : X} (hy : y ∉ E.supportSet) : Q.loweringOutput y = 0 :=
  angularLoweringSum_zero _ _ Q.horizontalSmooth _ _ E.supportSet Q.horizontalZero Q.source_zero hy

lemma raisingOutput_compact (Q : AngularComponentData E r L) : HasCompactSupport Q.raisingOutput :=
  HasCompactSupport.intro E.compactSupportSet (fun y hy => Q.raisingOutput_zero hy)

lemma loweringOutput_compact (Q : AngularComponentData E r L) : HasCompactSupport Q.loweringOutput :=
  HasCompactSupport.intro E.compactSupportSet (fun y hy => Q.loweringOutput_zero hy)

lemma weighted_polynomial_L2 (Q : AngularComponentData E r L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (k : ℕ) (i : I) (s : ℝ) {y : X} (hy : y ∈ Y) :
    polynomialSphereL2 (weightedFramePolynomialField g e (E.basis k) (Q.coordinates k)
      (fun x => Real.log (r x)) (k+1) s y i) =
      (harmonicProjection (k+1) (weightedAngularSection (Q.horizontalRepresentative i) (fun p => L (E.representative p))
        (Q.horizontalSmooth i) (L.contDiff.comp E.representativeSmooth) (Q.coefficient i) s y) : SphereL2) :=
  polynomialSphereL2_weighted_coordinates hY h hK e he hframe hφ E r L (Q.horizontalRepresentative i)
    (Q.horizontalSmooth i) i k (Q.coordinates k) (Q.coordinatesSmooth k) (Q.coordinatesSupport k)
    (Q.coordinatesEq k) (Q.horizontalEq i) (Q.horizontalZero i) (Q.coefficient i) (Q.coefficientEq i) s hy

lemma raised_polynomial_L2 (Q : AngularComponentData E r L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (k : ℕ) {y : X} (hy : y ∈ Y) :
    polynomialSphereL2 (raisedPolynomialField g e (E.basis k) (Q.coordinates k)
      (fun x => Real.log (r x)) k y) = (harmonicProjection (k+2) (Q.raisingOutput y) : SphereL2) :=
  polynomialSphereL2_raised_eq_projection hY h hK e he hframe k (E.basis k) (E.basisHarmonic k)
    (Q.coordinates k) _ Q.horizontalRepresentative _ Q.horizontalSmooth _ Q.coefficient hy
    (fun i => Q.weighted_polynomial_L2 hY h hK he hframe hφ k i 1 hy)

lemma lowered_polynomial_L2 (Q : AngularComponentData E r L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (k : ℕ) {y : X} (hy : y ∈ Y) :
    polynomialSphereL2 (loweredPolynomialField g e (E.basis k) (Q.coordinates k)
      (fun x => Real.log (r x)) k y) = (harmonicProjection k (Q.loweringOutput y) : SphereL2) :=
  polynomialSphereL2_lowered_eq_projection hY h hK e he hframe k (E.basis k) (E.basisHarmonic k)
    (Q.coordinates k) _ Q.horizontalRepresentative _ Q.horizontalSmooth _ Q.coefficient hy
    (fun i => Q.weighted_polynomial_L2 hY h hK he hframe hφ k i (-1) hy)

lemma raisingOutput_zeroDegree (Q : AngularComponentData E r L) (y : X) : harmonicProjection 0 (Q.raisingOutput y) = 0 :=
  harmonicProjection_angularRaisingSum_zero _ _ Q.horizontalSmooth _ Q.coefficient y

lemma raisingOutput_firstDegree (Q : AngularComponentData E r L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) {y : X} (hy : y ∈ Y) : harmonicProjection 1 (Q.raisingOutput y) = 0 := by
  unfold raisingOutput
  rw [show (1:ℕ) = 0+1 by omega,harmonicProjection_angularRaisingSum_succ]
  have hh (i : I) : harmonicProjection 0 (weightedAngularSection (Q.horizontalRepresentative i) (fun p => L (E.representative p))
      (Q.horizontalSmooth i) (L.contDiff.comp E.representativeSmooth) (Q.coefficient i) 1 y) = 0 := by
    have hAE : ambientSphereL2 (Q.horizontalRepresentative i) (Q.horizontalSmooth i) y =ᵐ[sphereProbability]
        (fun v : UnitSphere => L (horizontal g φ y (frameVector e y v.val) (e y i))) := by
      apply (ambientSphereL2_ae _ _ y).trans
      exact Filter.Eventually.of_forall (fun v => Q.horizontalEq i y hy v)
    have hz := E.horizontal_zeroDegree_component hY h hK he hframe hφ L Q.zeroDegree hy (e y i) _ hAE
    rw [weightedAngularSection,map_add,map_smul,map_smul,hz,harmonicProjection_ambientDegree]
    simp only [Nat.cast_zero,zero_smul,add_zero,smul_zero]
  simp_rw [hh,map_zero]
  exact Finset.sum_const_zero

lemma raising_sum_partial (Q : AngularComponentData E r L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (n : ℕ) {y : X} (hy : y ∈ Y) :
    polynomialSphereL2 (∑ k ∈ Finset.range n,raisedPolynomialField g e (E.basis k) (Q.coordinates k)
      (fun x => Real.log (r x)) k y) = harmonicPartialSum (n+2) (Q.raisingOutput y) := by
  rw [map_sum,harmonicPartialSum_eq_shift_two (n:=n) _ (Q.raisingOutput_zeroDegree y)
    (Q.raisingOutput_firstDegree hY h hK he hframe hφ hy)]
  exact Finset.sum_congr rfl (fun k _ => Q.raised_polynomial_L2 hY h hK he hframe hφ k hy)

lemma lowering_sum_partial (Q : AngularComponentData E r L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (n : ℕ) {y : X} (hy : y ∈ Y) :
    polynomialSphereL2 (∑ k ∈ Finset.range n,loweredPolynomialField g e (E.basis k) (Q.coordinates k)
      (fun x => Real.log (r x)) k y) = harmonicPartialSum n (Q.loweringOutput y) := by
  rw [map_sum,harmonicPartialSum_eq_sum]
  exact Finset.sum_congr rfl (fun k _ => Q.lowered_polynomial_L2 hY h hK he hframe hφ k hy)

end AngularComponentData
end ShrinkingSpheres
