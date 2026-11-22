module

public import Proof.CalderonN.TruncationCoordinates
public import Proof.CalderonN.SmoothSphereFields
public import Proof.CalderonN.HorizontalProjection

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

/-- Shared genuine harmonic coordinates of one actual test. The same smooth representative,
    compact support and real/imaginary bases are used by all cutoffs and graph limits. -/
structure HarmonicTestExpansion (Y : Set (X N)) (g : (MetricField N)) (e : (Frame N)) (φ : (Field N)) where
  supportSet : Set (X N)
  compactSupportSet : IsCompact supportSet
  supportSubset : supportSet ⊆ Y
  representative : (Field N)
  representativeSmooth : ContDiff ℝ ∞ representative
  representativeEq : ∀ y ∈ Y,∀ v : (UnitSphere N),representative (y,v.val) = φ (y,frameVector e y v.val)
  representativeZero : ∀ y ∉ supportSet,∀ v : (UnitSphere N),representative (y,v.val) = 0
  meanZero : ∀ y ∈ Y,sphereAverage e y (fun w => φ (y,w)) = 0
  dimension : ℕ → ℕ
  basis : (k : ℕ) → Fin (dimension k) → MvPolynomial (I N) ℝ
  basisHarmonic : ∀ k j,basis k j ∈ harmonicHomogeneous N (k+1)
  realCoefficients : (k : ℕ) → (X N) → Fin (dimension k) → ℝ
  imagCoefficients : (k : ℕ) → (X N) → Fin (dimension k) → ℝ
  realSmooth : ∀ k,ContDiff ℝ ∞ (realCoefficients k)
  imagSmooth : ∀ k,ContDiff ℝ ∞ (imagCoefficients k)
  realSupport : ∀ k,tsupport (realCoefficients k) ⊆ supportSet
  imagSupport : ∀ k,tsupport (imagCoefficients k) ⊆ supportSet
  realCoordinates : ∀ k x,polynomialSphereL2 (finitePolynomialField (basis k) (realCoefficients k) x) =
    (harmonicProjection (k+1) (ambientSphereL2 (fun p => (representative p).re)
      (Complex.reCLM.contDiff.comp representativeSmooth) x) : (SphereL2 N))
  imagCoordinates : ∀ k x,polynomialSphereL2 (finitePolynomialField (basis k) (imagCoefficients k) x) =
    (harmonicProjection (k+1) (ambientSphereL2 (fun p => (representative p).im)
      (Complex.imCLM.contDiff.comp representativeSmooth) x) : (SphereL2 N))
  zeroDegreeReal : ∀ x,harmonicProjection 0 (ambientSphereL2 (fun p => (representative p).re)
    (Complex.reCLM.contDiff.comp representativeSmooth) x) = 0
  zeroDegreeImag : ∀ x,harmonicProjection 0 (ambientSphereL2 (fun p => (representative p).im)
    (Complex.imCLM.contDiff.comp representativeSmooth) x) = 0

theorem Test.exists_harmonicTestExpansion (hn : 3 ≤ N) {Y : Set (X N)} (hY : IsOpen Y) {g : (MetricField N)} (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field N)} (hφ : Test Y g e φ) : Nonempty (HarmonicTestExpansion Y g e φ) := by
  classical
  obtain ⟨K,hK,hKY,G,hG,hrep,hzero⟩ := hφ.exists_smooth_standard_representative hY e he hframe
  let U := ambientSphereL2 (fun p => (G p).re) (Complex.reCLM.contDiff.comp hG)
  let V := ambientSphereL2 (fun p => (G p).im) (Complex.imCLM.contDiff.comp hG)
  have hU : ContDiff ℝ ∞ U := contDiff_ambientSphereL2 _ _
  have hV : ContDiff ℝ ∞ V := contDiff_ambientSphereL2 _ _
  have hzu (x : (X N)) (hx : x ∉ K) : U x = 0 := ambientSphereL2_eq_zero _ _ x (fun v => by
    simp only [hzero x hx v,Complex.zero_re])
  have hzv (x : (X N)) (hx : x ∉ K) : V x = 0 := ambientSphereL2_eq_zero _ _ x (fun v => by
    simp only [hzero x hx v,Complex.zero_im])
  have hRe (x : (X N)) (hx : x ∈ Y) : U x =ᵐ[(unitSphereProbability N)]
      (fun v : (UnitSphere N) => (φ (x,frameVector e x v.val)).re) := by
    apply (ambientSphereL2_ae _ _ x).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.re (hrep x hx v))
  have hIm (x : (X N)) (hx : x ∈ Y) : V x =ᵐ[(unitSphereProbability N)]
      (fun v : (UnitSphere N) => (φ (x,frameVector e x v.val)).im) := by
    apply (ambientSphereL2_ae _ _ x).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.im (hrep x hx v))
  have hz (x : (X N)) : harmonicProjection 0 (U x) = 0 ∧ harmonicProjection 0 (V x) = 0 := by
    by_cases hx : x ∈ Y
    · exact hφ.harmonicProjection_zero hn x hx (U x) (V x) (hRe x hx) (hIm x hx)
    · have hn : x ∉ K := fun hk => hx (hKY hk)
      simp only [hzu x hn,hzv x hn,map_zero,and_self]
  have hex := fun k : ℕ => exists_common_harmonic_coordinates (k+1) U V hU hV K hK hzu hzv
  choose dim b c d hdata using hex
  exact ⟨{
    supportSet := K
    compactSupportSet := hK
    supportSubset := hKY
    representative := G
    representativeSmooth := hG
    representativeEq := hrep
    representativeZero := hzero
    meanZero := hφ.2.2
    dimension := dim
    basis := b
    basisHarmonic := fun k => (hdata k).1
    realCoefficients := c
    imagCoefficients := d
    realSmooth := fun k => (hdata k).2.1
    imagSmooth := fun k => (hdata k).2.2.1
    realSupport := fun k => (hdata k).2.2.2.2.2.1
    imagSupport := fun k => (hdata k).2.2.2.2.2.2.1
    realCoordinates := fun k => (hdata k).2.2.2.2.2.2.2.1
    imagCoordinates := fun k => (hdata k).2.2.2.2.2.2.2.2
    zeroDegreeReal := fun x => (hz x).1
    zeroDegreeImag := fun x => (hz x).2 }⟩

/-- The literal partial sum of the protected degree projections. -/
def harmonicTruncation (g : MetricField N) (e : Frame N) (φ : Field N) (m : ℕ) : Field N :=
  fun q => ∑ k ∈ Finset.range m, degreePart g e k q.1 (fun w => φ (q.1,w)) q.2

namespace HarmonicTestExpansion
variable {Y : Set (X N)} {g : (MetricField N)} {e : (Frame N)} {φ : (Field N)}

def realSection (E : HarmonicTestExpansion Y g e φ) : (X N) → (SphereL2 N) :=
  ambientSphereL2 (fun p => (E.representative p).re) (Complex.reCLM.contDiff.comp E.representativeSmooth)

def imagSection (E : HarmonicTestExpansion Y g e φ) : (X N) → (SphereL2 N) :=
  ambientSphereL2 (fun p => (E.representative p).im) (Complex.imCLM.contDiff.comp E.representativeSmooth)

lemma realSection_ae (E : HarmonicTestExpansion Y g e φ) {y : (X N)} (hy : y ∈ Y) :
    E.realSection y =ᵐ[(unitSphereProbability N)] (fun v : (UnitSphere N) => (φ (y,frameVector e y v.val)).re) := by
  apply (ambientSphereL2_ae _ _ y).trans
  exact Filter.Eventually.of_forall (fun v => congrArg Complex.re (E.representativeEq y hy v))

lemma imagSection_ae (E : HarmonicTestExpansion Y g e φ) {y : (X N)} (hy : y ∈ Y) :
    E.imagSection y =ᵐ[(unitSphereProbability N)] (fun v : (UnitSphere N) => (φ (y,frameVector e y v.val)).im) := by
  apply (ambientSphereL2_ae _ _ y).trans
  exact Filter.Eventually.of_forall (fun v => congrArg Complex.im (E.representativeEq y hy v))

lemma real_compact (E : HarmonicTestExpansion Y g e φ) (k : ℕ) : HasCompactSupport (E.realCoefficients k) :=
  E.compactSupportSet.of_isClosed_subset (isClosed_tsupport _) (E.realSupport k)

lemma imag_compact (E : HarmonicTestExpansion Y g e φ) (k : ℕ) : HasCompactSupport (E.imagCoefficients k) :=
  E.compactSupportSet.of_isClosed_subset (isClosed_tsupport _) (E.imagSupport k)

def mode (E : HarmonicTestExpansion Y g e φ) (k : ℕ) : (Field N) :=
  pairedPolynomialField g e (E.basis k) (E.realCoefficients k) (E.imagCoefficients k)

def partialField (E : HarmonicTestExpansion Y g e φ) (n : ℕ) : (Field N) :=
  finiteAngularField g e (Finset.range n) E.basis E.realCoefficients E.imagCoefficients

lemma mode_eq_degreePart (hn : 3 ≤ N) (E : HarmonicTestExpansion Y g e φ)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (k : ℕ) {y : (X N)} (hy : y ∈ Y) (v : (UnitSphere N)) :
    E.mode k (y,frameVector e y v.val) = degreePart g e (k+1) y (fun w => φ (y,w)) (frameVector e y v.val) :=
  pairedPolynomialField_eq_degreePart hn g e y (hframe y hy) φ (E.realSection y) (E.imagSection y)
    (E.realSection_ae hy) (E.imagSection_ae hy) (k+1) (E.basis k) (E.basisHarmonic k)
    (E.realCoefficients k) (E.imagCoefficients k) (E.realCoordinates k y) (E.imagCoordinates k y) v

lemma partial_eq_truncation (hn : 3 ≤ N) (E : HarmonicTestExpansion Y g e φ)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (n : ℕ) {y : (X N)} (hy : y ∈ Y) (v : (UnitSphere N)) :
    E.partialField n (y,frameVector e y v.val) = harmonicTruncation g e φ (n+1) (y,frameVector e y v.val) := by
  classical
  have hz : degreePart g e 0 y (fun w => φ (y,w)) (frameVector e y v.val) = 0 := by
    simpa only [degreePart,zonal,harmonicMultiplicity,Nat.cast_one,Complex.ofReal_one,one_mul] using E.meanZero y hy
  change finiteAngularField g e (Finset.range n) E.basis E.realCoefficients E.imagCoefficients _ = _
  rw [finiteAngularField_eq_sum]
  simp only [Finset.sum_apply]
  change (∑ k ∈ Finset.range n,E.mode k (y,frameVector e y v.val)) =
    ∑ k ∈ Finset.range (n+1),degreePart g e k y (fun w => φ (y,w)) (frameVector e y v.val)
  rw [Finset.sum_range_succ',hz,add_zero]
  exact Finset.sum_congr rfl (fun k _ => E.mode_eq_degreePart hn hframe k hy v)

lemma mode_horizontal_eq_degreePart (E : HarmonicTestExpansion Y g e φ) (hn : 3 ≤ N)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (k : ℕ) {y : (X N)} (hy : y ∈ Y) (a : (X N)) (HRe HIm : (SphereL2 N))
    (hHRe : HRe =ᵐ[(sphereProbability N)] (fun v : (UnitSphere N) => (horizontal g φ y (frameVector e y v.val) a).re))
    (hHIm : HIm =ᵐ[(sphereProbability N)] (fun v : (UnitSphere N) => (horizontal g φ y (frameVector e y v.val) a).im))
    (v : (UnitSphere N)) :
    horizontal g (E.mode k) y (frameVector e y v.val) a =
      degreePart g e (k+1) y (fun w => horizontal g φ y w a) (frameVector e y v.val) :=
  horizontal_projection_commutes hn hY h hK e he hframe φ hφ E.representative E.representativeSmooth E.representativeEq
    (by omega : 1 ≤ k+1) (E.basis k) (E.basisHarmonic k) (E.realCoefficients k) (E.imagCoefficients k)
    (E.realSmooth k) (E.imagSmooth k) (E.realCoordinates k) (E.imagCoordinates k) hy a HRe HIm hHRe hHIm v

lemma horizontal_zeroDegree_component (E : HarmonicTestExpansion Y g e φ)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (L : ℂ →L[ℝ] ℝ)
    (hz : ∀ x,harmonicProjection 0 (ambientSphereL2 (fun p => L (E.representative p))
      (L.contDiff.comp E.representativeSmooth) x) = 0)
    {y : (X N)} (hy : y ∈ Y) (a : (X N)) (H : (SphereL2 N))
    (hH : H =ᵐ[(sphereProbability N)] (fun v : (UnitSphere N) => L (horizontal g φ y (frameVector e y v.val) a))) :
    harmonicProjection 0 H = 0 := by
  rw [harmonicProjection_horizontal_component hY h hK e he hframe φ hφ E.representative
    E.representativeSmooth E.representativeEq L hy a H hH 0]
  have hf : (fun x => harmonicProjection 0 (ambientSphereL2 (fun p => L (E.representative p))
      (L.contDiff.comp E.representativeSmooth) x)) = (fun _ : (X N) => (0 : harmonicSphereSubspace N 0)) := funext hz
  rw [hf]
  simp only [harmonicCovariantDerivative,fderiv_const_apply,zero_apply,map_zero,smul_zero,
    Finset.sum_const_zero,add_zero]

end HarmonicTestExpansion

end CalderonN
