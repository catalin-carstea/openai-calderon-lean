import Proof.TruncationSmoothness
import Proof.SphereBundleCongruence
import Proof.TestHarmonicCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma pairedPolynomialField_eq_degreePart (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (φ : Field) (U V : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).im))
    {ι : Type*} [Fintype ι] (k : ℕ) (b : ι → MvPolynomial I ℝ)
    (hb : ∀ j,b j ∈ harmonicHomogeneous k) (c d : X → ι → ℝ)
    (hc : polynomialSphereL2 (finitePolynomialField b c y) = (harmonicProjection k U : SphereL2))
    (hd : polynomialSphereL2 (finitePolynomialField b d y) = (harmonicProjection k V : SphereL2)) (v : UnitSphere) :
    pairedPolynomialField g e b c d (y,frameVector e y v.val) =
      degreePart g e k y (fun w => φ (y,w)) (frameVector e y v.val) := by
  rw [degreePart_harmonicProjection_components g e y hframe _ U V hRe hIm v k,
    harmonicProjectionPolynomial_eq_of_Lp k U _ (finitePolynomialField_harmonicHomogeneous k b hb c y) hc,
    harmonicProjectionPolynomial_eq_of_Lp k V _ (finitePolynomialField_harmonicHomogeneous k b hb d y) hd]
  exact movingFrameComplexPolynomial_frameVector g e y hframe _ _ v.val

lemma Test.degreePart_zero {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}
    (hφ : Test Y g e φ) {y : X} (hy : y ∈ Y) (w : X) :
    degreePart g e 0 y (fun v => φ (y,v)) w = 0 := by
  simpa only [degreePart,legendre,Nat.cast_zero,mul_zero,zero_add,Complex.ofReal_one,one_mul] using hφ.2.2 y hy

lemma smoothNear_finiteAngularField {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    {α : Type*} {ι : α → Type*} [∀ i,Fintype (ι i)] (s : Finset α)
    (b : (i : α) → ι i → MvPolynomial I ℝ) (c d : (i : α) → X → ι i → ℝ)
    (hc : ∀ i ∈ s,ContDiffOn ℝ ∞ (c i) Y) (hd : ∀ i ∈ s,ContDiffOn ℝ ∞ (d i) Y) :
    smoothNear (finiteAngularField g e s b c d) (bundle Y g) := by
  refine ⟨Prod.fst ⁻¹' Y,hY.preimage continuous_fst,fun p hp => hp.1,?_⟩
  rw [finiteAngularField_eq_sum]
  intro p hp
  have hfun : (∑ i ∈ s,pairedPolynomialField g e (b i) (c i) (d i)) =
      (fun q => ∑ i ∈ s,pairedPolynomialField g e (b i) (c i) (d i) q) := by
    funext q
    simp only [Finset.sum_apply]
  rw [hfun]
  exact (ContDiffAt.sum (fun i hi => contDiffAt_pairedPolynomialField hY h e he (b i) (c i) (d i)
    (hc i hi) (hd i hi) hp p.2)).contDiffWithinAt

/-- One common compact support and actual harmonic coordinates in each degree realize all
    literal truncations of an admitted mean-zero test as finite angular fields. -/
theorem Test.exists_truncation_coordinates {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) :
    ∃ K : Set X,IsCompact K ∧ K ⊆ Y ∧ ∃ dim : ℕ → ℕ,
      ∃ b : (k : ℕ) → Fin (dim k) → MvPolynomial I ℝ,
      ∃ c d : (k : ℕ) → X → Fin (dim k) → ℝ,
        (∀ k,(∀ j,b k j ∈ harmonicHomogeneous (k+1)) ∧ ContDiff ℝ ∞ (c k) ∧ ContDiff ℝ ∞ (d k) ∧
          HasCompactSupport (c k) ∧ HasCompactSupport (d k) ∧ tsupport (c k) ⊆ K ∧ tsupport (d k) ⊆ K) ∧
        ∀ n,∀ y ∈ Y,∀ v : UnitSphere,
          finiteAngularField g e (Finset.range n) b c d (y,frameVector e y v.val) =
            harmonicTruncation g e φ (n+1) (y,frameVector e y v.val) := by
  classical
  obtain ⟨K,U,V,hK,hKY,hU,hV,hcompU,hcompV,hzeroU,hzeroV,hRe,hIm,hcoords⟩ :=
    hφ.exists_harmonic_coordinate_fields hY e he hframe
  have hex := fun k : ℕ => hcoords (k+1)
  choose dim b c d hdata using hex
  refine ⟨K,hK,hKY,dim,b,c,d,?_,?_⟩
  · intro k
    obtain ⟨hb,hc,hd,hcc,hcd,hsc,hsd,hcrep,hdrep⟩ := hdata k
    exact ⟨hb,hc,hd,hcc,hcd,hsc,hsd⟩
  · intro n y hy v
    rw [finiteAngularField_eq_sum]
    simp only [Finset.sum_apply]
    change (∑ k ∈ Finset.range n,pairedPolynomialField g e (b k) (c k) (d k) (y,frameVector e y v.val)) =
      ∑ k ∈ Finset.range (n+1),degreePart g e k y (fun w => φ (y,w)) (frameVector e y v.val)
    rw [Finset.sum_range_succ',hφ.degreePart_zero hy,add_zero]
    apply Finset.sum_congr rfl
    intro k _
    obtain ⟨hb,hc,hd,hcc,hcd,hsc,hsd,hcrep,hdrep⟩ := hdata k
    exact pairedPolynomialField_eq_degreePart g e y (hframe y hy) φ (U y) (V y) (hRe y hy) (hIm y hy)
      (k+1) (b k) hb (c k) (d k) (hcrep y) (hdrep y) v

end ShrinkingSpheres
