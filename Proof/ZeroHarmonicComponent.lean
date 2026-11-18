import Proof.ComplexHilbertProjection

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.HarmonicSampling

lemma harmonicProjection_zero_of_integral_zero (u : SphereL2)
    (hu : (∫ v : UnitSphere,u v ∂sphereProbability) = 0) : harmonicProjection 0 u = 0 := by
  have hp : (harmonicProjectionPolynomial 0 u).val = 0 := by
    apply harmonicPolynomial_eq_zero_of_sphere sphereFischerInner 0 _
      (harmonicProjectionPolynomial 0 u).property
    intro v
    have h := sphere_legendre_projection_Lp v 0 u
    simpa [legendre,hu] using h.symm
  apply Subtype.ext
  change (harmonicProjection 0 u : SphereL2) = 0
  rw [← polynomialSphereL2_harmonicProjectionPolynomial,hp,map_zero]

/-- The actual physical mean-zero condition removes the degree-zero component of both
    Hilbert sections. All integrability here comes from L2 on the probability sphere. -/
theorem Test.harmonicProjection_zero {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}
    (hφ : Test Y g e φ) (y : X) (hy : y ∈ Y) (U V : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).im)) :
    harmonicProjection 0 U = 0 ∧ harmonicProjection 0 V = 0 := by
  have hiU : Integrable U sphereProbability := (Lp.memLp U).integrable (by norm_num)
  have hiV : Integrable V sphereProbability := (Lp.memLp V).integrable (by norm_num)
  have heq : (∫ v : UnitSphere,Complex.mk (U v) (V v) ∂sphereProbability) = 0 := by
    calc
      _ = ∫ v : UnitSphere,φ (y,frameVector e y v.val) ∂sphereProbability := by
        apply integral_congr_ae
        filter_upwards [hRe,hIm] with v hr hi
        apply Complex.ext <;> assumption
      _ = 0 := hφ.2.2 y hy
  rw [integral_complexMk_of_integrable hiU hiV] at heq
  exact ⟨harmonicProjection_zero_of_integral_zero U (congrArg Complex.re heq),
    harmonicProjection_zero_of_integral_zero V (congrArg Complex.im heq)⟩

/-- Local tests have globally mean-zero Hilbert representatives, including outside Y. -/
theorem Test.exists_meanZero_hilbert_sections {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) :
    ∃ K : Set X,∃ U V : X → SphereL2,IsCompact K ∧ K ⊆ Y ∧
      ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧ HasCompactSupport U ∧ HasCompactSupport V ∧
      (∀ y ∉ K,U y = 0) ∧ (∀ y ∉ K,V y = 0) ∧
      (∀ y ∈ Y,U y =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).re)) ∧
      (∀ y ∈ Y,V y =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).im)) ∧
      ∀ y,harmonicProjection 0 (U y) = 0 ∧ harmonicProjection 0 (V y) = 0 := by
  obtain ⟨K,U,V,hK,hKY,hU,hV,hcu,hcv,hzu,hzv,hRe,hIm,_⟩ :=
    hφ.exists_harmonic_coordinate_fields hY e he hframe
  refine ⟨K,U,V,hK,hKY,hU,hV,hcu,hcv,hzu,hzv,hRe,hIm,?_⟩
  intro y
  by_cases hy : y ∈ Y
  · exact hφ.harmonicProjection_zero y hy (U y) (V y) (hRe y hy) (hIm y hy)
  · have hn : y ∉ K := fun hk => hy (hKY hk)
    simp only [hzu y hn,hzv y hn,map_zero,and_self]

end ShrinkingSpheres
