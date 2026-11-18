import Proof.HorizontalProjection
import Proof.ComplexBesselSections

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial Filter
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SpectralCoreRegularity

def harmonicTruncation (g : MetricField) (e : Frame) (φ : Field) (n : ℕ) : Field :=
  fun p => ∑ k ∈ Finset.range n,degreePart g e k p.1 (fun w => φ (p.1,w)) p.2

lemma harmonicPartialSum_eq_sum (n : ℕ) (u : SphereL2) :
    harmonicPartialSum n u = ∑ k ∈ Finset.range n,(harmonicProjection k u : SphereL2) := by
  rw [harmonicPartialSum,sphereHarmonicPartialSum_apply]
  rfl

lemma harmonicProjection_ae_polynomial (k : ℕ) (u : SphereL2) :
    (harmonicProjection k u : SphereL2) =ᵐ[sphereProbability]
      (fun v : UnitSphere => eval (v.val : I → ℝ) (harmonicProjectionPolynomial k u).val) := by
  rw [← polynomialSphereL2_harmonicProjectionPolynomial]
  exact (polynomialSphere (harmonicProjectionPolynomial k u).val).coeFn_toLp (p:=2) (𝕜:=ℝ) sphereProbability

/-- The actual finite sum of frozen kernels has the canonical Hilbert partial-sum components. -/
theorem harmonicTruncation_components (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (φ : Field) (U V : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).im)) (n : ℕ) :
    (harmonicPartialSum n U =ᵐ[sphereProbability]
      (fun v : UnitSphere => (harmonicTruncation g e φ n (y,frameVector e y v.val)).re)) ∧
    (harmonicPartialSum n V =ᵐ[sphereProbability]
      (fun v : UnitSphere => (harmonicTruncation g e φ n (y,frameVector e y v.val)).im)) := by
  have hpu := sphereL2_sum_ae (Finset.range n) (fun k => (harmonicProjection k U : SphereL2))
    (fun k v => eval (v.val : I → ℝ) (harmonicProjectionPolynomial k U).val)
    (fun k _ => harmonicProjection_ae_polynomial k U)
  have hpv := sphereL2_sum_ae (Finset.range n) (fun k => (harmonicProjection k V : SphereL2))
    (fun k v => eval (v.val : I → ℝ) (harmonicProjectionPolynomial k V).val)
    (fun k _ => harmonicProjection_ae_polynomial k V)
  rw [← harmonicPartialSum_eq_sum] at hpu hpv
  constructor
  · apply hpu.trans
    apply Filter.Eventually.of_forall
    intro v
    change _ = Complex.reCLM (∑ k ∈ Finset.range n,degreePart g e k y (fun w => φ (y,w)) (frameVector e y v.val))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [degreePart_harmonicProjection_components g e y hframe _ U V hRe hIm v k]
    rfl
  · apply hpv.trans
    apply Filter.Eventually.of_forall
    intro v
    change _ = Complex.imCLM (∑ k ∈ Finset.range n,degreePart g e k y (fun w => φ (y,w)) (frameVector e y v.val))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [degreePart_harmonicProjection_components g e y hframe _ U V hRe hIm v k]
    rfl

end ShrinkingSpheres
