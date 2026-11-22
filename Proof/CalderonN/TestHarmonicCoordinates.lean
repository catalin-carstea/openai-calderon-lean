module

public import Proof.CalderonN.TestRepresentative
public import Proof.CalderonN.HarmonicCoordinateFields

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

/-- Every actual local compact test gives smooth compact real and imaginary L2 sections,
    and each harmonic projection has common smooth compact finite polynomial coordinates.
    The equalities with the original physical test use its actual moving frame. -/
theorem Test.exists_harmonic_coordinate_fields {Y : Set (X N)} (hY : IsOpen Y) {g : (MetricField N)} (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field N)} (hφ : Test Y g e φ) :
    ∃ K : Set (X N),∃ U V : (X N) → (SphereL2 N),IsCompact K ∧ K ⊆ Y ∧
      ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧ HasCompactSupport U ∧ HasCompactSupport V ∧
      (∀ y ∉ K,U y = 0) ∧ (∀ y ∉ K,V y = 0) ∧
      (∀ y ∈ Y,U y =ᵐ[unitSphereProbability N] (fun v : (UnitSphere N) => (φ (y,frameVector e y v.val)).re)) ∧
      (∀ y ∈ Y,V y =ᵐ[unitSphereProbability N] (fun v : (UnitSphere N) => (φ (y,frameVector e y v.val)).im)) ∧
      ∀ k : ℕ,∃ n : ℕ,∃ b : Fin n → MvPolynomial (I N) ℝ,∃ c d : (X N) → Fin n → ℝ,
        (∀ j,b j ∈ harmonicHomogeneous N k) ∧ ContDiff ℝ ∞ c ∧ ContDiff ℝ ∞ d ∧
        HasCompactSupport c ∧ HasCompactSupport d ∧ tsupport c ⊆ K ∧ tsupport d ⊆ K ∧
        (∀ x,polynomialSphereL2 (finitePolynomialField b c x) = (harmonicProjection k (U x) : (SphereL2 N))) ∧
        (∀ x,polynomialSphereL2 (finitePolynomialField b d x) = (harmonicProjection k (V x) : (SphereL2 N))) := by
  obtain ⟨K,hK,hKY,G,hG,hrep,hGzero⟩ := hφ.exists_smooth_standard_representative hY e he hframe
  let Gre : (X N) × (X N) → ℝ := fun z => (G z).re
  let Gim : (X N) × (X N) → ℝ := fun z => (G z).im
  have hGre : ContDiff ℝ ∞ Gre := Complex.reCLM.contDiff.comp hG
  have hGim : ContDiff ℝ ∞ Gim := Complex.imCLM.contDiff.comp hG
  let U := ambientSphereL2 Gre hGre
  let V := ambientSphereL2 Gim hGim
  have hU : ContDiff ℝ ∞ U := contDiff_ambientSphereL2 Gre hGre
  have hV : ContDiff ℝ ∞ V := contDiff_ambientSphereL2 Gim hGim
  have hzeroU (y : (X N)) (hy : y ∉ K) : U y = 0 :=
    ambientSphereL2_eq_zero Gre hGre y (fun v => by simp only [Gre,hGzero y hy v,Complex.zero_re])
  have hzeroV (y : (X N)) (hy : y ∉ K) : V y = 0 :=
    ambientSphereL2_eq_zero Gim hGim y (fun v => by simp only [Gim,hGzero y hy v,Complex.zero_im])
  refine ⟨K,U,V,hK,hKY,hU,hV,HasCompactSupport.intro hK hzeroU,HasCompactSupport.intro hK hzeroV,hzeroU,hzeroV,?_,?_,?_⟩
  · intro y hy
    apply (ambientSphereL2_ae Gre hGre y).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.re (hrep y hy v))
  · intro y hy
    apply (ambientSphereL2_ae Gim hGim y).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.im (hrep y hy v))
  · intro k
    exact exists_common_harmonic_coordinates k U V hU hV K hK hzeroU hzeroV

end CalderonN
