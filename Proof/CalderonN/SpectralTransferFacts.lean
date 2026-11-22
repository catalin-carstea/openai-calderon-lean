module

public import Proof.CalderonN.FiberEnergy
public import Proof.CalderonN.SmoothEnergyRegularity

import Proof.CalderonN.SmoothZonalSobolev
import Mathlib.Tactic

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace CalderonN

open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ} [NeZero n]

theorem Test.spectralTransferFacts (hn : 3 ≤ n) {Y : Set (X n)} (hY : IsOpen Y)
    (d : Data n) {K floor c₀ : ℝ} {Cj : Fin 9 → ℝ}
    (hγ : Elliptic Y K d.γ) (hK : 0 < K)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i = j then 1 else 0)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun y => d.frame y i) Y)
    (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj) (hfloor : 1 ≤ floor)
    {φ : Field n} (hφ : Test Y d.γ d.frame φ) :
    (∀ y ∈ Y, sobolevSq d.γ d.frame 0 y (fun w => φ (y,w)) = fiberSq d.frame y (fun w => φ (y,w))) ∧
    (∀ y ∈ Y, Summable (fun k : ℕ => (1+(k:ℝ))^(2*(1:ℝ)) *
      fiberSq d.frame y (degreePart d.γ d.frame k y (fun w => φ (y,w))))) ∧
    IntegrableOn (sphereEnergyDensity d φ) Y := by
  obtain ⟨_,_,_,H,hH,hrep,_⟩ := exists_smooth_standard_representative_of_support hY d.frame he hframe hφ.1 hφ.2.1
  have hRep (y : X n) (hy : y ∈ Y) :
      ∃ U V : SphereL2 n,
        (U =ᵐ[unitSphereProbability n] fun v : UnitSphere n => (φ (y,frameVector d.frame y v.val)).re) ∧
        (V =ᵐ[unitSphereProbability n] fun v : UnitSphere n => (φ (y,frameVector d.frame y v.val)).im) ∧
        Summable (fun k : ℕ => (1+(k:ℝ))^(2*(1:ℝ)) *
          (‖harmonicProjection k U‖^2 + ‖harmonicProjection k V‖^2)) := by
    let R (z : X n) := (H (y,z)).re
    let J (z : X n) := (H (y,z)).im
    have hS : ContDiff ℝ ∞ (fun z : X n => H (y,z)) :=
      hH.comp (contDiff_const.prodMk contDiff_id)
    have hR : ContDiff ℝ ∞ R := Complex.reCLM.contDiff.comp hS
    have hJ : ContDiff ℝ ∞ J := Complex.imCLM.contDiff.comp hS
    refine ⟨smoothSphereLift R hR,smoothSphereLift J hJ,?_,?_,?_⟩
    · exact (smoothSphereLift_ae R hR).trans (Filter.Eventually.of_forall fun w => congrArg Complex.re (hrep y hy w))
    · exact (smoothSphereLift_ae J hJ).trans (Filter.Eventually.of_forall fun w => congrArg Complex.im (hrep y hy w))
    · simpa only [mul_add, mul_one, Real.rpow_two] using
        ((summable_smooth_angular_weight_all hn 2 R hR).add (summable_smooth_angular_weight_all hn 2 J hJ))
  refine ⟨?_,?_,hp.integrableOn_physicalEnergyDensity hn hY hγ hK d.frame he hframe hfloor hφ⟩
  · intro y hy
    obtain ⟨U,V,hU,hV,_⟩ := hRep y hy
    exact sobolevSq_zero_eq_fiberSq_components hn d.γ d.frame y (hframe y hy) _ U V hU hV
  · intro y hy
    obtain ⟨U,V,hU,hV,hUV⟩ := hRep y hy
    simpa only [fiberSq_degreePart_harmonicProjection_components hn d.γ d.frame y (hframe y hy) (fun w => φ (y,w)) U V hU hV]
      using hUV

end CalderonN
