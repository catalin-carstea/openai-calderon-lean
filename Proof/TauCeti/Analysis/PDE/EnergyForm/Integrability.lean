/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.PDE.EnergyForm.Measurability
public import Mathlib.MeasureTheory.Integral.IntegrableOn

 



























public section

namespace TauCeti

namespace PDE

open Matrix MeasureTheory
open scoped InnerProductSpace

variable {α n : Type*} [MeasurableSpace α] [Fintype n]
variable {μ : Measure α}

 

noncomputable local instance energyFormIntegrabilityDecidableEq : DecidableEq n :=
  Classical.decEq n

 

lemma integrable_energyIntegrand_apply₂_of_integrable_norm_mul
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {U V : α → ℝ × EuclideanSpace ℝ n} {Lam beta gamma : ℝ} (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x => ‖U x‖ * ‖V x‖) μ) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ := by
  refine (hUV.const_mul (Lam + beta + gamma)).mono'
    (aestronglyMeasurable_energyIntegrand_apply₂ ha hb hc hU hV) ?_
  filter_upwards [ha_bound, hb_bound, hc_bound] with x hA hb₀ hc₀
  simpa [mul_assoc] using norm_energyIntegrand_apply_le_of_bounds hLam hA hb₀ hc₀ (U x) (V x)

 

lemma integrable_energyIntegrand_apply₂_of_memLp_two
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {U V : α → ℝ × EuclideanSpace ℝ n} {Lam beta gamma : ℝ} (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ :=
  integrable_energyIntegrand_apply₂_of_integrable_norm_mul hLam ha hb hc
    hU.aestronglyMeasurable hV.aestronglyMeasurable ha_bound hb_bound hc_bound
    (hU.norm.integrable_mul hV.norm)

 

lemma integrable_energyIntegrand_apply₂_of_bounds [IsFiniteMeasure μ]
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {U V : α → ℝ × EuclideanSpace ℝ n} {Lam beta gamma R S : ℝ} (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hU_bound : ∀ᵐ x ∂μ, ‖U x‖ ≤ R)
    (hV_bound : ∀ᵐ x ∂μ, ‖V x‖ ≤ S) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ := by
  refine integrable_energyIntegrand_apply₂_of_integrable_norm_mul hLam ha hb hc hU hV ha_bound
    hb_bound hc_bound ?_
  refine Integrable.of_bound (hU.norm.mul hV.norm) (R * S) ?_
  filter_upwards [hU_bound, hV_bound] with x hUx hVx
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hR : 0 ≤ R := (norm_nonneg (U x)).trans hUx
  exact mul_le_mul hUx hVx (norm_nonneg (V x)) hR

 
lemma integrable_energyIntegrand_apply_of_bounds [IsFiniteMeasure μ]
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ} {Lam beta gamma : ℝ}
    (hLam : 0 ≤ Lam) (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (U V : ℝ × EuclideanSpace ℝ n) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) U V) μ :=
  integrable_energyIntegrand_apply₂_of_bounds (U := fun _ => U) (V := fun _ => V)
    hLam ha hb hc aestronglyMeasurable_const aestronglyMeasurable_const
    ha_bound hb_bound hc_bound (Filter.Eventually.of_forall fun _ => le_rfl)
    (Filter.Eventually.of_forall fun _ => le_rfl)

namespace UniformlyEllipticOn

variable {Ω : Set α} {a : α → Matrix n n ℝ}
variable {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
variable {U V : α → ℝ × EuclideanSpace ℝ n}
variable {lam Lam beta gamma R S : ℝ}

 




lemma integrable_energyIntegrand_apply₂_of_integrable_norm_mul_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x => ‖U x‖ * ‖V x‖) μ) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ :=
  integrable_energyIntegrand_apply₂_of_integrable_norm_mul h.upper_nonneg ha hb hc hU hV
    (hΩ.mono fun _ hx => h.upper_bound hx) hb_bound hc_bound hUV

 
lemma integrable_energyIntegrand_apply₂_of_memLp_two_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ :=
  integrable_energyIntegrand_apply₂_of_memLp_two h.upper_nonneg ha hb hc hU hV
    (hΩ.mono fun _ hx => h.upper_bound hx) hb_bound hc_bound

 
lemma integrable_energyIntegrand_apply₂_of_bounds_on [IsFiniteMeasure μ]
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hU_bound : ∀ᵐ x ∂μ, ‖U x‖ ≤ R) (hV_bound : ∀ᵐ x ∂μ, ‖V x‖ ≤ S) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ :=
  integrable_energyIntegrand_apply₂_of_bounds h.upper_nonneg ha hb hc hU hV
    (hΩ.mono fun _ hx => h.upper_bound hx) hb_bound hc_bound hU_bound hV_bound

 

lemma integrable_energyIntegrand_apply_of_bounds_on [IsFiniteMeasure μ]
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) (hc : AEStronglyMeasurable c μ)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (U V : ℝ × EuclideanSpace ℝ n) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) U V) μ :=
  integrable_energyIntegrand_apply_of_bounds h.upper_nonneg ha hb hc
    (hΩ.mono fun _ hx => h.upper_bound hx) hb_bound hc_bound U V

end UniformlyEllipticOn

end PDE

end TauCeti
