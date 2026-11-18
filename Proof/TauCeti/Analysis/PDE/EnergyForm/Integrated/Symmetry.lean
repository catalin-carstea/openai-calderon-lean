/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.PDE.EnergyForm.Integrated.Basic
public import Proof.TauCeti.Analysis.PDE.SymmetricEnergy

 



























public section

namespace TauCeti

namespace PDE

open MeasureTheory Matrix

variable {X n : Type*} [MeasurableSpace X] [Fintype n]

 

noncomputable local instance integratedSymmetricEnergyDecidableEq : DecidableEq n :=
  Classical.decEq n

variable {μ : Measure X}
variable {a : X → Matrix n n ℝ} {c : X → ℝ}
variable {U V : X → ℝ × EuclideanSpace ℝ n}

 

lemma energyFormIntegral_zero_drift_transpose_apply :
    energyFormIntegral μ (fun x => (a x)ᵀ) (fun _ => 0) c U V =
      energyFormIntegral μ a (fun _ => 0) c V U := by
  classical
  rw [energyFormIntegral_def, energyFormIntegral_def]
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun x =>
    energyIntegrand_zero_drift_transpose_apply (a x) (c x) (U x) (V x)

 

lemma energyFormIntegral_zero_drift_comm_of_isSymm_ae (ha : ∀ᵐ x ∂μ, (a x).IsSymm) :
    energyFormIntegral μ a (fun _ => 0) c U V =
      energyFormIntegral μ a (fun _ => 0) c V U := by
  calc
    energyFormIntegral μ a (fun _ => 0) c U V =
        energyFormIntegral μ (fun x => (a x)ᵀ) (fun _ => 0) c U V := by
      refine energyFormIntegral_congr_ae (μ := μ) (a := a) (b := fun _ => 0) (c := c)
        (U := U) (V := V) (a' := fun x => (a x)ᵀ) (b' := fun _ => 0) (c' := c)
        (U' := U) (V' := V) ?_ ?_ ?_ ?_ ?_
      · filter_upwards [ha] with x hx
        exact hx.eq.symm
      · rfl
      · rfl
      · rfl
      · rfl
    _ = energyFormIntegral μ a (fun _ => 0) c V U :=
      energyFormIntegral_zero_drift_transpose_apply

 

@[simp]
lemma energyFormIntegral_zero_drift_swap_eq_of_isSymm_ae (ha : ∀ᵐ x ∂μ, (a x).IsSymm) :
    Function.swap (energyFormIntegral μ a (fun _ => 0) c) =
      energyFormIntegral μ a (fun _ => 0) c := by
  funext U V
  exact energyFormIntegral_zero_drift_comm_of_isSymm_ae (a := a) (c := c) (U := V) (V := U) ha

 
@[simp]
lemma energyFormIntegral_coefficientSymmetricPart_zero_drift_swap_eq :
    Function.swap
        (energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) (fun _ => 0) c) =
      energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) (fun _ => 0) c :=
  energyFormIntegral_zero_drift_swap_eq_of_isSymm_ae
    (Filter.Eventually.of_forall fun _ => coefficientSymmetricPart_isSymm _)

 


@[simp]
lemma energyFormIntegral_coefficientSymmetricPart_self {b : X → EuclideanSpace ℝ n} :
    energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) b c U U =
      energyFormIntegral μ a b c U U := by
  classical
  rw [energyFormIntegral_def, energyFormIntegral_def]
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun x =>
    energyIntegrand_coefficientSymmetricPart_self (a x) (b x) (c x) (U x)

 

lemma energyFormIntegral_coefficientSymmetricPart_zero_drift_apply
    (hUV : Integrable (fun x => energyIntegrand (a x) 0 (c x) (U x) (V x)) μ)
    (hVU : Integrable (fun x => energyIntegrand (a x) 0 (c x) (V x) (U x)) μ) :
    energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) (fun _ => 0) c U V =
      (energyFormIntegral μ a (fun _ => 0) c U V +
        energyFormIntegral μ a (fun _ => 0) c V U) / 2 := by
  classical
  rw [energyFormIntegral_def, energyFormIntegral_def, energyFormIntegral_def]
  have hpoint :
      (fun x => energyIntegrand (coefficientSymmetricPart (a x)) 0 (c x) (U x) (V x)) =
        fun x => (energyIntegrand (a x) 0 (c x) (U x) (V x) +
          energyIntegrand (a x) 0 (c x) (V x) (U x)) / 2 := by
    funext x
    exact energyIntegrand_coefficientSymmetricPart_zero_drift_apply (a x) (c x) (U x) (V x)
  rw [hpoint]
  rw [integral_div, integral_add hUV hVU]

 

lemma energyFormIntegral_coefficientSymmetricPart_eq_of_isSymm_ae {b : X → EuclideanSpace ℝ n}
    (ha : ∀ᵐ x ∂μ, (a x).IsSymm) :
    energyFormIntegral μ (fun x => coefficientSymmetricPart (a x)) b c U V =
      energyFormIntegral μ a b c U V := by
  classical
  rw [energyFormIntegral_def, energyFormIntegral_def]
  refine integral_congr_ae ?_
  filter_upwards [ha] with x hx
  simp [coefficientSymmetricPart_eq_self_of_isSymm hx]

end PDE

end TauCeti
