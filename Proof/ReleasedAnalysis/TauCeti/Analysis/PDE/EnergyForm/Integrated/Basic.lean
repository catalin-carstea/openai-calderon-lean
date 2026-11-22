/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.EnergyForm.Linearity
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Ellipticity.Energy
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! From Proof/TauCeti/Analysis/PDE/EnergyForm/Integrated/Basic.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 
































public section

namespace TauCeti

namespace PDE

open MeasureTheory Matrix
open scoped InnerProductSpace

variable {X n : Type*} [MeasurableSpace X] [Fintype n]

 
noncomputable local instance integratedEnergyFormDecidableEq : DecidableEq n := Classical.decEq n

 




@[expose] public noncomputable def energyFormIntegral (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ) (U V : X → ℝ × EuclideanSpace ℝ n) : ℝ :=
  ∫ x, (energyIntegrand (a x) (b x) (c x) (U x) (V x)) ∂μ

 
theorem energyFormIntegral_def (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ) (U V : X → ℝ × EuclideanSpace ℝ n) :
    energyFormIntegral μ a b c U V =
      ∫ x, (energyIntegrand (a x) (b x) (c x) (U x) (V x)) ∂μ :=
  by simp [energyFormIntegral]

variable (μ : Measure X) (a : X → Matrix n n ℝ)
variable (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
variable (U V W : X → ℝ × EuclideanSpace ℝ n)

 

lemma energyFormIntegral_congr_ae {a' : X → Matrix n n ℝ} {b' : X → EuclideanSpace ℝ n}
    {c' : X → ℝ} {U' V' : X → ℝ × EuclideanSpace ℝ n}
    (ha : a =ᵐ[μ] a') (hb : b =ᵐ[μ] b') (hc : c =ᵐ[μ] c') (hU : U =ᵐ[μ] U') (hV : V =ᵐ[μ] V') :
    energyFormIntegral μ a b c U V = energyFormIntegral μ a' b' c' U' V' := by
  rw [energyFormIntegral_def, energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ha, hb, hc, hU, hV] with x hax hbx hcx hUx hVx
  simp [hax, hbx, hcx, hUx, hVx]

 
@[simp]
lemma energyFormIntegral_zero_left :
    energyFormIntegral μ a b c (fun _ ↦ 0) V = 0 := by
  simp [energyFormIntegral_def]

 
@[simp]
lemma energyFormIntegral_zero_right :
    energyFormIntegral μ a b c U (fun _ ↦ 0) = 0 := by
  simp [energyFormIntegral_def]

 
@[simp]
lemma energyFormIntegral_zero_coefficients :
    energyFormIntegral μ (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) U V = 0 := by
  simp [energyFormIntegral_def]

 
private lemma integral_congr_forall {f g : X → ℝ} (h : ∀ x, f x = g x) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ :=
  integral_congr_ae (Filter.Eventually.of_forall h)

 
@[simp]
lemma energyFormIntegral_neg_left :
    energyFormIntegral μ a b c (fun x ↦ -U x) V = -energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (a x) (b x) (c x) (-U x) (V x))
      (g := fun x ↦ -energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x ↦ by simp),
    MeasureTheory.integral_neg]

 
@[simp]
lemma energyFormIntegral_neg_right :
    energyFormIntegral μ a b c U (fun x ↦ -V x) = -energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (-V x))
      (g := fun x ↦ -energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x ↦ map_neg (energyIntegrand (a x) (b x) (c x) (U x)) (V x)),
    MeasureTheory.integral_neg]

 
@[simp]
lemma energyFormIntegral_neg_coefficients :
    energyFormIntegral μ (fun x ↦ -a x) (fun x ↦ -b x) (fun x ↦ -c x) U V =
      -energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (-a x) (-b x) (-c x) (U x) (V x))
      (g := fun x ↦ -energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x ↦ by simp),
    MeasureTheory.integral_neg]

 

lemma energyFormIntegral_add_left
    (hU : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (hW : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (W x) (V x)) μ) :
    energyFormIntegral μ a b c (fun x ↦ U x + W x) V =
      energyFormIntegral μ a b c U V + energyFormIntegral μ a b c W V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (a x) (b x) (c x) (U x + W x) (V x))
      (g := fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x) +
          energyIntegrand (a x) (b x) (c x) (W x) (V x))
      (fun x ↦ by simp),
    integral_add hU hW]

 

lemma energyFormIntegral_add_right
    (hV : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (hW : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (W x)) μ) :
    energyFormIntegral μ a b c U (fun x ↦ V x + W x) =
      energyFormIntegral μ a b c U V + energyFormIntegral μ a b c U W := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x + W x))
      (g := fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x) +
          energyIntegrand (a x) (b x) (c x) (U x) (W x))
      (fun x ↦ map_add (energyIntegrand (a x) (b x) (c x) (U x)) (V x) (W x)),
    integral_add hV hW]

 
lemma energyFormIntegral_smul_left (r : ℝ) :
    energyFormIntegral μ a b c (fun x ↦ r • U x) V =
      r * energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (a x) (b x) (c x) (r • U x) (V x))
      (g := fun x ↦ r • energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x ↦ by simp),
    MeasureTheory.integral_smul]
  simp [smul_eq_mul]

 
lemma energyFormIntegral_smul_right (r : ℝ) :
    energyFormIntegral μ a b c U (fun x ↦ r • V x) =
      r * energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (r • V x))
      (g := fun x ↦ r • energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x ↦ by simp),
    MeasureTheory.integral_smul]
  simp [smul_eq_mul]

variable (a' : X → Matrix n n ℝ) (b' : X → EuclideanSpace ℝ n) (c' : X → ℝ)
variable (m : X → ℝ) (r : ℝ)

 

lemma energyFormIntegral_add
    (h : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (h' : Integrable (fun x ↦ energyIntegrand (a' x) (b' x) (c' x) (U x) (V x)) μ) :
    energyFormIntegral μ (fun x ↦ a x + a' x) (fun x ↦ b x + b' x) (fun x ↦ c x + c' x)
        U V =
      energyFormIntegral μ a b c U V + energyFormIntegral μ a' b' c' U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (a x + a' x) (b x + b' x) (c x + c' x) (U x) (V x))
      (g := fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x) +
          energyIntegrand (a' x) (b' x) (c' x) (U x) (V x))
      (fun x ↦ by simp),
    integral_add h h']

 

lemma energyFormIntegral_sub
    (h : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (h' : Integrable (fun x ↦ energyIntegrand (a' x) (b' x) (c' x) (U x) (V x)) μ) :
    energyFormIntegral μ (fun x ↦ a x - a' x) (fun x ↦ b x - b' x) (fun x ↦ c x - c' x)
        U V =
      energyFormIntegral μ a b c U V - energyFormIntegral μ a' b' c' U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (a x - a' x) (b x - b' x) (c x - c' x) (U x) (V x))
      (g := fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x) -
          energyIntegrand (a' x) (b' x) (c' x) (U x) (V x))
      (fun x ↦ by simp),
    integral_sub h h']

 
lemma energyFormIntegral_smul :
    energyFormIntegral μ (fun x ↦ r • a x) (fun x ↦ r • b x) (fun x ↦ r * c x) U V =
      r * energyFormIntegral μ a b c U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (r • a x) (r • b x) (r * c x) (U x) (V x))
      (g := fun x ↦ r • energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (fun x ↦ by simp),
    MeasureTheory.integral_smul]
  simp [smul_eq_mul]

 
lemma energyFormIntegral_principal_add_lowerOrder
    (hprincipal : Integrable (fun x ↦ energyIntegrand (a x) 0 0 (U x) (V x)) μ)
    (hlower : Integrable (fun x ↦ energyIntegrand 0 (b x) (c x) (U x) (V x)) μ) :
    energyFormIntegral μ a b c U V =
      energyFormIntegral μ a (fun _ ↦ 0) (fun _ ↦ 0) U V +
        energyFormIntegral μ (fun _ ↦ 0) b c U V := by
  simpa using
    energyFormIntegral_add μ a (fun _ ↦ 0) (fun _ ↦ 0) U V
      (fun _ ↦ 0) b c hprincipal hlower

 
lemma energyFormIntegral_principal_drift_mass
    (hprincipal : Integrable (fun x ↦ energyIntegrand (a x) 0 0 (U x) (V x)) μ)
    (hdrift : Integrable (fun x ↦ energyIntegrand 0 (b x) 0 (U x) (V x)) μ)
    (hmass : Integrable (fun x ↦ energyIntegrand 0 0 (c x) (U x) (V x)) μ) :
    energyFormIntegral μ a b c U V =
      energyFormIntegral μ a (fun _ ↦ 0) (fun _ ↦ 0) U V +
        energyFormIntegral μ (fun _ ↦ 0) b (fun _ ↦ 0) U V +
          energyFormIntegral μ (fun _ ↦ 0) (fun _ ↦ 0) c U V := by
   
  have hlower :
      Integrable (fun x ↦ energyIntegrand 0 (b x) (c x) (U x) (V x)) μ := by
    refine (hdrift.add hmass).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [Pi.add_apply]
   
  have hlower_eq :
      energyFormIntegral μ (fun _ ↦ 0) b c U V =
        energyFormIntegral μ (fun _ ↦ 0) b (fun _ ↦ 0) U V +
          energyFormIntegral μ (fun _ ↦ 0) (fun _ ↦ 0) c U V := by
    simpa using
      energyFormIntegral_add μ (fun _ ↦ 0) b (fun _ ↦ 0) U V
        (fun _ ↦ 0) (fun _ ↦ 0) c hdrift hmass
   
  calc
    energyFormIntegral μ a b c U V =
        energyFormIntegral μ a (fun _ ↦ 0) (fun _ ↦ 0) U V +
          energyFormIntegral μ (fun _ ↦ 0) b c U V :=
      energyFormIntegral_principal_add_lowerOrder μ a b c U V hprincipal hlower
    _ = energyFormIntegral μ a (fun _ ↦ 0) (fun _ ↦ 0) U V +
          (energyFormIntegral μ (fun _ ↦ 0) b (fun _ ↦ 0) U V +
            energyFormIntegral μ (fun _ ↦ 0) (fun _ ↦ 0) c U V) := by
      rw [hlower_eq]
    _ = energyFormIntegral μ a (fun _ ↦ 0) (fun _ ↦ 0) U V +
          energyFormIntegral μ (fun _ ↦ 0) b (fun _ ↦ 0) U V +
            energyFormIntegral μ (fun _ ↦ 0) (fun _ ↦ 0) c U V := by
      rw [add_assoc]

 

lemma energyFormIntegral_eq_one_zero_baseMass_add_perturbation (hmodel : Integrable
      (fun x ↦ energyIntegrand (1 : Matrix n n ℝ) 0 (m x) (U x) (V x)) μ) (hpert : Integrable
      (fun x ↦ energyIntegrand (a x - 1) (b x) (c x - m x) (U x) (V x)) μ) :
    energyFormIntegral μ a b c U V =
      energyFormIntegral μ (fun _ ↦ (1 : Matrix n n ℝ)) (fun _ ↦ 0) m U V +
        energyFormIntegral μ (fun x ↦ a x - 1) b (fun x ↦ c x - m x) U V := by
  simp only [energyFormIntegral_def]
  rw [integral_congr_forall (μ := μ)
      (f := fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x))
      (g := fun x ↦ energyIntegrand (1 : Matrix n n ℝ) 0 (m x) (U x) (V x) +
          energyIntegrand (a x - 1) (b x) (c x - m x) (U x) (V x))
      (fun x ↦ energyIntegrand_eq_one_zero_baseMass_add_perturbation_apply
        (a x) (b x) (c x) (m x) (U x) (V x)),
    integral_add hmodel hpert]

 

lemma energyFormIntegral_eq_one_zero_mass_add_perturbation (hmodel : Integrable
      (fun x ↦ energyIntegrand (1 : Matrix n n ℝ) 0 (c x) (U x) (V x)) μ) (hpert : Integrable
      (fun x ↦ energyIntegrand (a x - 1) (b x) 0 (U x) (V x)) μ) :
    energyFormIntegral μ a b c U V =
      energyFormIntegral μ (fun _ ↦ (1 : Matrix n n ℝ)) (fun _ ↦ 0) c U V +
        energyFormIntegral μ (fun x ↦ a x - 1) b (fun _ ↦ 0) U V := by
  simpa using
    energyFormIntegral_eq_one_zero_baseMass_add_perturbation μ a b c U V c hmodel
      (by simpa using hpert)

 

lemma energyFormIntegral_one_zero_zero :
    energyFormIntegral μ (fun _ ↦ (1 : Matrix n n ℝ)) (fun _ ↦ 0) (fun _ ↦ 0) U V =
      ∫ x, ((V x).2 ⬝ᵥ (U x).2) ∂μ := by
  rw [energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    by simp

 

lemma energyFormIntegral_one_zero_mass (m : X → ℝ) :
    energyFormIntegral μ (fun _ ↦ (1 : Matrix n n ℝ)) (fun _ ↦ 0) m U V =
      ∫ x, ((V x).2 ⬝ᵥ (U x).2 + m x * (U x).1 * (V x).1) ∂μ := by
  rw [energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    by simp

 

lemma energyFormIntegral_one_zero_mass_self (m : X → ℝ) :
    energyFormIntegral μ (fun _ ↦ (1 : Matrix n n ℝ)) (fun _ ↦ 0) m U U =
      ∫ x, (‖(U x).2‖ ^ 2 + m x * (U x).1 ^ 2) ∂μ := by
  rw [energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    by simpa using energyIntegrand_one_zero_mass_self (m x) (U x)

variable {Lam beta gamma : ℝ}

 




lemma norm_energyFormIntegral_le_of_bounds (hLam : 0 ≤ Lam)
    (ha : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x ↦ (Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) μ) :
    ‖energyFormIntegral μ a b c U V‖ ≤
      ∫ x, ((Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) ∂μ := by
  rw [energyFormIntegral_def]
  refine norm_integral_le_of_norm_le hUV ?_
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  simpa [mul_assoc] using
    norm_energyIntegrand_apply_le_of_bounds hLam hax hbx hcx (U x) (V x)

 

lemma garding_energyFormIntegral_self_of_bounds (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (hlower : Integrable
      (fun x ↦ lam / 2 * ‖(U x).2‖ ^ 2 - beta ^ 2 / (2 * lam) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (lam / 2 * ‖(U x).2‖ ^ 2 - beta ^ 2 / (2 * lam) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  exact garding_energyIntegrand_self_of_bounds hlam
    (fun ξ ↦ by simpa [Matrix.toQuadraticForm'_apply] using hax ξ) hbx hcx (U x)

 

lemma garding_energyFormIntegral_self_of_mass_lower_bound_of_bounds_with_parameter
    {eps : ℝ} (heps : 0 < eps)
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x)
    (hlower : Integrable
      (fun x ↦ (lam - eps) * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (4 * eps)) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, ((lam - eps) * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (4 * eps)) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  exact garding_energyIntegrand_self_of_mass_lower_bound_of_bounds_with_parameter heps
    (fun ξ ↦ by simpa [Matrix.toQuadraticForm'_apply] using hax ξ) hbx hcx (U x)

 

lemma garding_energyFormIntegral_self_of_mass_lower_bound_of_bounds (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x)
    (hlower : Integrable
      (fun x ↦ lam / 2 * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (2 * lam)) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (lam / 2 * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (2 * lam)) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  exact garding_energyIntegrand_self_of_mass_lower_bound_of_bounds hlam
    (fun ξ ↦ by simpa [Matrix.toQuadraticForm'_apply] using hax ξ) hbx hcx (U x)

 

lemma integral_min_lam_mass_mul_norm_sq_le_energyFormIntegral_zero_drift_self (hlam : 0 ≤ lam)
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hlower : Integrable (fun x ↦ min lam (c x) * ‖U x‖ ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) 0 (c x) (U x) (U x)) μ) :
    ∫ x, (min lam (c x) * ‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ a (fun _ ↦ 0) c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha] with x hax
  exact min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self hlam
    (fun ξ ↦ by simpa [Matrix.toQuadraticForm'_apply] using hax ξ) (U x)

 

lemma integral_mul_norm_snd_sq_le_energyFormIntegral_zero_drift_self
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (hlower : Integrable (fun x ↦ lam * ‖(U x).2‖ ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) 0 (c x) (U x) (U x)) μ) :
    ∫ x, lam * ‖(U x).2‖ ^ 2 ∂μ ≤ energyFormIntegral μ a (fun _ ↦ 0) c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hc] with x hax hcx
  exact mul_norm_snd_sq_le_energyIntegrand_zero_drift_self
    (fun ξ ↦ by simpa [Matrix.toQuadraticForm'_apply] using hax ξ) hcx (U x)

 

lemma energyFormIntegral_zero_drift_self_nonneg
    (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n, 0 ≤ ξ ⬝ᵥ (a x *ᵥ ξ)) (hc : ∀ᵐ x ∂μ, 0 ≤ c x) :
    0 ≤ energyFormIntegral μ a (fun _ ↦ 0) c U U := by
  rw [energyFormIntegral_def]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ha, hc] with x hax hcx
  have hpoint :=
    min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self (lam := 0) (c₀ := c x)
      le_rfl (fun ξ ↦ by simpa [Matrix.toQuadraticForm'_apply] using hax ξ)
      (U x)
  simpa [min_eq_left hcx] using hpoint

 

lemma integral_min_diagonal_lower_bound_mul_norm_sq_le_energyFormIntegral_self_of_bounds
    (hlam : 0 < lam) (ha : ∀ᵐ x ∂μ, ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x)
    (hlower : Integrable
      (fun x ↦ min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U x‖ ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  rw [energyFormIntegral_def]
  refine integral_mono_ae hlower henergy ?_
  filter_upwards [ha, hb, hc] with x hax hbx hcx
  exact min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self hlam
    (fun ξ ↦ by simpa [Matrix.toQuadraticForm'_apply] using hax ξ) hbx hcx (U x)

namespace UniformlyEllipticOn

variable {Ω : Set X} {lam Lam beta gamma mu : ℝ}
variable {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {U V : X → ℝ × EuclideanSpace ℝ n}

 

lemma norm_energyFormIntegral_le_on (h : UniformlyEllipticOn Ω a lam Lam)
    (hΩ : ∀ᵐ x ∂μ, x ∈ Ω) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x ↦ (Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) μ) :
    ‖energyFormIntegral μ a b c U V‖ ≤
      ∫ x, ((Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) ∂μ := by
  refine PDE.norm_energyFormIntegral_le_of_bounds (μ := μ) (a := a) (b := b) (c := c)
    (U := U) (V := V) h.upper_nonneg ?_ hb hc hUV
  filter_upwards [hΩ] with x hx
  exact h.upper_bound hx

 

lemma garding_energyFormIntegral_self_on (h : UniformlyEllipticOn Ω a lam Lam)
    (hΩ : ∀ᵐ x ∂μ, x ∈ Ω) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (hlower : Integrable (fun x ↦ lam / 2 * ‖(U x).2‖ ^ 2 - beta ^ 2 / (2 * lam) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (lam / 2 * ‖(U x).2‖ ^ 2 - beta ^ 2 / (2 * lam) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  refine PDE.garding_energyFormIntegral_self_of_bounds (μ := μ) (a := a) (b := b) (c := c)
    (U := U) h.pos ?_ hb hc hlower henergy
  filter_upwards [hΩ] with x hx
  intro ξ
  simpa [Matrix.toQuadraticForm'_apply] using h.lower_bound hx ξ

 

lemma garding_energyFormIntegral_self_of_mass_lower_bound_with_parameter_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x) {eps : ℝ}
    (heps : 0 < eps)
    (hlower : Integrable
      (fun x ↦ (lam - eps) * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (4 * eps)) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, ((lam - eps) * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (4 * eps)) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  refine PDE.garding_energyFormIntegral_self_of_mass_lower_bound_of_bounds_with_parameter
    (μ := μ) (a := a) (b := b) (c := c) (U := U) heps ?_ hb hc hlower henergy
  filter_upwards [hΩ] with x hx
  intro ξ
  simpa only [Matrix.toQuadraticForm'_apply] using h.lower_bound hx ξ

 

lemma garding_energyFormIntegral_self_of_mass_lower_bound_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x) (hlower : Integrable
      (fun x ↦ lam / 2 * ‖(U x).2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * (U x).1 ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (lam / 2 * ‖(U x).2‖ ^ 2 +
        (mu - beta ^ 2 / (2 * lam)) * (U x).1 ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  refine PDE.garding_energyFormIntegral_self_of_mass_lower_bound_of_bounds (μ := μ) (a := a)
    (b := b) (c := c) (U := U) h.pos ?_ hb hc hlower henergy
  filter_upwards [hΩ] with x hx
  intro ξ
  simpa [Matrix.toQuadraticForm'_apply] using h.lower_bound hx ξ

 

lemma integral_min_diagonal_lower_bound_mul_norm_sq_le_energyFormIntegral_self_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc : ∀ᵐ x ∂μ, mu ≤ c x)
    (hlower : Integrable (fun x ↦ min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U x‖ ^ 2) μ)
    (henergy : Integrable (fun x ↦ energyIntegrand (a x) (b x) (c x) (U x) (U x)) μ) :
    ∫ x, (min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U x‖ ^ 2) ∂μ
      ≤ energyFormIntegral μ a b c U U := by
  refine PDE.integral_min_diagonal_lower_bound_mul_norm_sq_le_energyFormIntegral_self_of_bounds
    (μ := μ) (a := a) (b := b) (c := c) (U := U) h.pos ?_ hb hc hlower henergy
  filter_upwards [hΩ] with x hx
  intro ξ
  simpa [Matrix.toQuadraticForm'_apply] using h.lower_bound hx ξ

end UniformlyEllipticOn

end PDE

end TauCeti
