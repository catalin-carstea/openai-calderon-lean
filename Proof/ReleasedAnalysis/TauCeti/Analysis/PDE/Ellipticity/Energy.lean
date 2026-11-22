/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.EnergyLowerBounds

/-! From Proof/TauCeti/Analysis/PDE/Ellipticity/Energy.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 










































public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ}
variable {lam Lam beta gamma mu : ℝ}

 

lemma norm_energyIntegrand_apply_le (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ} (hb : ‖b₀‖ ≤ beta) (hc : ‖c₀‖ ≤ gamma)
    (U V : ℝ × EuclideanSpace ℝ n) :
    ‖energyIntegrand (a x) b₀ c₀ U V‖ ≤ (Lam + beta + gamma) * ‖U‖ * ‖V‖ :=
  norm_energyIntegrand_apply_le_of_bounds h.upper_nonneg (h.upper_bound hx) hb hc U V

grind_pattern norm_energyIntegrand_apply_le =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, ‖c₀‖ ≤ gamma,
  energyIntegrand (a x) b₀ c₀ U V

 

lemma opNorm_energyIntegrand_le (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ} (hb : ‖b₀‖ ≤ beta) (hc : ‖c₀‖ ≤ gamma) :
    ‖energyIntegrand (a x) b₀ c₀‖ ≤ Lam + beta + gamma :=
  opNorm_energyIntegrand_le_of_bounds h.upper_nonneg (h.upper_bound hx) hb hc

grind_pattern opNorm_energyIntegrand_le =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, ‖c₀‖ ≤ gamma,
  ‖energyIntegrand (a x) b₀ c₀‖

 



lemma garding_energyIntegrand_self (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ} (hb : ‖b₀‖ ≤ beta) (hc : 0 ≤ c₀)
    (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2
      ≤ energyIntegrand (a x) b₀ c₀ U U :=
  garding_energyIntegrand_self_of_bounds h.pos (h.lower_bound hx) hb hc U

grind_pattern garding_energyIntegrand_self =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, 0 ≤ c₀,
  energyIntegrand (a x) b₀ c₀ U U

 




lemma garding_energyIntegrand_self_of_mass_lower_bound_with_parameter
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {b₀ : EuclideanSpace ℝ n} {c₀ eps : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (heps : 0 < eps) (U : ℝ × EuclideanSpace ℝ n) :
    (lam - eps) * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (4 * eps)) * U.1 ^ 2
      ≤ energyIntegrand (a x) b₀ c₀ U U :=
  garding_energyIntegrand_self_of_mass_lower_bound_of_bounds_with_parameter heps
    (h.lower_bound hx) hb hc U

grind_pattern garding_energyIntegrand_self_of_mass_lower_bound_with_parameter =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, mu ≤ c₀, 0 < eps,
  energyIntegrand (a x) b₀ c₀ U U

 




lemma garding_energyIntegrand_self_of_mass_lower_bound (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand (a x) b₀ c₀ U U :=
  garding_energyIntegrand_self_of_mass_lower_bound_of_bounds h.pos (h.lower_bound hx) hb hc U

grind_pattern garding_energyIntegrand_self_of_mass_lower_bound =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, mu ≤ c₀,
  energyIntegrand (a x) b₀ c₀ U U

 

lemma min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x) b₀ c₀ U U :=
  PDE.min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self h.pos (h.lower_bound hx)
    hb hc U

grind_pattern min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, mu ≤ c₀,
  energyIntegrand (a x) b₀ c₀ U U

 

lemma min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {c₀ : ℝ}
    (U : ℝ × EuclideanSpace ℝ n) :
    min lam c₀ * ‖U‖ ^ 2 ≤ energyIntegrand (a x) 0 c₀ U U :=
  PDE.min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self h.pos.le
    (h.lower_bound hx) U

grind_pattern min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, energyIntegrand (a x) 0 c₀ U U

 

lemma mul_norm_snd_sq_le_energyIntegrand_zero_drift_self
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {c₀ : ℝ} (hc : 0 ≤ c₀)
    (U : ℝ × EuclideanSpace ℝ n) :
    lam * ‖U.2‖ ^ 2 ≤ energyIntegrand (a x) 0 c₀ U U :=
  PDE.mul_norm_snd_sq_le_energyIntegrand_zero_drift_self (h.lower_bound hx) hc U

grind_pattern mul_norm_snd_sq_le_energyIntegrand_zero_drift_self =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, 0 ≤ c₀, energyIntegrand (a x) 0 c₀ U U

end UniformlyEllipticOn

end PDE

end TauCeti
