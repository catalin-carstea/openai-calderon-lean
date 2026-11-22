/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
module

public import Proof.CalderonPatch.BoundaryLayerWaves

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

public section

noncomputable section

open Polynomial Set Finset Filter Topology
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polynomialSpatialDeriv_congr {W : Set E} (hW : IsOpen W) {P Q : E → ℂ[X]}
    (hPQ : EqOn P Q W) (D : ℕ) (v : E) :
    EqOn (polynomialSpatialDeriv D v P) (polynomialSpatialDeriv D v Q) W := by
  intro y hy
  unfold polynomialSpatialDeriv
  apply sum_congr rfl
  intro j hj
  have he : (fun x => (P x).coeff j) =ᶠ[𝓝 y] (fun x => (Q x).coeff j) :=
    (hPQ.eventuallyEq_of_mem (hW.mem_nhds hy)).mono (fun x hx => congrArg (fun p : ℂ[X] => p.coeff j) hx)
  rw [he.fderiv_eq]

theorem profileSpatialDeriv_congr {W : Set E} (hW : IsOpen W)
    {κ κ₂ : E → ℝ} (hκ : EqOn κ κ₂ W) {P Q : E → ℂ[X]} (hPQ : EqOn P Q W) (D : ℕ) (v : E) :
    EqOn (profileSpatialDeriv D v κ P) (profileSpatialDeriv D v κ₂ Q) W := by
  intro y hy
  unfold profileSpatialDeriv
  have he : fderiv ℝ κ y = fderiv ℝ κ₂ y := (hκ.eventuallyEq_of_mem (hW.mem_nhds hy)).fderiv_eq
  rw [polynomialSpatialDeriv_congr hW hPQ D v hy, he, hPQ hy]

end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem forcing_congr {ξ : Fin n → ℝ} {U₁ U₂ W : Set Y}
    (B₁ : BoundaryLayerCoefficients ξ U₁) (B₂ : BoundaryLayerCoefficients ξ U₂)
    (hW : IsOpen W) (hκ : EqOn B₁.kappa B₂.kappa W) {P Q : Y → ℂ[X]} (hPQ : EqOn P Q W)
    (j k : ℕ) (hkj : k < j)
    (hA : ∀ l ≤ j - k, ∀ i r, EqOn (B₁.inverse l i r) (B₂.inverse l i r) W)
    (hτ : ∀ l < j - k, EqOn (B₁.normalDrift l) (B₂.normalDrift l) W)
    (hc : ∀ l < j - k, ∀ i, EqOn (B₁.tangentDrift l i) (B₂.tangentDrift l i) W) :
    EqOn (B₁.forcing j k P) (B₂.forcing j k Q) W := by
  let l := j - k
  have hl : 0 < l := Nat.sub_pos_of_lt hkj
  have hlJ : l ≤ j := Nat.sub_le _ _
  have hm1 : l - 1 < j - k := by omega
  have hm2 : l - 2 < j - k := by omega
  have hsp (v : Y) := profileSpatialDeriv_congr hW hκ hPQ (2 * k) v
  have hspp (v w : Y) := profileSpatialDeriv_congr hW hκ (hsp w) (2 * k + 1) v
  intro y hy
  have hp : B₁.principalTerm l P y = B₂.principalTerm l Q y := by
    unfold principalTerm
    rw [hPQ hy]
    apply congrArg (fun c : ℂ => C c * X ^ l * Q y)
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro r hr
    rw [hA l le_rfl i r hy]
  have hn : B₁.normalTerm l P y = B₂.normalTerm l Q y := by
    unfold normalTerm
    rw [hτ (l - 1) hm1 hy, hκ hy, hPQ hy]
  have hx : B₁.crossTerm l (2 * k) P y = B₂.crossTerm l (2 * k) Q y := by
    unfold crossTerm
    apply congrArg (fun R : ℂ[X] => C (-2 * Complex.I) * R)
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro r hr
    rw [hA (l - 1) (by omega) i r hy, hsp (e r) hy]
  have hd : B₁.phaseDriftTerm l P y = B₂.phaseDriftTerm l Q y := by
    unfold phaseDriftTerm
    apply congrArg (fun R : ℂ[X] => C (-Complex.I) * R)
    apply sum_congr rfl; intro i hi
    rw [hc (l - 1) hm1 i hy, hPQ hy]
  have ht : B₁.tangentSecondTerm l (2 * k) P y = B₂.tangentSecondTerm l (2 * k) Q y := by
    unfold tangentSecondTerm
    apply congrArg (fun R : ℂ[X] => -R)
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro r hr
    rw [hA (l - 2) (by omega) i r hy, hspp (e i) (e r) hy]
  have hf : B₁.tangentFirstTerm l (2 * k) P y = B₂.tangentFirstTerm l (2 * k) Q y := by
    unfold tangentFirstTerm
    apply congrArg (fun R : ℂ[X] => -R)
    apply sum_congr rfl; intro i hi
    rw [hc (l - 2) hm2 i hy, hsp (e i) hy]
  change B₁.principalTerm l P y + B₁.normalTerm l P y + B₁.crossTerm l (2 * k) P y +
    B₁.phaseDriftTerm l P y + (if 2 ≤ l then B₁.tangentSecondTerm l (2 * k) P y + B₁.tangentFirstTerm l (2 * k) P y else 0) = _
  rw [hp, hn, hx, hd, ht, hf]
  rfl

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Set Finset
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem layerPolynomial_congr_below {ξ : Fin n → ℝ} {U₁ U₂ W : Set Y}
    (B₁ : BoundaryLayerCoefficients ξ U₁) (B₂ : BoundaryLayerCoefficients ξ U₂)
    (hW : IsOpen W) (hκ : EqOn B₁.kappa B₂.kappa W) (a : Y → ℂ) (N : ℕ)
    (hA : ∀ l < N, ∀ i r, EqOn (B₁.inverse l i r) (B₂.inverse l i r) W)
    (hτ : ∀ l, l + 1 < N → EqOn (B₁.normalDrift l) (B₂.normalDrift l) W)
    (hc : ∀ l < N, ∀ i, EqOn (B₁.tangentDrift l i) (B₂.tangentDrift l i) W) :
    ∀ j : ℕ, j < N → EqOn (B₁.layerPolynomial a j) (B₂.layerPolynomial a j) W := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj y hy
    cases j with
    | zero => rw [B₁.layerPolynomial_zero, B₂.layerPolynomial_zero]
    | succ j =>
      change triangularLayerPolynomial B₁.transportScale a B₁.forcing (j + 1) y =
        triangularLayerPolynomial B₂.transportScale a B₂.forcing (j + 1) y
      rw [triangularLayerPolynomial_succ, triangularLayerPolynomial_succ]
      change fixedDegreeTransport (2 * (B₁.kappa y : ℂ)) (2 * (j + 1)) _ =
        fixedDegreeTransport (2 * (B₂.kappa y : ℂ)) (2 * (j + 1)) _
      rw [hκ hy]
      apply congrArg (fixedDegreeTransport (2 * (B₂.kappa y : ℂ)) (2 * (j + 1)))
      apply congrArg (fun R : ℂ[X] => -R)
      apply sum_congr rfl
      intro k hk
      exact B₁.forcing_congr B₂ hW hκ (ih k.val k.isLt (by omega)) (j + 1) k.val k.isLt
        (fun l hl i r => hA l (by omega) i r) (fun l hl => hτ l (by omega))
        (fun l hl i => hc l (by omega) i) hy

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Set Finset
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem forcing_top_difference {ξ : Fin n → ℝ} {U₁ U₂ W : Set Y}
    (B₁ : BoundaryLayerCoefficients ξ U₁) (B₂ : BoundaryLayerCoefficients ξ U₂)
    (hW : IsOpen W) (hκ : EqOn B₁.kappa B₂.kappa W) (a : Y → ℂ)
    (N : ℕ) (hN : 0 < N)
    (hA : ∀ l < N, ∀ i r, EqOn (B₁.inverse l i r) (B₂.inverse l i r) W)
    (hc : ∀ l < N, ∀ i, EqOn (B₁.tangentDrift l i) (B₂.tangentDrift l i) W)
    {y : Y} (hy : y ∈ W) :
    B₁.forcing N 0 (B₁.layerPolynomial a 0) y - B₂.forcing N 0 (B₂.layerPolynomial a 0) y =
      C (((∑ i, ∑ r, B₁.inverse N i r y * (ξ i : ℂ) * (ξ r : ℂ)) -
        (∑ i, ∑ r, B₂.inverse N i r y * (ξ i : ℂ) * (ξ r : ℂ))) * a y) * X ^ N -
      C (((B₁.normalDrift (N - 1) y - B₂.normalDrift (N - 1) y) / 2 * (B₁.kappa y : ℂ)) * a y) * X ^ (N - 1) := by
  let P : Y → ℂ[X] := fun z => C (a z)
  have hp₁ : B₁.layerPolynomial a 0 = P := funext (B₁.layerPolynomial_zero a)
  have hp₂ : B₂.layerPolynomial a 0 = P := funext (B₂.layerPolynomial_zero a)
  have hsp (v : Y) := profileSpatialDeriv_congr hW hκ (fun _ _ => rfl : EqOn P P W) 0 v
  have hspp (v w : Y) := profileSpatialDeriv_congr hW hκ (hsp w) 1 v
  have hm1 : N - 1 < N := by omega
  have hm2 : N - 2 < N := by omega
  have hx : B₁.crossTerm N 0 P y = B₂.crossTerm N 0 P y := by
    unfold crossTerm
    apply congrArg (fun R : ℂ[X] => C (-2 * Complex.I) * R)
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro r hr
    rw [hA (N - 1) hm1 i r hy, hsp (e r) hy]
  have hd : B₁.phaseDriftTerm N P y = B₂.phaseDriftTerm N P y := by
    unfold phaseDriftTerm
    apply congrArg (fun R : ℂ[X] => C (-Complex.I) * R)
    apply sum_congr rfl; intro i hi
    rw [hc (N - 1) hm1 i hy]
  have ht : B₁.tangentSecondTerm N 0 P y = B₂.tangentSecondTerm N 0 P y := by
    unfold tangentSecondTerm
    apply congrArg (fun R : ℂ[X] => -R)
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro r hr
    rw [hA (N - 2) hm2 i r hy, hspp (e i) (e r) hy]
  have hf : B₁.tangentFirstTerm N 0 P y = B₂.tangentFirstTerm N 0 P y := by
    unfold tangentFirstTerm
    apply congrArg (fun R : ℂ[X] => -R)
    apply sum_congr rfl; intro i hi
    rw [hc (N - 2) hm2 i hy, hsp (e i) hy]
  rw [hp₁, hp₂]
  unfold forcing
  simp only [Nat.sub_zero, Nat.mul_zero]
  rw [hx, hd, ht, hf]
  unfold principalTerm normalTerm
  simp only [hκ hy, P, profileDerivative, derivative_C, zero_sub]
  simp only [sub_div, map_sub, map_mul]
  ring

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Set Finset
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem layerForcing_top_difference {ξ : Fin n → ℝ} {U₁ U₂ W : Set Y}
    (B₁ : BoundaryLayerCoefficients ξ U₁) (B₂ : BoundaryLayerCoefficients ξ U₂)
    (hW : IsOpen W) (hκ : EqOn B₁.kappa B₂.kappa W) (a : Y → ℂ)
    (N : ℕ) (hN : 0 < N)
    (hA : ∀ l < N, ∀ i r, EqOn (B₁.inverse l i r) (B₂.inverse l i r) W)
    (hτ : ∀ l, l + 1 < N → EqOn (B₁.normalDrift l) (B₂.normalDrift l) W)
    (hc : ∀ l < N, ∀ i, EqOn (B₁.tangentDrift l i) (B₂.tangentDrift l i) W)
    {y : Y} (hy : y ∈ W) :
    B₁.layerForcing a N y - B₂.layerForcing a N y =
      C (((B₁.normalDrift (N - 1) y - B₂.normalDrift (N - 1) y) / 2 * (B₁.kappa y : ℂ)) * a y) * X ^ (N - 1) -
      C (((∑ i, ∑ r, B₁.inverse N i r y * (ξ i : ℂ) * (ξ r : ℂ)) -
        (∑ i, ∑ r, B₂.inverse N i r y * (ξ i : ℂ) * (ξ r : ℂ))) * a y) * X ^ N := by
  have hP := B₁.layerPolynomial_congr_below B₂ hW hκ a N hA hτ hc
  have hlow (k : Fin N) (hk : k.val ≠ 0) :
      B₁.forcing N k.val (B₁.layerPolynomial a k.val) y = B₂.forcing N k.val (B₂.layerPolynomial a k.val) y := by
    exact B₁.forcing_congr B₂ hW hκ (hP k.val k.isLt) N k.val k.isLt
      (fun l hl i r => hA l (by omega) i r)
      (fun l hl => hτ l (by omega)) (fun l hl i => hc l (by omega) i) hy
  have hsum : (∑ k : Fin N, B₁.forcing N k.val (B₁.layerPolynomial a k.val) y) -
      (∑ k : Fin N, B₂.forcing N k.val (B₂.layerPolynomial a k.val) y) =
      B₁.forcing N 0 (B₁.layerPolynomial a 0) y - B₂.forcing N 0 (B₂.layerPolynomial a 0) y := by
    rw [← sum_sub_distrib, sum_eq_single (⟨0, hN⟩ : Fin N)]
    · intro k hk hk0
      have hkv : k.val ≠ 0 := fun hkz => hk0 (Fin.ext hkz)
      exact sub_eq_zero.mpr (hlow k hkv)
    · intro hfalse
      exact (hfalse (mem_univ _)).elim
  change -(∑ k : Fin N, B₁.forcing N k.val (B₁.layerPolynomial a k.val) y) -
    -(∑ k : Fin N, B₂.forcing N k.val (B₂.layerPolynomial a k.val) y) = _
  calc
    _ = -((∑ k : Fin N, B₁.forcing N k.val (B₁.layerPolynomial a k.val) y) -
      (∑ k : Fin N, B₂.forcing N k.val (B₂.layerPolynomial a k.val) y)) := by ring
    _ = _ := by rw [hsum, B₁.forcing_top_difference B₂ hW hκ a N hN hA hc hy]; ring

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem traceCoefficient_top_difference {ξ : Fin n → ℝ} {U W : Set Y}
    (B₁ B₂ : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (hW : IsOpen W) (hWU : W ⊆ U) (hκ : EqOn B₁.kappa B₂.kappa W)
    (N : ℕ) (hN : 0 < N)
    (hA : ∀ l < N, ∀ i r, EqOn (B₁.inverse l i r) (B₂.inverse l i r) W)
    (hτ : ∀ l, l + 1 < N → EqOn (B₁.normalDrift l) (B₂.normalDrift l) W)
    (hc : ∀ l < N, ∀ i, EqOn (B₁.tangentDrift l i) (B₂.tangentDrift l i) W)
    {y : Y} (hy : y ∈ W) :
    B₁.traceCoefficient a N y - B₂.traceCoefficient a N y =
      a y * ((2 * (B₁.kappa y : ℂ))⁻¹ ^ N * ((N - 1).factorial : ℂ) *
        ((B₁.normalDrift (N - 1) y - B₂.normalDrift (N - 1) y) / 2 * (B₁.kappa y : ℂ)) -
      (2 * (B₁.kappa y : ℂ))⁻¹ ^ (N + 1) * (N.factorial : ℂ) *
        ((∑ i, ∑ r, B₁.inverse N i r y * (ξ i : ℂ) * (ξ r : ℂ)) -
          (∑ i, ∑ r, B₂.inverse N i r y * (ξ i : ℂ) * (ξ r : ℂ)))) := by
  have hμ : 2 * (B₁.kappa y : ℂ) ≠ 0 := B₁.transportScale_ne_zero (hWU hy)
  rw [B₁.traceCoefficient_positive hU hK a ha ha0 N hN (hWU hy),
    B₂.traceCoefficient_positive hU hK a ha ha0 N hN (hWU hy), ← hκ hy,
    ← polynomialTrace_sub _ hμ,
    B₁.layerForcing_top_difference B₂ hW hκ a N hN hA hτ hc hy,
    C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, polynomialTrace_sub _ hμ,
    polynomialTrace_monomial _ hμ, polynomialTrace_monomial _ hμ]
  rw [Nat.sub_add_cancel hN]
  ring

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

namespace CalderonPatch.BoundaryLayer

theorem trace_factorial_response (L : ℕ) (k A B T S : ℂ) (hk : k ≠ 0) :
    (2 * k)⁻¹ ^ (L + 1) * (L.factorial : ℂ) *
        ((T / (L.factorial : ℂ) - S / (L.factorial : ℂ)) / 2 * k) -
      (2 * k)⁻¹ ^ ((L + 1) + 1) * ((L + 1).factorial : ℂ) *
        (A / ((L + 1).factorial : ℂ) - B / ((L + 1).factorial : ℂ)) =
      -((A - B) - k ^ 2 * (T - S)) / (2 * k) ^ (L + 2) := by
  have hfac : (L.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero L
  have hfac' : ((L + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (L + 1)
  rw [show L + 2 = (L + 1) + 1 by omega]
  simp only [inv_pow, pow_succ]
  field_simp
  all_goals ring

end CalderonPatch.BoundaryLayer
