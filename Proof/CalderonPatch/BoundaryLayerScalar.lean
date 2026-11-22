/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
module

public import Proof.CalderonPatch.BoundaryLayerResidual

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Tactic

public section

noncomputable section

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

theorem profile_contDiff {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (hKU : K ⊆ U) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) :
    ContDiff ℝ ∞ (B.profile a j) := by
  have he := B.cutoffProfile_contDiff hU hK hKU a ha ha0 j (fun _ => 1) contDiff_const 1
  unfold cutoffProfileFamily polynomialProfileFamily at he
  unfold profile polynomialProfile
  simpa only [div_one, one_smul] using he

@[expose] def rawFiniteProfiles {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (M : ℕ) (h : ℝ) (x : Y × ℝ) : ℂ :=
  ∑ j ∈ range (M + 1), (h ^ j : ℂ) * B.profile a j x

theorem rawFiniteProfiles_contDiff {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (hKU : K ⊆ U) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (M : ℕ) (h : ℝ) :
    ContDiff ℝ ∞ (B.rawFiniteProfiles a M h) := by
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul (B.profile_contDiff hU hK hKU a ha ha0 j)

theorem hasDerivAt_rawFiniteProfiles {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (M : ℕ) (h : ℝ) (y : Y) (s : ℝ) :
    HasDerivAt (fun t : ℝ => B.rawFiniteProfiles a M h (y, t))
      (∑ j ∈ range (M + 1), (h ^ j : ℂ) *
        polynomialProfile (B.kappa y) (profileDerivative (B.kappa y) (B.layerPolynomial a j y)) s) s := by
  apply HasDerivAt.fun_sum
  intro j hj
  exact (hasDerivAt_polynomialProfile (B.kappa y) (B.layerPolynomial a j y) s).const_mul _

theorem deriv_rawFiniteProfiles {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (M : ℕ) (h : ℝ) (y : Y) :
    deriv (fun t : ℝ => B.rawFiniteProfiles a M h (y, t)) = fun s =>
      ∑ j ∈ range (M + 1), (h ^ j : ℂ) *
        polynomialProfile (B.kappa y) (profileDerivative (B.kappa y) (B.layerPolynomial a j y)) s :=
  funext (fun s => (B.hasDerivAt_rawFiniteProfiles a M h y s).deriv)

theorem rawFiniteProfiles_normal_operator {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (M : ℕ) (h : ℝ) (y : Y) (s : ℝ) :
    -deriv (deriv (fun t : ℝ => B.rawFiniteProfiles a M h (y, t))) s +
      B.kappa y ^ 2 • B.rawFiniteProfiles a M h (y, s) =
      ∑ j ∈ range (M + 1), (h ^ j : ℂ) * polynomialProfile (B.kappa y)
        (C (2 * (B.kappa y : ℂ)) * derivative (B.layerPolynomial a j y) -
          derivative (derivative (B.layerPolynomial a j y))) s := by
  have hd : HasDerivAt
      (fun t : ℝ => ∑ j ∈ range (M + 1), (h ^ j : ℂ) *
        polynomialProfile (B.kappa y) (profileDerivative (B.kappa y) (B.layerPolynomial a j y)) t)
      (∑ j ∈ range (M + 1), (h ^ j : ℂ) * polynomialProfile (B.kappa y)
        (profileDerivative (B.kappa y) (profileDerivative (B.kappa y) (B.layerPolynomial a j y))) s) s := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hasDerivAt_polynomialProfile _ _ s).const_mul _
  rw [B.deriv_rawFiniteProfiles, hd.deriv]
  unfold rawFiniteProfiles profile
  rw [smul_sum, ← sum_neg_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  have he := secondOrder_polynomialProfile (B.kappa y) (B.layerPolynomial a j y) s
  rw [deriv_polynomialProfile, deriv_polynomialProfile] at he
  rw [← he]
  simp only [Complex.real_smul, mul_add, mul_neg]
  ring

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Finset Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer

abbrev LayerJetIndex (n : ℕ) := Unit ⊕ (Unit ⊕ (Fin n ⊕ (Fin n × Fin n)))

theorem polynomialProfile_X_mul (κ : ℝ) (m : ℕ) (p : ℂ[X]) (s : ℝ) :
    polynomialProfile κ (X ^ m * p) s = (s : ℂ) ^ m * polynomialProfile κ p s := by
  simp only [polynomialProfile, eval_mul, eval_pow, eval_X, Complex.real_smul]
  ring

namespace BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

@[expose] def layerJetPolynomial {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (j : ℕ) : LayerJetIndex n → Y → ℂ[X]
  | .inl _ => B.layerPolynomial a j
  | .inr (.inl _) => fun y => profileDerivative (B.kappa y) (B.layerPolynomial a j y)
  | .inr (.inr (.inl i)) => profileSpatialDeriv (2 * j) (e i) B.kappa (B.layerPolynomial a j)
  | .inr (.inr (.inr ij)) => profileSpatialDeriv (2 * j + 1) (e ij.1) B.kappa
      (profileSpatialDeriv (2 * j) (e ij.2) B.kappa (B.layerPolynomial a j))

theorem layerJetPolynomial_regular {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) (q : LayerJetIndex n) :
    CoeffContDiffOn (B.layerJetPolynomial a j q) U := by
  have hp := (B.layerPolynomial_properties hU hK a ha ha0 j).1
  rcases q with u | q
  · exact hp
  rcases q with u | q
  · exact hp.normalProfileDerivative B.kappa_smooth
  rcases q with i | ij
  · exact hp.profileSpatialDeriv hU B.kappa_smooth (2 * j) (e i)
  · exact (hp.profileSpatialDeriv hU B.kappa_smooth (2 * j) (e ij.2)).profileSpatialDeriv
      hU B.kappa_smooth (2 * j + 1) (e ij.1)

theorem layerJetPolynomial_degree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) (q : LayerJetIndex n)
    {y : Y} (hy : y ∈ U) : (B.layerJetPolynomial a j q y).natDegree ≤ 2 * j + 2 := by
  have hp := (B.layerPolynomial_properties hU hK a ha ha0 j).2.1 y hy
  rcases q with u | q
  · exact hp.trans (by omega)
  rcases q with u | q
  · exact (profileDerivative_natDegree_le _ _).trans (hp.trans (by omega))
  rcases q with i | ij
  · exact (profileSpatialDeriv_natDegree_le (2 * j) (e i) B.kappa _ hp).trans (by omega)
  · have hd := profileSpatialDeriv_natDegree_le (2 * j) (e ij.2) B.kappa _ hp
    exact (profileSpatialDeriv_natDegree_le (2 * j + 1) (e ij.1) B.kappa _ hd).trans (by omega)

theorem exists_uniform_layerJet_moment_exp_bound {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (M m : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ j : Fin (M + 1), ∀ q : LayerJetIndex n, ∀ y ∈ K, ∀ s : ℝ, 0 ≤ s →
      s ^ m * ‖polynomialProfile (B.kappa y) (B.layerJetPolynomial a j.val q y) s‖ ≤ C * Real.exp (-c * s) := by
  let Q : (Fin (M + 1) × LayerJetIndex n) → Y → ℂ[X] :=
    fun i y => X ^ m * B.layerJetPolynomial a i.1.val i.2 y
  have hQ (i : Fin (M + 1) × LayerJetIndex n) : CoeffContDiffOn (Q i) U :=
    (CoeffContDiffOn.const (X ^ m) U).mul (B.layerJetPolynomial_regular hU hK.isClosed a ha ha0 i.1.val i.2)
  have hD (i : Fin (M + 1) × LayerJetIndex n) (y : Y) (hy : y ∈ K) :
      (Q i y).natDegree < m + 2 * M + 3 := by
    have hd := B.layerJetPolynomial_degree hU hK.isClosed a ha ha0 i.1.val i.2 (hKU hy)
    have he : (Q i y).natDegree ≤ m + (2 * i.1.val + 2) :=
      natDegree_mul_le.trans (add_le_add (natDegree_X_pow_le m) hd)
    exact he.trans_lt (by have hi := i.1.isLt; omega)
  obtain ⟨c, C, hc, hC, hb⟩ := exists_uniform_finite_profile_exp_bound hK hKU B.kappa_smooth B.kappa_pos
    Q hQ (fun _ => m + 2 * M + 3) hD
  refine ⟨c, C, hc, hC, ?_⟩
  intro j q y hy s hs
  have he : ‖polynomialProfile (B.kappa y) (Q (j, q) y) s‖ =
      s ^ m * ‖polynomialProfile (B.kappa y) (B.layerJetPolynomial a j.val q y) s‖ := by
    change ‖polynomialProfile (B.kappa y) (X ^ m * B.layerJetPolynomial a j.val q y) s‖ = _
    rw [polynomialProfile_X_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  rw [← he]
  exact hb (j, q) y hy s hs

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer

theorem hasDerivAt_normal_scale {f : ℝ → ℂ} {f' : ℂ} (h t : ℝ)
    (hf : HasDerivAt f f' (t / h)) :
    HasDerivAt (fun r : ℝ => f (r / h)) (f' / (h : ℂ)) t := by
  have hs : HasDerivAt (fun r : ℝ => r / h) (1 / h) t := by
    simpa only [id_eq] using (hasDerivAt_id t).div_const h
  have hd := hf.scomp t hs
  have he : (1 / h) • f' = f' / (h : ℂ) := by
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  rw [he] at hd
  exact hd

theorem deriv_const_mul_normal_scale (c : ℂ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (h t : ℝ) :
    deriv (fun r : ℝ => c * f (r / h)) t = (c / (h : ℂ)) * deriv f (t / h) := by
  have hd := (hasDerivAt_normal_scale h t ((hf.differentiable (by decide) (t / h)).hasDerivAt)).const_mul c
  rw [hd.deriv]
  ring

theorem deriv_twice_const_mul_normal_scale (c : ℂ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (h t : ℝ) :
    deriv (deriv (fun r : ℝ => c * f (r / h))) t =
      (c / (h : ℂ) ^ 2) * deriv (deriv f) (t / h) := by
  have he : deriv (fun r : ℝ => c * f (r / h)) = fun r => (c / (h : ℂ)) * deriv f (r / h) :=
    funext (fun r => deriv_const_mul_normal_scale c hf h r)
  have hdf : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  rw [he, deriv_const_mul_normal_scale (c / (h : ℂ)) hdf h t]
  simp only [div_eq_mul_inv, pow_two, mul_inv_rev]
  ring

theorem normal_scale_times_sq {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) {h : ℝ} (hh : h ≠ 0) (t : ℝ) :
    (h : ℂ) ^ 2 * deriv (deriv (fun r : ℝ => c * f (r / h))) t = c * deriv (deriv f) (t / h) := by
  rw [deriv_twice_const_mul_normal_scale c hf]
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp

end CalderonPatch.BoundaryLayer

open Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

@[expose] def splitFirst (V : Y × ℝ → ℂ) (y : Y) (t : ℝ) (i : Fin n) : ℂ :=
  fderiv ℝ (fun z => V (z, t)) y (e i)

@[expose] def splitSecond (V : Y × ℝ → ℂ) (y : Y) (t : ℝ) (i j : Fin n) : ℂ :=
  fderiv ℝ (fun z => fderiv ℝ (fun w => V (w, t)) z (e j)) y (e i)

@[expose] def splitNormal (V : Y × ℝ → ℂ) (y : Y) (t : ℝ) : ℂ :=
  deriv (fun r : ℝ => V (y, r)) t

@[expose] def splitNormalSecond (V : Y × ℝ → ℂ) (y : Y) (t : ℝ) : ℂ :=
  deriv (deriv (fun r : ℝ => V (y, r))) t

@[expose] def scaledPlaneWave (ξ : Fin n → ℝ) (h : ℝ) (V : Y × ℝ → ℂ) (x : Y × ℝ) : ℂ :=
  tangentialWave ξ h x.1 * V (x.1, x.2 / h)

theorem splitNormal_scaledPlaneWave (ξ : Fin n → ℝ) (h : ℝ)
    {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) (y : Y) (t : ℝ) :
    splitNormal (scaledPlaneWave ξ h V) y t =
      (tangentialWave ξ h y / (h : ℂ)) * splitNormal V y (t / h) :=
by
  have hmap : ContDiff ℝ ∞ (fun r : ℝ => ((y, r) : Y × ℝ)) := contDiff_const.prodMk contDiff_id
  have hs : ContDiff ℝ ∞ (fun r : ℝ => V (y, r)) := hV.comp hmap
  unfold splitNormal scaledPlaneWave
  exact deriv_const_mul_normal_scale (f := fun r : ℝ => V (y, r)) (tangentialWave ξ h y) hs h t

theorem splitNormalSecond_scaledPlaneWave (ξ : Fin n → ℝ) (h : ℝ)
    {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) (y : Y) (t : ℝ) :
    splitNormalSecond (scaledPlaneWave ξ h V) y t =
      (tangentialWave ξ h y / (h : ℂ) ^ 2) * splitNormalSecond V y (t / h) :=
by
  have hmap : ContDiff ℝ ∞ (fun r : ℝ => ((y, r) : Y × ℝ)) := contDiff_const.prodMk contDiff_id
  have hs : ContDiff ℝ ∞ (fun r : ℝ => V (y, r)) := hV.comp hmap
  unfold splitNormalSecond scaledPlaneWave
  exact deriv_twice_const_mul_normal_scale (f := fun r : ℝ => V (y, r)) (tangentialWave ξ h y) hs h t

theorem splitFirst_scaledPlaneWave (ξ : Fin n → ℝ) (h : ℝ)
    {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) (y : Y) (t : ℝ) (i : Fin n) :
    splitFirst (scaledPlaneWave ξ h V) y t i = tangentialWave ξ h y *
      (phaseRate ξ h (e i) * V (y, t / h) + splitFirst V y (t / h) i) :=
by
  have hs : ContDiff ℝ ∞ (fun z : Y => V (z, t / h)) := hV.comp (contDiff_id.prodMk contDiff_const)
  exact fderiv_tangentialWave_mul_direction ξ h (hs.differentiable (by decide) y) (e i)

theorem splitSecond_scaledPlaneWave (ξ : Fin n → ℝ) (h : ℝ)
    {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) (y : Y) (t : ℝ) (i j : Fin n) :
    splitSecond (scaledPlaneWave ξ h V) y t i j = tangentialWave ξ h y *
      (phaseRate ξ h (e i) * phaseRate ξ h (e j) * V (y, t / h) +
        phaseRate ξ h (e j) * splitFirst V y (t / h) i +
        phaseRate ξ h (e i) * splitFirst V y (t / h) j + splitSecond V y (t / h) i j) :=
by
  have hs : ContDiff ℝ ∞ (fun z : Y => V (z, t / h)) := hV.comp (contDiff_id.prodMk contDiff_const)
  exact fderiv_twice_tangentialWave_mul_direction ξ h isOpen_univ hs.contDiffOn (mem_univ y) (e i) (e j)

end CalderonPatch.BoundaryLayer

open Polynomial Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem layerJet_normal_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (j : ℕ) (y : Y) (s : ℝ) :
    polynomialProfile (B.kappa y) (B.layerJetPolynomial a j (.inr (.inl ())) y) s =
      splitNormal (B.profile a j) y s := by
  change polynomialProfile (B.kappa y) (profileDerivative (B.kappa y) (B.layerPolynomial a j y)) s =
    deriv (polynomialProfile (B.kappa y) (B.layerPolynomial a j y)) s
  rw [deriv_polynomialProfile]

theorem layerJet_tangent_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) {y : Y} (hy : y ∈ U) (s : ℝ) (i : Fin n) :
    polynomialProfile (B.kappa y) (B.layerJetPolynomial a j (.inr (.inr (.inl i))) y) s =
      splitFirst (B.profile a j) y s i :=
  (fderiv_polynomialProfile_direction hU (B.layerPolynomial_properties hU hK a ha ha0 j).1
    B.kappa_smooth (2 * j) (B.layerPolynomial_properties hU hK a ha ha0 j).2.1 hy s (e i)).symm

theorem layerJet_second_read {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) {y : Y} (hy : y ∈ U) (s : ℝ) (i l : Fin n) :
    polynomialProfile (B.kappa y) (B.layerJetPolynomial a j (.inr (.inr (.inr (i, l)))) y) s =
      splitSecond (B.profile a j) y s i l :=
  (fderiv_twice_polynomialProfile_direction hU (B.layerPolynomial_properties hU hK a ha ha0 j).1
    B.kappa_smooth (2 * j) (B.layerPolynomial_properties hU hK a ha ha0 j).2.1 hy s (e i) (e l)).symm

theorem exists_uniform_actual_layerJet_moment_exp_bound {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsCompact K) (hKU : K ⊆ U) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (M m : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ j : ℕ, j ≤ M → ∀ y ∈ K, ∀ s : ℝ, 0 ≤ s →
      s ^ m * ‖B.profile a j (y, s)‖ ≤ C * Real.exp (-c * s) ∧
      s ^ m * ‖splitNormal (B.profile a j) y s‖ ≤ C * Real.exp (-c * s) ∧
      (∀ i, s ^ m * ‖splitFirst (B.profile a j) y s i‖ ≤ C * Real.exp (-c * s)) ∧
      (∀ i l, s ^ m * ‖splitSecond (B.profile a j) y s i l‖ ≤ C * Real.exp (-c * s)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := B.exists_uniform_layerJet_moment_exp_bound hU hK hKU a ha ha0 M m
  refine ⟨c, C, hc, hC, ?_⟩
  intro j hj y hy s hs
  let J : Fin (M + 1) := ⟨j, by omega⟩
  refine ⟨hb J (.inl ()) y hy s hs, ?_, ?_, ?_⟩
  · have he := hb J (.inr (.inl ())) y hy s hs
    rw [B.layerJet_normal_read] at he
    exact he
  · intro i
    have he := hb J (.inr (.inr (.inl i))) y hy s hs
    rw [B.layerJet_tangent_read hU hK.isClosed a ha ha0 j (hKU hy) s i] at he
    exact he
  · intro i l
    have he := hb J (.inr (.inr (.inr (i, l)))) y hy s hs
    rw [B.layerJet_second_read hU hK.isClosed a ha ha0 j (hKU hy) s i l] at he
    exact he

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem phaseRate_basis (ξ : Fin n → ℝ) (h : ℝ) (i : Fin n) :
    phaseRate ξ h (e i) = Complex.I * (ξ i : ℂ) / (h : ℂ) := by
  rw [phaseRate, tangentialPhaseRead_basis]
  simp only [Complex.ofReal_div, mul_div_assoc]

theorem symmetric_cross_sum (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A i j = A j i)
    (ξ : Fin n → ℝ) (g : Fin n → ℂ) :
    (∑ i, ∑ j, A i j * (ξ j : ℂ) * g i) = ∑ i, ∑ j, A i j * (ξ i : ℂ) * g j := by
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  exact congrArg (fun z : ℂ => z * (ξ i : ℂ) * g j) (hA j i)

@[expose] def complexSplitOperator (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (c : Fin n → ℂ)
    (V : Y × ℝ → ℂ) (y : Y) (t : ℝ) : ℂ :=
  -splitNormalSecond V y t - (∑ i, ∑ j, A i j * splitSecond V y t i j) +
    τ / 2 * splitNormal V y t - ∑ i, c i * splitFirst V y t i

@[expose] def conjugatedSplitOperator (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (c : Fin n → ℂ)
    (ξ : Fin n → ℝ) (h : ℝ) (V : Y × ℝ → ℂ) (y : Y) (s : ℝ) : ℂ :=
  -splitNormalSecond V y s + (∑ i, ∑ j, A i j * (ξ i : ℂ) * (ξ j : ℂ)) * V (y, s) +
    (h : ℂ) * τ / 2 * splitNormal V y s -
    (2 * Complex.I * (h : ℂ)) * (∑ i, ∑ j, A i j * (ξ i : ℂ) * splitFirst V y s j) -
    (Complex.I * (h : ℂ)) * (∑ i, c i * (ξ i : ℂ) * V (y, s)) -
    (h : ℂ) ^ 2 * (∑ i, ∑ j, A i j * splitSecond V y s i j) -
    (h : ℂ) ^ 2 * (∑ i, c i * splitFirst V y s i)

theorem scaled_second_sum (A : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0)
    {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) (y : Y) (t : ℝ) :
    (h : ℂ) ^ 2 * (∑ i, ∑ j, A i j * splitSecond (scaledPlaneWave ξ h V) y t i j) =
    tangentialWave ξ h y *
      (-(∑ i, ∑ j, A i j * (ξ i : ℂ) * (ξ j : ℂ)) * V (y, t / h) +
        (Complex.I * (h : ℂ)) * (∑ i, ∑ j, A i j * (ξ j : ℂ) * splitFirst V y (t / h) i) +
        (Complex.I * (h : ℂ)) * (∑ i, ∑ j, A i j * (ξ i : ℂ) * splitFirst V y (t / h) j) +
        (h : ℂ) ^ 2 * (∑ i, ∑ j, A i j * splitSecond V y (t / h) i j)) := by
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hl (i j : Fin n) : (h : ℂ) ^ 2 * (A i j * splitSecond (scaledPlaneWave ξ h V) y t i j) =
      tangentialWave ξ h y * (-(A i j * (ξ i : ℂ) * (ξ j : ℂ)) * V (y, t / h) +
        (Complex.I * (h : ℂ)) * (A i j * (ξ j : ℂ) * splitFirst V y (t / h) i) +
        (Complex.I * (h : ℂ)) * (A i j * (ξ i : ℂ) * splitFirst V y (t / h) j) +
        (h : ℂ) ^ 2 * (A i j * splitSecond V y (t / h) i j)) := by
    rw [splitSecond_scaledPlaneWave ξ h hV, phaseRate_basis, phaseRate_basis]
    field_simp [hh']
    ring_nf
    simp only [Complex.I_sq]
    all_goals ring
  calc
    _ = ∑ i, ∑ j, (h : ℂ) ^ 2 * (A i j * splitSecond (scaledPlaneWave ξ h V) y t i j) := by simp only [mul_sum]
    _ = ∑ i, ∑ j, tangentialWave ξ h y * (-(A i j * (ξ i : ℂ) * (ξ j : ℂ)) * V (y, t / h) +
        (Complex.I * (h : ℂ)) * (A i j * (ξ j : ℂ) * splitFirst V y (t / h) i) +
        (Complex.I * (h : ℂ)) * (A i j * (ξ i : ℂ) * splitFirst V y (t / h) j) +
        (h : ℂ) ^ 2 * (A i j * splitSecond V y (t / h) i j)) := by
      apply sum_congr rfl
      intro i hi
      exact sum_congr rfl (fun j _ => hl i j)
    _ = _ := by
      simp only [sum_add_distrib, sum_neg_distrib, mul_add, mul_neg, neg_mul, mul_sum, sum_mul, mul_assoc]

theorem scaled_first_sum (c : Fin n → ℂ) (ξ : Fin n → ℝ) {h : ℝ} (hh : h ≠ 0)
    {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) (y : Y) (t : ℝ) :
    (h : ℂ) ^ 2 * (∑ i, c i * splitFirst (scaledPlaneWave ξ h V) y t i) =
      tangentialWave ξ h y * ((Complex.I * (h : ℂ)) * (∑ i, c i * (ξ i : ℂ) * V (y, t / h)) +
        (h : ℂ) ^ 2 * (∑ i, c i * splitFirst V y (t / h) i)) := by
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hl (i : Fin n) : (h : ℂ) ^ 2 * (c i * splitFirst (scaledPlaneWave ξ h V) y t i) =
      tangentialWave ξ h y * ((Complex.I * (h : ℂ)) * (c i * (ξ i : ℂ) * V (y, t / h)) +
        (h : ℂ) ^ 2 * (c i * splitFirst V y (t / h) i)) := by
    rw [splitFirst_scaledPlaneWave ξ h hV, phaseRate_basis]
    field_simp [hh']
    all_goals ring
  calc
    _ = ∑ i, (h : ℂ) ^ 2 * (c i * splitFirst (scaledPlaneWave ξ h V) y t i) := by rw [mul_sum]
    _ = ∑ i, tangentialWave ξ h y * ((Complex.I * (h : ℂ)) * (c i * (ξ i : ℂ) * V (y, t / h)) +
        (h : ℂ) ^ 2 * (c i * splitFirst V y (t / h) i)) := sum_congr rfl (fun i _ => hl i)
    _ = _ := by simp only [sum_add_distrib, mul_add, mul_sum, mul_assoc]

theorem complexSplitOperator_scaledPlaneWave (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A i j = A j i) (τ : ℂ) (c : Fin n → ℂ) (ξ : Fin n → ℝ)
    {h : ℝ} (hh : h ≠ 0) {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) (y : Y) (t : ℝ) :
    (h : ℂ) ^ 2 * complexSplitOperator A τ c (scaledPlaneWave ξ h V) y t =
      tangentialWave ξ h y * conjugatedSplitOperator A τ c ξ h V y (t / h) := by
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hN : (h : ℂ) ^ 2 * splitNormalSecond (scaledPlaneWave ξ h V) y t =
      tangentialWave ξ h y * splitNormalSecond V y (t / h) := by
    rw [splitNormalSecond_scaledPlaneWave ξ h hV]
    field_simp [hh']
  have hD : (h : ℂ) ^ 2 * (τ / 2 * splitNormal (scaledPlaneWave ξ h V) y t) =
      tangentialWave ξ h y * ((h : ℂ) * τ / 2 * splitNormal V y (t / h)) := by
    rw [splitNormal_scaledPlaneWave ξ h hV]
    field_simp [hh']
    all_goals ring
  unfold complexSplitOperator
  simp only [mul_sub, mul_add, mul_neg]
  rw [hN, scaled_second_sum A ξ hh hV, hD, scaled_first_sum c ξ hh hV,
    symmetric_cross_sum A hA ξ (splitFirst V y (t / h))]
  unfold conjugatedSplitOperator
  ring

end CalderonPatch.BoundaryLayer

open Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

@[expose] def scalarCoefficientDifference (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (c : Fin n → ℂ)
    (ξ : Fin n → ℝ) (h : ℝ) (V : Y × ℝ → ℂ) (y : Y) (s : ℝ) : ℂ :=
  (∑ i, ∑ j, A i j * (ξ i : ℂ) * (ξ j : ℂ)) * V (y, s) +
    (h : ℂ) * τ / 2 * splitNormal V y s -
    (2 * Complex.I * (h : ℂ)) * (∑ i, ∑ j, A i j * (ξ i : ℂ) * splitFirst V y s j) -
    (Complex.I * (h : ℂ)) * (∑ i, c i * (ξ i : ℂ) * V (y, s)) -
    (h : ℂ) ^ 2 * (∑ i, ∑ j, A i j * splitSecond V y s i j) -
    (h : ℂ) ^ 2 * (∑ i, c i * splitFirst V y s i)

theorem conjugatedSplitOperator_sub (A B : Matrix (Fin n) (Fin n) ℂ) (τ σ : ℂ)
    (c d : Fin n → ℂ) (ξ : Fin n → ℝ) (h : ℝ) (V : Y × ℝ → ℂ) (y : Y) (s : ℝ) :
    conjugatedSplitOperator A τ c ξ h V y s - conjugatedSplitOperator B σ d ξ h V y s =
      scalarCoefficientDifference (A - B) (τ - σ) (c - d) ξ h V y s := by
  unfold conjugatedSplitOperator scalarCoefficientDifference
  simp only [Matrix.sub_apply, Pi.sub_apply, sub_mul, sum_sub_distrib]
  ring

@[expose] def scalarFrequencyWeight (ξ : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, |ξ i| * |ξ j|) + 1 + 2 * (∑ i, ∑ _j : Fin n, |ξ i|) +
    (∑ i, |ξ i|) + (∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ)) + (∑ _i : Fin n, (1 : ℝ))

theorem scalarFrequencyWeight_nonneg (ξ : Fin n → ℝ) : 0 ≤ scalarFrequencyWeight ξ := by
  unfold scalarFrequencyWeight
  positivity

theorem scalarCoefficientDifference_product_bound
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (c : Fin n → ℂ) (ξ : Fin n → ℝ)
    {h R : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (hR : 0 ≤ R)
    (V : Y × ℝ → ℂ) (y : Y) (s : ℝ)
    (hv : ∀ i j, ‖A i j‖ * ‖V (y, s)‖ ≤ R)
    (hn : ‖τ‖ * ‖splitNormal V y s‖ ≤ R)
    (ht : ∀ i j, ‖A i j‖ * ‖splitFirst V y s j‖ ≤ R)
    (hc : ∀ i, ‖c i‖ * ‖V (y, s)‖ ≤ R)
    (htt : ∀ i j, ‖A i j‖ * ‖splitSecond V y s i j‖ ≤ R)
    (hf : ∀ i, ‖c i‖ * ‖splitFirst V y s i‖ ≤ R) :
    ‖scalarCoefficientDifference A τ c ξ h V y s‖ ≤ R * scalarFrequencyWeight ξ := by
  have hnorm : ‖(h : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh] using hh1
  have hnorm0 : 0 ≤ ‖(h : ℂ)‖ := norm_nonneg _
  have hp : ‖(∑ i, ∑ j, A i j * (ξ i : ℂ) * (ξ j : ℂ)) * V (y, s)‖ ≤
      R * (∑ i, ∑ j, |ξ i| * |ξ j|) := by
    rw [sum_mul]
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum; intro i hi
    rw [sum_mul, mul_sum]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro j hj
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = (‖A i j‖ * ‖V (y, s)‖) * (|ξ i| * |ξ j|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hv i j) (by positivity)
  have hn' : ‖(h : ℂ) * τ / 2 * splitNormal V y s‖ ≤ R := by
    simp only [norm_mul, norm_div, Complex.norm_ofNat]
    calc
      _ = ‖(h : ℂ)‖ / 2 * (‖τ‖ * ‖splitNormal V y s‖) := by ring
      _ ≤ (1 : ℝ) / 2 * R := mul_le_mul (by gcongr) hn (by positivity) (by positivity)
      _ ≤ R := by linarith
  have hx : ‖(2 * Complex.I * (h : ℂ)) * (∑ i, ∑ j, A i j * (ξ i : ℂ) * splitFirst V y s j)‖ ≤
      2 * (R * (∑ i, ∑ _j : Fin n, |ξ i|)) := by
    rw [norm_mul]
    have hb : ‖∑ i, ∑ j, A i j * (ξ i : ℂ) * splitFirst V y s j‖ ≤ R * ∑ i, ∑ _j : Fin n, |ξ i| := by
      apply (norm_sum_le _ _).trans
      rw [mul_sum]
      apply sum_le_sum; intro i hi
      apply (norm_sum_le _ _).trans
      rw [mul_sum]
      apply sum_le_sum; intro j hj
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ = (‖A i j‖ * ‖splitFirst V y s j‖) * |ξ i| := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (ht i j) (abs_nonneg _)
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    exact mul_le_mul (by nlinarith) hb (norm_nonneg _) (by positivity)
  have hc' : ‖(Complex.I * (h : ℂ)) * (∑ i, c i * (ξ i : ℂ) * V (y, s))‖ ≤
      R * (∑ i, |ξ i|) := by
    rw [norm_mul]
    have hb : ‖∑ i, c i * (ξ i : ℂ) * V (y, s)‖ ≤ R * ∑ i, |ξ i| := by
      apply (norm_sum_le _ _).trans
      rw [mul_sum]
      apply sum_le_sum; intro i hi
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ = (‖c i‖ * ‖V (y, s)‖) * |ξ i| := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)
    simp only [norm_mul, Complex.norm_I, one_mul]
    exact (mul_le_mul hnorm hb (norm_nonneg _) (by positivity)).trans_eq (one_mul _)
  have h2 : ‖(h : ℂ) ^ 2‖ ≤ 1 := by simpa only [norm_pow, one_pow] using pow_le_pow_left₀ hnorm0 hnorm 2
  have hs : ‖(h : ℂ) ^ 2 * (∑ i, ∑ j, A i j * splitSecond V y s i j)‖ ≤
      R * (∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ)) := by
    rw [norm_mul]
    calc
      _ ≤ 1 * (∑ _i : Fin n, ∑ _j : Fin n, R) := by
        apply mul_le_mul h2 _ (norm_nonneg _) (by positivity)
        apply (norm_sum_le _ _).trans
        apply sum_le_sum; intro i hi
        apply (norm_sum_le _ _).trans
        apply sum_le_sum; intro j hj
        rw [norm_mul]
        exact htt i j
      _ = _ := by simp only [mul_sum, mul_one, one_mul]
  have hf' : ‖(h : ℂ) ^ 2 * (∑ i, c i * splitFirst V y s i)‖ ≤
      R * (∑ _i : Fin n, (1 : ℝ)) := by
    rw [norm_mul]
    calc
      _ ≤ 1 * (∑ _i : Fin n, R) := by
        apply mul_le_mul h2 _ (norm_nonneg _) (by positivity)
        apply (norm_sum_le _ _).trans
        apply sum_le_sum; intro i hi
        rw [norm_mul]
        exact hf i
      _ = _ := by simp only [mul_sum, mul_one, one_mul]
  unfold scalarCoefficientDifference
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ _ := add_le_add (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl) le_rfl
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hp hn') hx) hc') hs) hf'
    _ = _ := by unfold scalarFrequencyWeight; ring

theorem scalarCoefficientDifference_bound
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (c : Fin n → ℂ) (ξ : Fin n → ℝ)
    {h E J : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (hE : 0 ≤ E) (hJ : 0 ≤ J)
    (hA : ∀ i j, ‖A i j‖ ≤ E) (hτ : ‖τ‖ ≤ E) (hc : ∀ i, ‖c i‖ ≤ E)
    (V : Y × ℝ → ℂ) (y : Y) (s : ℝ)
    (hv : ‖V (y, s)‖ ≤ J) (hn : ‖splitNormal V y s‖ ≤ J)
    (ht : ∀ i, ‖splitFirst V y s i‖ ≤ J)
    (htt : ∀ i j, ‖splitSecond V y s i j‖ ≤ J) :
    ‖scalarCoefficientDifference A τ c ξ h V y s‖ ≤ E * J * scalarFrequencyWeight ξ := by
  apply scalarCoefficientDifference_product_bound A τ c ξ hh hh1 (mul_nonneg hE hJ) V y s
  · exact fun i j => mul_le_mul (hA i j) hv (norm_nonneg _) hE
  · exact mul_le_mul hτ hn (norm_nonneg _) hE
  · exact fun i j => mul_le_mul (hA i j) (ht j) (norm_nonneg _) hE
  · exact fun i => mul_le_mul (hc i) hv (norm_nonneg _) hE
  · exact fun i j => mul_le_mul (hA i j) (htt i j) (norm_nonneg _) hE
  · exact fun i => mul_le_mul (hc i) (ht i) (norm_nonneg _) hE

end CalderonPatch.BoundaryLayer
