module

/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
public import Proof.CalderonPatch.BoundaryLayerWaves
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

open Polynomial Set Finset
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint boundary-layer transport data. Only the directions in the angular
coordinate are differentiated in the transport, while the coefficients may
also vary in the geometry parameter and in the angular frequency direction. -/
structure ParametricLayerCoefficients (U : Set E) where
  angularDirection : Fin n → E
  covector : Fin n → E → ℂ
  covector_smooth : ∀ i, ContDiffOn ℝ ∞ (covector i) U
  kappa : E → ℝ
  inverse : ℕ → Fin n → Fin n → E → ℂ
  normalDrift : ℕ → E → ℂ
  tangentDrift : ℕ → Fin n → E → ℂ
  kappa_smooth : ContDiffOn ℝ ∞ kappa U
  kappa_pos : ∀ y ∈ U, 0 < kappa y
  inverse_smooth : ∀ l i j, ContDiffOn ℝ ∞ (inverse l i j) U
  inverse_symm : ∀ l i j y, y ∈ U → inverse l i j y = inverse l j i y
  normalDrift_smooth : ∀ l, ContDiffOn ℝ ∞ (normalDrift l) U
  tangentDrift_smooth : ∀ l i, ContDiffOn ℝ ∞ (tangentDrift l i) U
  principal_squared : ∀ y ∈ U, (kappa y : ℂ) ^ 2 =
    ∑ i, ∑ j, inverse 0 i j y * covector i y * covector j y


namespace ParametricLayerCoefficients

private theorem normalProfileDerivative_regular
    {U : Set E} {P : E → ℂ[X]} {κ : E → ℝ}
    (hP : CoeffContDiffOn P U) (hκ : ContDiffOn ℝ ∞ κ U) :
    CoeffContDiffOn (fun y => profileDerivative (κ y) (P y)) U :=
  hP.derivative.sub (hP.C_mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hκ))

@[expose] def principalTerm {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (l : ℕ) (P : E → ℂ[X]) (y : E) : ℂ[X] :=
  C (∑ i, ∑ j, B.inverse l i j y * B.covector i y * B.covector j y) * X ^ l * P y

@[expose] def normalTerm {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (l : ℕ) (P : E → ℂ[X]) (y : E) : ℂ[X] :=
  C (B.normalDrift (l - 1) y / 2) * X ^ (l - 1) * profileDerivative (B.kappa y) (P y)

@[expose] def crossTerm {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (l d : ℕ) (P : E → ℂ[X]) (y : E) : ℂ[X] :=
  C (-2 * Complex.I) * ∑ i, ∑ j,
    C (B.inverse (l - 1) i j y * B.covector i y) * X ^ (l - 1) *
      profileSpatialDeriv d (B.angularDirection j) B.kappa P y

@[expose] def phaseDriftTerm {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (l : ℕ) (P : E → ℂ[X]) (y : E) : ℂ[X] :=
  C (-Complex.I) * ∑ i,
    C (B.tangentDrift (l - 1) i y * B.covector i y) * X ^ (l - 1) * P y

@[expose] def tangentSecondTerm {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (l d : ℕ) (P : E → ℂ[X]) (y : E) : ℂ[X] :=
  -(∑ i, ∑ j, C (B.inverse (l - 2) i j y) * X ^ (l - 2) *
    profileSpatialDeriv (d + 1) (B.angularDirection i) B.kappa (profileSpatialDeriv d (B.angularDirection j) B.kappa P) y)

@[expose] def tangentFirstTerm {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (l d : ℕ) (P : E → ℂ[X]) (y : E) : ℂ[X] :=
  -(∑ i, C (B.tangentDrift (l - 2) i y) * X ^ (l - 2) *
    profileSpatialDeriv d (B.angularDirection i) B.kappa P y)

@[expose] def forcing {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (j k : ℕ) (P : E → ℂ[X]) (y : E) : ℂ[X] :=
  let l := j - k
  B.principalTerm l P y + B.normalTerm l P y + B.crossTerm l (2 * k) P y +
    B.phaseDriftTerm l P y +
    (if 2 ≤ l then B.tangentSecondTerm l (2 * k) P y + B.tangentFirstTerm l (2 * k) P y else 0)

theorem principalTerm_regular {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (l : ℕ) {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.principalTerm l P) U := by
  have hc : ContDiffOn ℝ ∞
      (fun y => ∑ i, ∑ j, B.inverse l i j y * B.covector i y * B.covector j y) U :=
    ContDiffOn.sum (fun i _ => ContDiffOn.sum
      (fun j _ => ((B.inverse_smooth l i j).mul (B.covector_smooth i)).mul (B.covector_smooth j)))
  exact ((CoeffContDiffOn.const (X ^ l) U).C_mul hc).mul hP

theorem normalTerm_regular {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (l : ℕ) {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.normalTerm l P) U :=
  ((CoeffContDiffOn.const (X ^ (l - 1)) U).C_mul ((B.normalDrift_smooth (l - 1)).div_const (2 : ℂ))).mul
    (normalProfileDerivative_regular hP B.kappa_smooth)

theorem crossTerm_regular {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (hU : IsOpen U) (l d : ℕ) {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.crossTerm l d P) U := by
  apply CoeffContDiffOn.C_mul
  · apply CoeffContDiffOn.sum
    intro i hi
    apply CoeffContDiffOn.sum
    intro j hj
    exact ((CoeffContDiffOn.const (X ^ (l - 1)) U).C_mul
      ((B.inverse_smooth (l - 1) i j).mul (B.covector_smooth i))).mul
        (hP.profileSpatialDeriv hU B.kappa_smooth d (B.angularDirection j))
  · exact contDiffOn_const

theorem phaseDriftTerm_regular {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (l : ℕ) {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.phaseDriftTerm l P) U := by
  apply CoeffContDiffOn.C_mul
  · apply CoeffContDiffOn.sum
    intro i hi
    exact ((CoeffContDiffOn.const (X ^ (l - 1)) U).C_mul
      ((B.tangentDrift_smooth (l - 1) i).mul (B.covector_smooth i))).mul hP
  · exact contDiffOn_const

theorem tangentSecondTerm_regular {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (hU : IsOpen U) (l d : ℕ) {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.tangentSecondTerm l d P) U := by
  have hs : CoeffContDiffOn (fun y => ∑ i, ∑ j, C (B.inverse (l - 2) i j y) * X ^ (l - 2) *
      profileSpatialDeriv (d + 1) (B.angularDirection i) B.kappa (profileSpatialDeriv d (B.angularDirection j) B.kappa P) y) U := by
    apply CoeffContDiffOn.sum
    intro i hi
    apply CoeffContDiffOn.sum
    intro j hj
    exact ((CoeffContDiffOn.const (X ^ (l - 2)) U).C_mul (B.inverse_smooth (l - 2) i j)).mul
      ((hP.profileSpatialDeriv hU B.kappa_smooth d (B.angularDirection j)).profileSpatialDeriv hU B.kappa_smooth (d + 1) (B.angularDirection i))
  unfold tangentSecondTerm
  simpa only [zero_sub] using (CoeffContDiffOn.const 0 U).sub hs

theorem tangentFirstTerm_regular {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (hU : IsOpen U) (l d : ℕ) {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.tangentFirstTerm l d P) U := by
  have hs : CoeffContDiffOn (fun y => ∑ i, C (B.tangentDrift (l - 2) i y) * X ^ (l - 2) *
      profileSpatialDeriv d (B.angularDirection i) B.kappa P y) U := by
    apply CoeffContDiffOn.sum
    intro i hi
    exact ((CoeffContDiffOn.const (X ^ (l - 2)) U).C_mul (B.tangentDrift_smooth (l - 2) i)).mul
      (hP.profileSpatialDeriv hU B.kappa_smooth d (B.angularDirection i))
  unfold tangentFirstTerm
  simpa only [zero_sub] using (CoeffContDiffOn.const 0 U).sub hs

theorem forcing_regular {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (hU : IsOpen U) (j k : ℕ) {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.forcing j k P) U := by
  have hbase := (((B.principalTerm_regular (j - k) hP).add (B.normalTerm_regular (j - k) hP)).add
    (B.crossTerm_regular hU (j - k) (2 * k) hP)).add (B.phaseDriftTerm_regular (j - k) hP)
  unfold forcing
  dsimp only
  by_cases h : 2 ≤ j - k
  · simpa only [ite_eq_left h] using hbase.add
      ((B.tangentSecondTerm_regular hU (j - k) (2 * k) hP).add
        (B.tangentFirstTerm_regular hU (j - k) (2 * k) hP))
  · simpa only [ite_eq_right h, add_zero] using hbase

theorem forcing_zero_outside {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (j k : ℕ) (P : E → ℂ[X]) {K : Set E} (hK : IsClosed K)
    (hP0 : ∀ y ∉ K, P y = 0) {y : E} (hy : y ∉ K) : B.forcing j k P y = 0 := by
  have hd (i : Fin n) : profileSpatialDeriv (2 * k) (B.angularDirection i) B.kappa P y = 0 :=
    profileSpatialDeriv_zero_outside _ _ _ _ hK hP0 hy
  have hdd (i j : Fin n) : profileSpatialDeriv (2 * k + 1) (B.angularDirection i) B.kappa
      (profileSpatialDeriv (2 * k) (B.angularDirection j) B.kappa P) y = 0 :=
    profileSpatialDeriv_zero_outside _ _ _ _ hK
      (fun x hx => profileSpatialDeriv_zero_outside _ _ _ _ hK hP0 hx) hy
  simp [forcing, principalTerm, normalTerm, crossTerm, phaseDriftTerm, tangentSecondTerm,
    tangentFirstTerm, hP0 y hy, profileDerivative, hd, hdd]

theorem principalTerm_degree {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (l d : ℕ) (P : E → ℂ[X]) {y : E} (hp : (P y).natDegree ≤ d) :
    (B.principalTerm l P y).natDegree ≤ l + d :=
  scalar_X_pow_mul_degree_le _ _ _ _ hp

theorem normalTerm_degree {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (l d : ℕ) (P : E → ℂ[X]) {y : E} (hp : (P y).natDegree ≤ d) :
    (B.normalTerm l P y).natDegree ≤ l + d := by
  have he := scalar_X_pow_mul_degree_le (B.normalDrift (l - 1) y / 2) (l - 1) d
    (profileDerivative (B.kappa y) (P y)) ((profileDerivative_natDegree_le _ _).trans hp)
  exact he.trans (Nat.add_le_add_right (Nat.sub_le _ _) _)

theorem crossTerm_degree {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (l d : ℕ) (hl : 1 ≤ l) (P : E → ℂ[X]) {y : E} (hp : (P y).natDegree ≤ d) :
    (B.crossTerm l d P y).natDegree ≤ l + d := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (scalar_X_pow_mul_degree_le _ (l - 1) (d + 1) _
    (profileSpatialDeriv_natDegree_le d (B.angularDirection j) B.kappa P hp)).trans (by omega)

theorem phaseDriftTerm_degree {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (l d : ℕ) (P : E → ℂ[X]) {y : E} (hp : (P y).natDegree ≤ d) :
    (B.phaseDriftTerm l P y).natDegree ≤ l + d := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (scalar_X_pow_mul_degree_le _ (l - 1) d _ hp).trans (by omega)

theorem tangentSecondTerm_degree {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (l d : ℕ) (hl : 2 ≤ l) (P : E → ℂ[X]) {y : E} (hp : (P y).natDegree ≤ d) :
    (B.tangentSecondTerm l d P y).natDegree ≤ l + d := by
  rw [tangentSecondTerm, natDegree_neg]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have h₁ := profileSpatialDeriv_natDegree_le d (B.angularDirection j) B.kappa P hp
  have h₂ := profileSpatialDeriv_natDegree_le (d + 1) (B.angularDirection i) B.kappa
    (profileSpatialDeriv d (B.angularDirection j) B.kappa P) h₁
  exact (scalar_X_pow_mul_degree_le _ (l - 2) (d + 1 + 1) _ h₂).trans (by omega)

theorem tangentFirstTerm_degree {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (l d : ℕ) (hl : 2 ≤ l) (P : E → ℂ[X]) {y : E} (hp : (P y).natDegree ≤ d) :
    (B.tangentFirstTerm l d P y).natDegree ≤ l + d := by
  rw [tangentFirstTerm, natDegree_neg]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (scalar_X_pow_mul_degree_le _ (l - 2) (d + 1) _
    (profileSpatialDeriv_natDegree_le d (B.angularDirection i) B.kappa P hp)).trans (by omega)

theorem forcing_degree {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (j k : ℕ) (hkj : k < j) (P : E → ℂ[X]) {y : E} (hp : (P y).natDegree ≤ 2 * k) :
    (B.forcing j k P y).natDegree ≤ 2 * j - 1 := by
  have hbase := natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (B.principalTerm_degree (j - k) (2 * k) P hp)
        (B.normalTerm_degree (j - k) (2 * k) P hp))
      (B.crossTerm_degree (j - k) (2 * k) (by omega) P hp))
    (B.phaseDriftTerm_degree (j - k) (2 * k) P hp)
  have he : (B.forcing j k P y).natDegree ≤ j - k + 2 * k := by
    by_cases h : 2 ≤ j - k
    · simp only [forcing, ite_eq_left h]
      exact natDegree_add_le_of_degree_le hbase (natDegree_add_le_of_degree_le
        (B.tangentSecondTerm_degree (j - k) (2 * k) h P hp)
        (B.tangentFirstTerm_degree (j - k) (2 * k) h P hp))
    · simpa only [forcing, ite_eq_right h, add_zero] using hbase
  exact he.trans (by omega)

@[expose] def transportSystem {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) (K : Set E) (hK : IsClosed K) : TriangularLayerSystem U K where
  forcing := B.forcing
  regular j k _ P hP := B.forcing_regular hU j k hP
  degree j k hkj P hP y hy := B.forcing_degree j k hkj P (hP y hy)
  zero_outside j k _ P hP y hy := B.forcing_zero_outside j k P hK hP hy

@[expose] def transportScale {U : Set E} (B : ParametricLayerCoefficients (n := n) U) (y : E) : ℂ :=
  2 * (B.kappa y : ℂ)

theorem transportScale_smooth {U : Set E} (B : ParametricLayerCoefficients (n := n) U) :
    ContDiffOn ℝ ∞ B.transportScale U :=
  contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn B.kappa_smooth)

theorem transportScale_ne_zero {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    {y : E} (hy : y ∈ U) : B.transportScale y ≠ 0 :=
  mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (B.kappa_pos y hy).ne')

@[expose] def layerPolynomial {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (j : ℕ) : E → ℂ[X] :=
  triangularLayerPolynomial B.transportScale a B.forcing j

@[expose] def layerForcing {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (j : ℕ) : E → ℂ[X] :=
  totalLayerForcing B.transportScale a B.forcing j

theorem layerPolynomial_properties {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsClosed K) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) :
    CoeffContDiffOn (B.layerPolynomial a j) U ∧
      (∀ y ∈ U, (B.layerPolynomial a j y).natDegree ≤ 2 * j) ∧
      (∀ y ∉ K, B.layerPolynomial a j y = 0) :=
  triangularLayerPolynomial_properties (B.transportSystem hU K hK) B.transportScale a
    B.transportScale_smooth (fun y hy => B.transportScale_ne_zero hy) ha ha0 j

theorem layerPolynomial_zero {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (y : E) : B.layerPolynomial a 0 y = C (a y) := by
  exact congrFun (triangularLayerPolynomial_zero B.transportScale a B.forcing) y

theorem layerPolynomial_transport {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsClosed K) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) (hj : 0 < j) {y : E} (hy : y ∈ U) :
    C (2 * (B.kappa y : ℂ)) * derivative (B.layerPolynomial a j y) -
      derivative (derivative (B.layerPolynomial a j y)) = B.layerForcing a j y :=
  triangularLayerPolynomial_transport (B.transportSystem hU K hK) B.transportScale a
    B.transportScale_smooth (fun y hy => B.transportScale_ne_zero hy) ha ha0 j hj hy

theorem layerPolynomial_face_zero {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (j : ℕ) (hj : 0 < j) (y : E) : (B.layerPolynomial a j y).eval 0 = 0 :=
  triangularLayerPolynomial_face_zero B.transportScale a B.forcing j hj y

@[expose] def profile {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (j : ℕ) (x : E × ℝ) : ℂ :=
  polynomialProfile (B.kappa x.1) (B.layerPolynomial a j x.1) x.2

theorem profile_contDiffOn {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsClosed K) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) :
    ContDiffOn ℝ ∞ (B.profile a j) (U ×ˢ Set.univ) :=
  ((B.layerPolynomial_properties hU hK a ha ha0 j).1).profile B.kappa_smooth (2 * j + 1)
    (fun y hy => Nat.lt_succ_of_le ((B.layerPolynomial_properties hU hK a ha ha0 j).2.1 y hy))

theorem profile_transport {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsClosed K) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) (hj : 0 < j) {y : E} (hy : y ∈ U) (s : ℝ) :
    -deriv (deriv (fun t => B.profile a j (y, t))) s +
      B.kappa y ^ 2 • B.profile a j (y, s) = polynomialProfile (B.kappa y) (B.layerForcing a j y) s := by
  change -deriv (deriv (polynomialProfile (B.kappa y) (B.layerPolynomial a j y))) s +
    B.kappa y ^ 2 • polynomialProfile (B.kappa y) (B.layerPolynomial a j y) s = _
  rw [secondOrder_polynomialProfile, B.layerPolynomial_transport hU hK a ha ha0 j hj hy]

theorem profile_face_zero {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (a : E → ℂ) (j : ℕ) (hj : 0 < j) (y : E) : B.profile a j (y, 0) = 0 := by
  simp only [profile, polynomialProfile, mul_zero, Real.exp_zero, one_smul, Complex.ofReal_zero,
    B.layerPolynomial_face_zero a j hj y]

theorem cutoffProfile_contDiff {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsClosed K) (hKU : K ⊆ U) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (h : ℝ) :
    ContDiff ℝ ∞ (cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h) :=
  cutoffProfileFamily_contDiff hU hη B.kappa_smooth (B.layerPolynomial_properties hU hK a ha ha0 j).1
    (2 * j + 1) (fun y hy => Nat.lt_succ_of_le ((B.layerPolynomial_properties hU hK a ha ha0 j).2.1 y hy))
    hK hKU (B.layerPolynomial_properties hU hK a ha ha0 j).2.2 h

theorem cutoffProfile_hasCompactSupport {U : Set E} (B : ParametricLayerCoefficients (n := n) U)
    (hU : IsOpen U) {K : Set E} (hK : IsCompact K) (a : E → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ)
    (η : ℝ → ℝ) (hη : HasCompactSupport η) (h : ℝ) :
    HasCompactSupport (cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h) :=
  cutoffProfileFamily_hasCompactSupport η B.kappa _ h hK hη
    (B.layerPolynomial_properties hU hK.isClosed a ha ha0 j).2.2

end ParametricLayerCoefficients

end CalderonPatch.BoundaryLayer
