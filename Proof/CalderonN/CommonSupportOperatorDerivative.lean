module

public import Proof.CalderonN.CommonSupportMultiplierDerivative
public import Proof.CalderonN.SharpBallCoefficientOperator

import Mathlib.Tactic

/-! Adapted from `Proof/CommonSupportOperatorDerivative.lean` in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Matrix.Norms.Elementwise Topology
namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim]


variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Actual matrix multiplier derivative, using only true parameter derivatives
    of the coefficient's local C0/C1 jets. -/
theorem norm_fderiv_commonSupport_matrixMultiplier_zero_le
    (hcalc : FixedSobolevCalculus dim) (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → a (p,z) = 0)
    (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : (I dim),∀ k : Fin 2,∀ x ∈ ((fixedBallOpens dim):Set (X dim)),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖fderiv ℝ (fun t => coefficientMatrixMultiplierL hcalc 0
      (commonSupportMatrixFamily 2 a ha K hK hz t)) p‖ ≤ 4*q := by
  let M := fun t => coefficientMatrixMultiplierL hcalc 0
    (commonSupportMatrixFamily 2 a ha K hK hz t)
  have hm : ContDiff ℝ ∞ M := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc 1
      (fun v => a v i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
      (fun t z h => by rw [hz t z h];rfl)
  have hDiff := hm.differentiable (by simp) p
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (4*q)*‖b‖)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (4*q)*‖b‖)).mpr
  intro j
  have hi := fderiv_apply hDiff i
  have hij := fderiv_apply ((differentiableAt_pi.mp hDiff) i) j
  have hAt : (fderiv ℝ M p b) i j = fderiv ℝ (fun t => M t i j) p b := by
    have h1 := congrArg (fun L => (L b) j) hi
    have h2 := congrArg (fun L => L b) hij
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] at h1 h2
    exact h1.symm.trans h2.symm
  rw [hAt]
  have hNorm := norm_fderiv_commonSupport_coefficientMultiplier_one_le hcalc
    (fun v => a v i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
    (fun t z h => by rw [hz t z h];rfl) p q hq (hJets i j)
  exact (ContinuousLinearMap.le_opNorm _ b).trans
    (mul_le_mul_of_nonneg_right hNorm (norm_nonneg b))

/-- The actual H2-to-L2 Dirichlet operator derivative has a local C1 bound,
    with no dependence on higher jets or on the exterior coefficient cutoff. -/
theorem norm_fderiv_commonSupport_strongOperator_zero_le
    (hcalc : FixedSobolevCalculus dim) (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → a (p,z) = 0)
    (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : (I dim),∀ k : Fin 2,∀ x ∈ ((fixedBallOpens dim):Set (X dim)),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖fderiv ℝ (fun t => strongDirichletOperator hcalc 0
      (commonSupportMatrixFamily 2 a ha K hK hz t)) p‖ ≤ 2*strongC1OperatorBudget hcalc*q := by
  let M := fun t => coefficientMatrixMultiplierL hcalc 0
    (commonSupportMatrixFamily 2 a ha K hK hz t)
  have hm : ContDiff ℝ ∞ M := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc 1
      (fun v => a v i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
      (fun t z h => by rw [hz t z h];rfl)
  have hD := ((unitBallDivergenceL hcalc 0).hasFDerivAt.comp p
    (hm.differentiable (by simp) p).hasFDerivAt).fderiv
  change ‖fderiv ℝ (fun t => unitBallDivergenceL hcalc 0 (M t)) p‖ ≤ _
  simp only [Function.comp_def] at hD
  rw [hD]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left
      (norm_fderiv_commonSupport_matrixMultiplier_zero_le hcalc a ha K hK hz p q hq hJets)
      (norm_nonneg _)).trans_eq (by unfold strongC1OperatorBudget;ring))

/-- The actual H2-to-L2 full divergence operator derivative has a local C1 bound,
    with no dependence on higher jets or on the exterior coefficient cutoff. -/
theorem norm_fderiv_commonSupport_fullOperator_zero_le
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → a (p,z) = 0)
    (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : (I dim),∀ k : Fin 2,∀ x ∈ ((fixedBallOpens dim):Set (X dim)),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖fderiv ℝ (fun t => fullBallDivergenceL 0
      (commonSupportMatrixFamily 2 a ha K hK hz t)) p‖ ≤ 2*fullC1OperatorBudget (dim := dim)*q := by
  let M := fun t => coefficientMatrixMultiplierL (fixedSobolevCalculus (dim := dim)) 0
    (commonSupportMatrixFamily 2 a ha K hK hz t)
  have hm : ContDiff ℝ ∞ M := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier (fixedSobolevCalculus (dim := dim)) 1
      (fun v => a v i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
      (fun t z h => by rw [hz t z h];rfl)
  have hD := ((coefficientDivergenceL (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 0) (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 1)).hasFDerivAt.comp p
    (hm.differentiable (by simp) p).hasFDerivAt).fderiv
  change ‖fderiv ℝ (fun t => coefficientDivergenceL (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 0) (unitBallCoordinateDerivativeL (fixedSobolevCalculus (dim := dim)) 1) (M t)) p‖ ≤ _
  simp only [Function.comp_def] at hD
  rw [hD]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left
      (norm_fderiv_commonSupport_matrixMultiplier_zero_le (fixedSobolevCalculus (dim := dim)) a ha K hK hz p q hq hJets)
      (norm_nonneg _)).trans_eq (by unfold fullC1OperatorBudget;ring))

end CalderonN
