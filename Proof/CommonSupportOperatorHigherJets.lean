import Proof.CommonSupportMultiplierHigherJets
import Proof.CommonSupportOperatorDerivative
import Proof.FiniteJetBoundCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Matrix.Norms.Elementwise Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem norm_iteratedFDeriv_commonSupport_matrixMultiplier_zero_le
    (hcalc : FixedSobolevCalculus) (a : P × X → Mat) (ha : ContDiff ℝ ∞ a)
    (K : Set X) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → a (p,z) = 0)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => coefficientMatrixMultiplierL hcalc 0
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
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (4*q)*∏ k,‖v k‖)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (4*q)*∏ k,‖v k‖)).mpr
  intro j
  let ev : (I → I → BallSobolev 1 →L[ℝ] BallSobolev 1) →L[ℝ]
      (BallSobolev 1 →L[ℝ] BallSobolev 1) :=
    (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : I => BallSobolev 1 →L[ℝ] BallSobolev 1) j).comp
      (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : I => I → BallSobolev 1 →L[ℝ] BallSobolev 1) i)
  have hComp := ev.iteratedFDeriv_comp_left (hm.contDiffAt (x:=p)) (i:=n) (by simp)
  have hEval := congrArg (fun A => A v) hComp
  have hAt : (iteratedFDeriv ℝ n M p v) i j =
      iteratedFDeriv ℝ n (fun t => M t i j) p v := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe,Function.comp_apply,ev] using hEval.symm
  rw [hAt]
  have hNorm := norm_iteratedFDeriv_commonSupport_coefficientMultiplier_one_le hcalc
    (fun v => a v i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
    (fun t z h => by rw [hz t z h];rfl) p n q hq (hJets i j)
  exact (ContinuousMultilinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right hNorm (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem norm_iteratedFDeriv_commonSupport_strongOperator_zero_le
    (hcalc : FixedSobolevCalculus) (a : P × X → Mat) (ha : ContDiff ℝ ∞ a)
    (K : Set X) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → a (p,z) = 0)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => strongDirichletOperator hcalc 0
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
  change ‖iteratedFDeriv ℝ n ((unitBallDivergenceL hcalc 0) ∘ M) p‖ ≤ _
  exact (norm_iteratedFDeriv_clm_comp_le _ M p hm.contDiffAt n).trans
    ((mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_commonSupport_matrixMultiplier_zero_le hcalc a ha K hK hz p n q hq hJets)
      (norm_nonneg _)).trans_eq (by unfold strongC1OperatorBudget;ring))

theorem norm_iteratedFDeriv_commonSupport_fullOperator_zero_le
    (hcalc : FixedSobolevCalculus) (a : P × X → Mat) (ha : ContDiff ℝ ∞ a)
    (K : Set X) (hK : IsCompact K) (hz : ∀ p z,z ∉ K → a (p,z) = 0)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => fullCoefficientOperatorL hcalc 0
      (commonSupportMatrixFamily 2 a ha K hK hz t)) p‖ ≤ 2*fullC1OperatorBudget hcalc*q := by
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
  change ‖iteratedFDeriv ℝ n ((coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1)) ∘ M) p‖ ≤ _
  exact (norm_iteratedFDeriv_clm_comp_le _ M p hm.contDiffAt n).trans
    ((mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_commonSupport_matrixMultiplier_zero_le hcalc a ha K hK hz p n q hq hJets)
      (norm_nonneg _)).trans_eq (by unfold fullC1OperatorBudget;ring))

end ShrinkingSpheres
