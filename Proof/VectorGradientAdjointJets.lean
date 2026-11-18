import Proof.RadialTaylorHigherJets
import Proof.OperatorFamilyJetCalculus
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff BigOperators
namespace ShrinkingSpheres
variable {ι : Type*} [Fintype ι]
variable {P Coeff E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Coeff] [NormedSpace ℝ Coeff]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def vectorNormalOperator (Multiplier : Coeff →L[ℝ] (E →L[ℝ] E))
    (Coord : ι → E →L[ℝ] E) (Q : ι → Coeff) : E →L[ℝ] E :=
  ∑ j : ι,(Coord j).comp (Multiplier (Q j))
def vectorTangentialOperator (Multiplier : Coeff →L[ℝ] (E →L[ℝ] E))
    (Coord : ι → E →L[ℝ] E) (Rot : ι → ι → E →L[ℝ] F) (Q : ι → Coeff) : E →L[ℝ] F :=
  ∑ j : ι,∑ i : ι,-(Rot i j).comp ((Coord i).comp (Multiplier (Q j)))
def vectorGradientAdjointOperator (Multiplier : Coeff →L[ℝ] (E →L[ℝ] E))
    (Coord : ι → E →L[ℝ] E) (Rot : ι → ι → E →L[ℝ] F)
    (Q : ι → Coeff) (Da : E →L[ℝ] F) : E →L[ℝ] F :=
  vectorTangentialOperator Multiplier Coord Rot Q+Da.comp (vectorNormalOperator Multiplier Coord Q)
def vectorNormalOperatorBudget (Coord : ι → E →L[ℝ] E) : ℝ := ∑ j : ι,‖Coord j‖
def vectorTangentialOperatorBudget (Coord : ι → E →L[ℝ] E) (Rot : ι → ι → E →L[ℝ] F) : ℝ :=
  ∑ j : ι,∑ i : ι,‖Rot i j‖*‖Coord i‖

lemma contDiffAt_vectorGradientAdjointOperator
    (Multiplier : Coeff →L[ℝ] (E →L[ℝ] E)) (Coord : ι → E →L[ℝ] E)
    (Rot : ι → ι → E →L[ℝ] F) (Q : ι → P → Coeff) (Da : P → E →L[ℝ] F)
    (p : P) (hQ : ∀ j,ContDiffAt ℝ ∞ (Q j) p) (hDa : ContDiffAt ℝ ∞ Da p) :
    ContDiffAt ℝ ∞ (fun t => vectorGradientAdjointOperator Multiplier Coord Rot (fun j => Q j t) (Da t)) p := by
  have hM (j : ι) := Multiplier.contDiff.contDiffAt.comp p (hQ j)
  have hN : ContDiffAt ℝ ∞ (fun t => vectorNormalOperator Multiplier Coord (fun j => Q j t)) p :=
    ContDiffAt.sum (fun j _ => contDiffAt_const.clm_comp (hM j))
  have hT : ContDiffAt ℝ ∞ (fun t => vectorTangentialOperator Multiplier Coord Rot (fun j => Q j t)) p :=
    ContDiffAt.sum (fun j _ => ContDiffAt.sum (fun i _ =>
      (contDiffAt_const.clm_comp (contDiffAt_const.clm_comp (hM j))).neg))
  exact hT.add (hDa.clm_comp hN)

theorem norm_iteratedFDeriv_vectorGradientAdjointOperator_le
    (Multiplier : Coeff →L[ℝ] (E →L[ℝ] E)) (Coord : ι → E →L[ℝ] E)
    (Rot : ι → ι → E →L[ℝ] F) (CM : ℝ) (hCM : 0 ≤ CM) (hMultiplier : ‖Multiplier‖ ≤ CM)
    (Q : ι → P → Coeff) (Da : P → E →L[ℝ] F)
    (p : P) (hQ : ∀ j,ContDiffAt ℝ ∞ (Q j) p) (hDa : ContDiffAt ℝ ∞ Da p)
    (N : ℕ) (BQ CD : ℝ) (hBQ : 0 ≤ BQ) (hCD : 0 ≤ CD)
    (hQJets : ∀ j : ι,∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (Q j) p‖ ≤ BQ)
    (hDaJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n Da p‖ ≤ CD)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun t => vectorGradientAdjointOperator Multiplier Coord Rot (fun j => Q j t) (Da t)) p‖ ≤
      (CM*vectorTangentialOperatorBudget Coord Rot+2^N*CD*(CM*vectorNormalOperatorBudget Coord))*BQ := by
  let M := fun j t => Multiplier (Q j t)
  let NM := fun t => vectorNormalOperator Multiplier Coord (fun j => Q j t)
  let TA := fun t => vectorTangentialOperator Multiplier Coord Rot (fun j => Q j t)
  have hM (j : ι) : ContDiffAt ℝ ∞ (M j) p := Multiplier.contDiff.contDiffAt.comp p (hQ j)
  have hMJ (j : ι) (k : ℕ) (hk : k ≤ N) : ‖iteratedFDeriv ℝ k (M j) p‖ ≤ CM*BQ :=
    (norm_iteratedFDeriv_clm_comp_le Multiplier (Q j) p (hQ j) k).trans
      (mul_le_mul hMultiplier (hQJets j k hk) (norm_nonneg _) hCM)
  have hNM : ContDiffAt ℝ ∞ NM p := ContDiffAt.sum (fun j _ => contDiffAt_const.clm_comp (hM j))
  have hTA : ContDiffAt ℝ ∞ TA p := ContDiffAt.sum (fun j _ => ContDiffAt.sum (fun i _ =>
    (contDiffAt_const.clm_comp (contDiffAt_const.clm_comp (hM j))).neg))
  have hNMJ (k : ℕ) (hk : k ≤ N) : ‖iteratedFDeriv ℝ k NM p‖ ≤ (CM*vectorNormalOperatorBudget Coord)*BQ := by
    have hh := norm_iteratedFDeriv_fintype_sum_at_le
      (fun j : ι => fun t => (Coord j).comp (M j t)) p
      (fun j => contDiffAt_const.clm_comp (hM j)) k
    exact hh.trans ((Finset.sum_le_sum (fun j _ =>
      (norm_iteratedFDeriv_operator_postcomp_fixed_le (Coord j) (M j) p (hM j) k).trans
        (mul_le_mul_of_nonneg_left (hMJ j k hk) (norm_nonneg _)))).trans_eq
      (by unfold vectorNormalOperatorBudget;simp_rw [← Finset.sum_mul];ring))
  have hTAJ : ‖iteratedFDeriv ℝ n TA p‖ ≤ (CM*vectorTangentialOperatorBudget Coord Rot)*BQ := by
    have hEach (j i : ι) : ‖iteratedFDeriv ℝ n (fun t => -(Rot i j).comp
        ((Coord i).comp (M j t))) p‖ ≤
        (‖Rot i j‖*‖Coord i‖)*(CM*BQ) := by
      rw [norm_iteratedFDeriv_neg_at _ p (contDiffAt_const.clm_comp (contDiffAt_const.clm_comp (hM j))) n]
      exact (norm_iteratedFDeriv_operator_postcomp_fixed_le (Rot i j)
        (fun t => (Coord i).comp (M j t)) p (contDiffAt_const.clm_comp (hM j)) n).trans
        ((mul_le_mul_of_nonneg_left ((norm_iteratedFDeriv_operator_postcomp_fixed_le (Coord i)
          (M j) p (hM j) n).trans (mul_le_mul_of_nonneg_left (hMJ j n hn) (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring))
    have hh := norm_iteratedFDeriv_fintype_sum_at_le (fun j : ι => fun t => ∑ i : ι,
      -(Rot i j).comp ((Coord i).comp (M j t))) p
      (fun j => ContDiffAt.sum (fun i _ => (contDiffAt_const.clm_comp (contDiffAt_const.clm_comp (hM j))).neg)) n
    exact hh.trans ((Finset.sum_le_sum (fun j _ =>
      (norm_iteratedFDeriv_fintype_sum_at_le (fun i : ι => fun t => -(Rot i j).comp
        ((Coord i).comp (M j t))) p
        (fun i => (contDiffAt_const.clm_comp (contDiffAt_const.clm_comp (hM j))).neg) n).trans
          (Finset.sum_le_sum (fun i _ => hEach j i)))).trans_eq
      (by unfold vectorTangentialOperatorBudget;simp_rw [← Finset.sum_mul];ring))
  have hBudget : 0 ≤ CM*vectorNormalOperatorBudget Coord := by unfold vectorNormalOperatorBudget;positivity
  have hh := norm_iteratedFDeriv_add_at_le TA (fun t => (Da t).comp (NM t)) p hTA (hDa.clm_comp hNM) n
  exact hh.trans ((add_le_add hTAJ
    (norm_iteratedFDeriv_operator_comp_common_bound Da NM p hDa hNM N CD
      ((CM*vectorNormalOperatorBudget Coord)*BQ) hCD (by positivity) hDaJets hNMJ n hn)).trans_eq (by ring))

end ShrinkingSpheres
