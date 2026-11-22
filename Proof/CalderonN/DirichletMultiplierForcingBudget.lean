module

public import Proof.CalderonN.NormalizedMultiplierCommutator
public import Proof.CalderonN.DoubleAngularBulkEstimates

import Proof.CalderonN.MatrixFieldJetNorms
import Mathlib.Tactic

/-! Strong Dirichlet bounds for sums of divergence sources and
multiplication defects. The two terms use the same order-zero source norm. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def DirichletMultiplierForcingBudget
    (A : X dim → Mat dim) (m : SmoothData dim) (J C : ℝ) : Prop :=
  ∀ {n l : ℕ} (a : Fin n → X dim → Mat dim) (b : Fin l → X dim → Mat dim),
    (∀ i,ContDiff ℝ ∞ (a i)) → (∀ i,ContDiff ℝ ∞ (b i)) →
    ∀ (u : Fin n → SmoothData dim) (w : Fin l → SmoothData dim)
      (s q : Fin n → ℝ) (t p : Fin l → ℝ),
      (∀ i,0 ≤ s i) → (∀ i,0 ≤ q i) → (∀ i,0 ≤ t i) → (∀ i,0 ≤ p i) →
      (∀ i,SmoothCoefficientC1Bound (a i) (q i)) →
      (∀ i,SmoothCoefficientC1Bound (b i) (p i)) →
      ∀ v : SmoothData dim, EqOn v.1 0 (standardSphere dim) →
      EqOn (negativeBallDivergence A v.1)
        (fun z => -(∑ i,s i*negativeBallDivergence (a i) (u i).1 z)
          -(∑ i,t i*greenSourceCutoffError (b i) m.1 (w i).1 z)) (ball (0 : X dim) 1) →
      ‖smoothBallSobolev 2 v‖ ≤
        C*((∑ i,s i*q i*‖smoothBallSobolev 2 (u i)‖)+(∑ i,t i*p i*J*‖smoothSobolev (w i)‖))

theorem norm_smoothMultiplierForcing_le_of_C1Bound
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (m u : SmoothData dim)
    (G J : ℝ) (hG : 0 ≤ G) (hJ : 0 ≤ J)
    (hB : SmoothCoefficientC1Bound A G) (hm : SmoothMultiplierJetBound m J) :
    ‖smoothBallSobolev 0 (smoothMultiplierForcing hA m u)‖ ≤
      (4*(dim:ℝ)^2*G*J)*‖smoothSobolev u‖ := by
  exact norm_smoothMultiplierForcing_le hA m u G J hG hJ
    (fun z hz i j => by
      have h := hB z hz
      refine ⟨?_,?_⟩
      · rw [← Real.norm_eq_abs]
        exact (Matrix.norm_entry_le_entrywise_sup_norm _).trans h.1
      · rw [fderiv_matrix_entry A z (hA.differentiable (by simp) z) i j]
        apply ContinuousLinearMap.opNorm_le_bound _ hG
        intro v
        change |(fderiv ℝ A z v) i j| ≤ _
        rw [← Real.norm_eq_abs]
        refine (Matrix.norm_entry_le_entrywise_sup_norm (fderiv ℝ A z v)).trans ?_
        exact ((fderiv ℝ A z).le_opNorm v).trans (mul_le_mul_of_nonneg_right h.2 (norm_nonneg _)))
    (fun z hz => (hm z hz).1)

theorem dirichletMultiplierForcingBudget_of_inverse
    {A : X dim → Mat dim} (m : SmoothData dim) (J Inv : ℝ) (hJ : 0 ≤ J) (hInv : 0 ≤ Inv)
    (hm : SmoothMultiplierJetBound m J)
    (hI : ∀ v f : SmoothData dim, EqOn v.1 0 (standardSphere dim) →
      EqOn (negativeBallDivergence A v.1) f.1 (ball (0 : X dim) 1) →
      ‖smoothBallSobolev 2 v‖ ≤ Inv*‖smoothBallSobolev 0 f‖) :
    DirichletMultiplierForcingBudget A m J
      (Inv*max (fullC1OperatorBudget (dim:=dim)) (4*(dim:ℝ)^2)) := by
  intro n l a b ha hb u w s q t p hs hq ht hp hA hB v hv hV
  let K := max (fullC1OperatorBudget (dim:=dim)) (4*(dim:ℝ)^2)
  let L := smoothBallSobolevLinear dim 0
  let data (f : SmoothData dim) : smoothBallDataSubmodule dim := ⟨f.1,f.2⟩
  let d (i : Fin n) := data (smoothDivergenceForcing (ha i) (u i))
  let e (i : Fin l) := data (smoothMultiplierForcing (hb i) m (w i))
  let F := -(∑ i,s i • d i)-(∑ i,t i • e i)
  let f : SmoothData dim := ⟨F.1,smoothBallData_contDiff F⟩
  have hf : EqOn (negativeBallDivergence A v.1) f.1 (ball (0 : X dim) 1) := by
    intro z hz
    rw [hV hz]
    simp only [f,F,Submodule.coe_sub,Pi.sub_apply,Submodule.coe_neg,Pi.neg_apply,
      Submodule.coe_sum,Finset.sum_apply,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,
      data,d,e,smoothDivergenceForcing,smoothMultiplierForcing]
  refine (hI v f hv hf).trans ?_
  change Inv*‖L F‖ ≤ _
  change _ ≤ (Inv*K)*_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hInv
  simp only [F,map_sub,map_neg,map_sum,map_smul]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg,mul_add,Finset.mul_sum,Finset.mul_sum]
  refine add_le_add ((norm_sum_le _ _).trans ?_) ((norm_sum_le _ _).trans ?_)
  · apply Finset.sum_le_sum
    intro i _
    rw [norm_smul_of_nonneg (hs i)]
    have h := norm_smoothBallSobolev_negativeDivergence_le (ha i) (u i) (q i) (hq i) (hA i)
    have hK : fullC1OperatorBudget (dim:=dim) ≤ K := le_max_left _ _
    exact (mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (hq i)) (norm_nonneg _))) (hs i)).trans_eq (by ring)
  · apply Finset.sum_le_sum
    intro i _
    rw [norm_smul_of_nonneg (ht i)]
    have h := norm_smoothMultiplierForcing_le_of_C1Bound (hb i) m (w i) (p i) J (hp i) hJ (hB i) hm
    have hK : 4*(dim:ℝ)^2 ≤ K := le_max_right _ _
    exact (mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (hp i)) hJ) (norm_nonneg _))) (ht i)).trans_eq (by ring)

end CalderonN
