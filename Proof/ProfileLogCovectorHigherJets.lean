import Proof.ProfileLogThirdJet
import Proof.FiniteJetBudgetAlgebra
import Proof.ThirdDerivativeProductBounds
import Proof.MetricCoefficientSecondDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The derivative covector expands in the fixed coordinate projections. -/
lemma fderiv_eq_sum_coordinate_covectors (f : X → ℝ) :
    fderiv ℝ f = fun y => ∑ i : I,coordDeriv i f y • (EuclideanSpace.proj i : X →L[ℝ] ℝ) := by
  funext y
  ext v
  rw [linear_axis_expansion]
  simp only [_root_.sum_apply,_root_.smul_apply,PiLp.proj_apply,smul_eq_mul,coordDeriv]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma norm_iteratedFDeriv_fderiv_le_coordinate_jets (f : X → ℝ) (y : X)
    (hf : ContDiffAt ℝ ∞ f y) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hJets : ∀ i : I,‖iteratedFDeriv ℝ n (coordDeriv i f) y‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ f) y‖ ≤ 3*C := by
  have hCoord (i : I) : ContDiffAt ℝ ∞ (coordDeriv i f) y :=
    (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const
  rw [fderiv_eq_sum_coordinate_covectors]
  have hh := norm_iteratedFDeriv_finite_sum_le
    Finset.univ (fun i : I => fun x => coordDeriv i f x • (EuclideanSpace.proj i : X →L[ℝ] ℝ)) y n
    (fun i _ => (hCoord i).smul contDiffAt_const)
  apply hh.trans
  calc
    _ ≤ ∑ _i : I,C := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_iteratedFDeriv_smul_const_le (hCoord i) (EuclideanSpace.proj i) n).trans
        ((mul_le_mul (norm_euclidean_proj_le_one i) (hJets i) (norm_nonneg _) zero_le_one).trans_eq (one_mul C))
    _ = _ := by simp only [Fin.sum_univ_three];ring

def profileLogCovectorJetBudget (K G DG C2 C3 : ℝ) : ℝ :=
  1+3*K+9*(9*K^2*|C2|+3*G*K)+27*profileLogThirdBudget K G DG C2 C3

/-- The first three frozen profile budgets give the covector's two jets
    without using ANY derivatives of the chosen orthonormal frame. -/
theorem Profile.log_covector_higher_jets {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    (G DG : ℝ) (hG : 0 ≤ G) (hDG : 0 ≤ DG) {y : X} (hy : y ∈ Y)
    (hΓ : ∀ a b c : I,|christoffel g y a b c| ≤ G)
    (hDΓ : ∀ a b c d : I,|coordDeriv a (fun x => christoffel g x b c d) y| ≤ DG) :
    ∀ n : ℕ,n ≤ 2 → ‖iteratedFDeriv ℝ n (fderiv ℝ (fun x => Real.log (r x))) y‖ ≤
      profileLogCovectorJetBudget K G DG (Cj 2) (Cj 3)*(beta g r y)^(n+1) := by
  let f := fun x => Real.log (r x)
  let β := beta g r y
  let L2 := 9*K^2*|Cj 2|+3*G*K
  let L3 := profileLogThirdBudget K G DG (Cj 2) (Cj 3)
  let C := profileLogCovectorJetBudget K G DG (Cj 2) (Cj 3)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hL2 : 0 ≤ L2 := by dsimp only [L2];positivity
  have hL3 : 0 ≤ L3 := profileLogThirdBudget_nonneg _ _ _ _ _ hK0 hG hDG
  have hC1 : 3*K ≤ C := by dsimp only [C,profileLogCovectorJetBudget];nlinarith only [hL2,hL3]
  have hC2 : 9*L2 ≤ C := by dsimp only [C,profileLogCovectorJetBudget,L2];nlinarith only [hK0,hL3]
  have hC3 : 27*L3 ≤ C := by dsimp only [C,profileLogCovectorJetBudget,L3];nlinarith only [hK0,hL2]
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hs : ContDiffOn ℝ ∞ f Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hsAt := hs.contDiffAt (hY.mem_nhds hy)
  have hSecond : ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ 9*L2*β^2 := by
    have hh := norm_bilinear_le_of_axis_bound (fderiv ℝ (fderiv ℝ f) y) (L2*β^2) (by positivity)
      (fun i j => by
        rw [← coordinate_second_derivative f y ((hsAt.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)) i j,Real.norm_eq_abs]
        exact hp.coordinate_log_second_bound h hK e hframe hf hG hy hΓ i j)
    exact hh.trans_eq (by ring)
  have hThird : ‖iteratedFDeriv ℝ 2 (fderiv ℝ f) y‖ ≤ 27*L3*β^3 := by
    have hh := norm_iteratedFDeriv_fderiv_le_coordinate_jets f y hsAt 2 (9*L3*β^3) (by positivity)
      (fun k => by
        rw [norm_iteratedFDeriv_two_eq_nested]
        have hsk := (contDiffOn_coordDeriv hY hs k).contDiffAt (hY.mem_nhds hy)
        exact (norm_bilinear_le_of_axis_bound (fderiv ℝ (fderiv ℝ (coordDeriv k f)) y) (L3*β^3) (by positivity)
          (fun i j => by
            rw [← coordinate_second_derivative (coordDeriv k f) y
              ((hsk.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)) i j,Real.norm_eq_abs]
            exact hp.coordinate_log_third_bound hY h hK e hframe hf G DG hG hDG hy hΓ hDΓ i j k)).trans_eq (by ring))
    exact hh.trans_eq (by ring)
  intro n hn
  interval_cases n
  · rw [norm_iteratedFDeriv_zero,pow_one]
    have hh := norm_linear_le_of_axis_bound (fderiv ℝ f y) (K*β) (by positivity)
      (fun i => by simpa only [Real.norm_eq_abs,coordDeriv] using h.coord_logRadius_bound hK e r hy (hframe y hy) i)
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hC1 hβ0])
  · rw [norm_iteratedFDeriv_one]
    exact hSecond.trans (mul_le_mul_of_nonneg_right hC2 (sq_nonneg β))
  · exact hThird.trans (mul_le_mul_of_nonneg_right hC3 (by positivity))

end ShrinkingSpheres
