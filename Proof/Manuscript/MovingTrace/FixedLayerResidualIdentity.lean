module

public import Proof.CalderonPatch.NativeBoundaryLayerResidual
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

open Set Finset
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I)

variable {n : ℕ}
local notation "Y" => X n

private theorem fderiv_layer_sum {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset β) (a : β → ℂ) (f : β → E → ℂ)
    (hf : ∀ j ∈ S, ContDiff ℝ ∞ (f j)) (x v : E) :
    fderiv ℝ (fun y => ∑ j ∈ S, a j * f j y) x v =
      ∑ j ∈ S, a j * fderiv ℝ (f j) x v := by
  rw [fderiv_fun_sum (fun j hj => (contDiff_const.mul (hf j hj)).differentiable (by simp) x),
    _root_.sum_apply]
  apply sum_congr rfl
  intro j hj
  rw [fderiv_const_mul (((hf j hj).differentiable (by simp)) x)]
  rfl

private theorem deriv_layer_sum {β : Type*} (S : Finset β) (a : β → ℂ) (f : β → ℝ → ℂ)
    (hf : ∀ j ∈ S, ContDiff ℝ ∞ (f j)) (x : ℝ) :
    deriv (fun y => ∑ j ∈ S, a j * f j y) x = ∑ j ∈ S, a j * deriv (f j) x :=
  fderiv_layer_sum S a f hf x 1

theorem complexSplitOperator_layer_sum {β : Type*}
    (A : Matrix (I n) (I n) ℂ) (τ : ℂ) (c : I n → ℂ)
    (S : Finset β) (a : β → ℂ) (V : β → Y × ℝ → ℂ)
    (hV : ∀ j ∈ S, ContDiff ℝ ∞ (V j)) (y : Y) (t : ℝ) :
    complexSplitOperator A τ c (fun z => ∑ j ∈ S, a j * V j z) y t =
      ∑ j ∈ S, a j * complexSplitOperator A τ c (V j) y t := by
  let W (z : Y × ℝ) := ∑ j ∈ S, a j * V j z
  have hT (j) (hj : j ∈ S) : ContDiff ℝ ∞ (fun u : Y => V j (u,t)) :=
    (hV j hj).comp (contDiff_id.prodMk contDiff_const)
  have hN (j) (hj : j ∈ S) : ContDiff ℝ ∞ (fun r : ℝ => V j (y,r)) :=
    (hV j hj).comp (contDiff_const.prodMk contDiff_id)
  have hfirst (i : I n) (u : Y) : splitFirst W u t i =
      ∑ j ∈ S, a j * splitFirst (V j) u t i :=
    fderiv_layer_sum S a (fun j w => V j (w,t)) hT u _
  have hsecond (i l : I n) : splitSecond W y t i l =
      ∑ j ∈ S, a j * splitSecond (V j) y t i l := by
    change fderiv ℝ (fun u => splitFirst W u t l) y _ = _
    simp_rw [hfirst]
    apply fderiv_layer_sum
    intro j hj
    exact ((hT j hj).fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiff_const
  have hnormal (s : ℝ) : splitNormal W y s = ∑ j ∈ S, a j * splitNormal (V j) y s :=
    deriv_layer_sum S a (fun j r => V j (y,r)) hN s
  have hnormalSecond : splitNormalSecond W y t = ∑ j ∈ S, a j * splitNormalSecond (V j) y t := by
    change deriv (fun s => splitNormal W y s) t = _
    simp_rw [hnormal]
    apply deriv_layer_sum
    intro j hj
    exact ((hN j hj).of_le (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).deriv'
  change complexSplitOperator A τ c W y t = _
  unfold complexSplitOperator
  simp only [hfirst,hsecond,hnormal,hnormalSecond,mul_sub,mul_add,mul_neg,mul_sum,sum_neg_distrib,
    sum_sub_distrib,sum_add_distrib]
  have hA :
      (∑ i : I n, ∑ l : I n, ∑ j ∈ S, A i l * (a j * splitSecond (V j) y t i l)) =
        ∑ j ∈ S, ∑ i : I n, ∑ l : I n, a j * (A i l * splitSecond (V j) y t i l) := by
    calc
      _ = ∑ i : I n, ∑ j ∈ S, ∑ l : I n, A i l * (a j * splitSecond (V j) y t i l) :=
        sum_congr rfl (fun _ _ => sum_comm)
      _ = ∑ j ∈ S, ∑ i : I n, ∑ l : I n, A i l * (a j * splitSecond (V j) y t i l) :=
        sum_comm
      _ = _ := by simp only [mul_left_comm]
  rw [hA]
  have hc :
      (∑ i : I n, ∑ j ∈ S, c i * (a j * splitFirst (V j) y t i)) =
        ∑ j ∈ S, ∑ i : I n, a j * (c i * splitFirst (V j) y t i) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _
    ring
  rw [hc]
  congr 1
  congr 1
  apply sum_congr rfl
  intro j _
  ring

/-- Exact rescaled residual of a finite cutoff wave on one parameter
slice. The Taylor part cancels to the finite residual polynomial, leaving
the coefficient differences and the normal cutoff commutator. -/
theorem BoundaryLayerCoefficients.finiteWave_residual_identity
    {ξ : I n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (hKU : K ⊆ U)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (M : ℕ)
    (A : Matrix (I n) (I n) ℂ) (hA : ∀ i j, A i j = A j i)
    (τ : ℂ) (c : I n → ℂ) {h : ℝ} (hh : h ≠ 0) {y : Y} (hy : y ∈ U) (t : ℝ) :
    let s := t/h
    (h : ℂ) ^ 2 * complexSplitOperator A τ c (B.finiteWave a η M h) y t =
      tangentialWave ξ h y * (
        (η t : ℂ) * (B.finiteResidualProfile a M h (y,s) +
          ∑ j ∈ range (M+1), (h ^ j : ℂ) *
            scalarCoefficientDifference (A - B.matrixTaylor M y t) (τ - B.normalTaylor M y t)
              (c - B.tangentTaylor M y t) ξ h (B.profile a j) y s) +
        ∑ j ∈ range (M+1), (h ^ j : ℂ) * scaledCutoffDefect τ η h (B.profile a j) y t) := by
  dsimp only
  let V (j : ℕ) := normalCutoffWave η (scaledPlaneWave ξ h (B.profile a j))
  have hW (j : ℕ) (_ : j ∈ range (M+1)) : ContDiff ℝ ∞ (V j) :=
    contDiff_normalCutoffWave hη
      (contDiff_scaledPlaneWave ξ h (B.profile_contDiff hU hK hKU a ha ha0 j))
  let raw (j : ℕ) := conjugatedSplitOperator A τ c ξ h (B.profile a j) y (t/h)
  let taylor (j : ℕ) := conjugatedSplitOperator (B.matrixTaylor M y t) (B.normalTaylor M y t)
    (B.tangentTaylor M y t) ξ h (B.profile a j) y (t/h)
  let diff (j : ℕ) := scalarCoefficientDifference (A - B.matrixTaylor M y t)
    (τ - B.normalTaylor M y t) (c - B.tangentTaylor M y t) ξ h (B.profile a j) y (t/h)
  have hd (j : ℕ) : raw j = taylor j + diff j := by
    dsimp only [raw,taylor,diff]
    rw [← conjugatedSplitOperator_sub]
    exact (add_sub_cancel _ _).symm
  have ht : h * (t/h) = t := mul_div_cancel₀ t hh
  have hT :
      B.finiteResidualProfile a M h (y,t/h) =
        ∑ j ∈ range (M+1), (h ^ j : ℂ) * taylor j := by
    rw [B.finiteResidualProfile_eq_TaylorOperator_sum hU hK a ha ha0 M hy h (t/h), ht]
  have hΦ (j : ℕ) :
      (h : ℂ)^2 * complexSplitOperator A τ c (V j) y t =
        tangentialWave ξ h y * ((η t : ℂ) * raw j + scaledCutoffDefect τ η h (B.profile a j) y t) :=
    complexSplitOperator_scaledCutoff A hA τ c ξ hη hh
      (B.profile_contDiff hU hK hKU a ha ha0 j) y t
  rw [B.finiteWave_eq_layer_sum a η M h,
    complexSplitOperator_layer_sum A τ c _ (fun j => (h ^ j : ℂ)) V hW y t, mul_sum, hT]
  have hTerm (j : ℕ) : (h : ℂ)^2 * ((h ^ j : ℂ) * complexSplitOperator A τ c (V j) y t) =
      tangentialWave ξ h y * ((η t : ℂ) * ((h ^ j : ℂ) * taylor j) +
        (η t : ℂ) * ((h ^ j : ℂ) * diff j) +
        ((h ^ j : ℂ) * scaledCutoffDefect τ η h (B.profile a j) y t)) := by
    rw [mul_left_comm, hΦ, hd]
    ring
  simp only [hTerm, ← mul_sum, sum_add_distrib, ← mul_add]
  simp only [mul_add, sum_add_distrib, diff]

end CalderonPatch.BoundaryLayer
