import Proof.EndpointBoundaryCalculus
import Proof.ConnectionOperatorBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

def LocalC1Bound (f : X → ℝ) (A : ℝ) : Prop :=
  ∀ x ∈ (ballOpens : Set X),|f x| ≤ A ∧ ‖fderiv ℝ f x‖ ≤ A

lemma localC1Bound_mul {f g : X → ℝ} {A B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : LocalC1Bound f A) (hG : LocalC1Bound g B) :
    LocalC1Bound (fun x => f x*g x) (2*A*B) := by
  intro x hx
  obtain ⟨hFV,hFD⟩ := hF x hx
  obtain ⟨hGV,hGD⟩ := hG x hx
  constructor
  · rw [abs_mul]
    exact (mul_le_mul hFV hGV (abs_nonneg _) hA).trans (by nlinarith only [mul_nonneg hA hB])
  · rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact (add_le_add (mul_le_mul hFV hGD (norm_nonneg _) hA)
      (mul_le_mul hGV hFD (norm_nonneg _) hB)).trans_eq (by ring)

lemma localC1Bound_sum {ι : Type*} [Fintype ι] (F : ι → X → ℝ) (A : ι → ℝ)
    (hSmooth : ∀ i,ContDiff ℝ ∞ (F i)) (hBound : ∀ i,LocalC1Bound (F i) (A i)) :
    LocalC1Bound (fun x => ∑ i,F i x) (∑ i,A i) := by
  intro x hx
  constructor
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => (hBound i x hx).1)
  · rw [fderiv_fun_sum (u:=Finset.univ) (A:=F) (fun i hi => (hSmooth i).differentiable (by simp) x)]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => (hBound i x hx).2)

lemma localC1Bound_sub {f g : X → ℝ} {A B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hF : LocalC1Bound f A) (hG : LocalC1Bound g B) :
    LocalC1Bound (fun x => f x-g x) (A+B) := by
  intro x hx
  constructor
  · exact (abs_sub _ _).trans (add_le_add (hF x hx).1 (hG x hx).1)
  · rw [fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
    exact (norm_sub_le _ _).trans (add_le_add (hF x hx).2 (hG x hx).2)

lemma localC1Bound_coordinate (i : I) : LocalC1Bound (fun x : X => x i) 1 := by
  intro x hx
  constructor
  · exact (PiLp.norm_apply_le x i).trans (le_of_lt (by simpa [OAI.AnisotropicCalderon.B,Metric.mem_ball,dist_zero_right] using hx))
  · change ‖fderiv ℝ (EuclideanSpace.proj i : X →L[ℝ] ℝ) x‖ ≤ 1
    rw [(EuclideanSpace.proj i : X →L[ℝ] ℝ).hasFDerivAt.fderiv]
    exact norm_euclidean_proj_le_one i

/-- The boundary normal coefficient has local C1 control from the bulk matrix.
    These bounds are applied to the small perturbation matrix, not to exterior jets. -/
theorem boundaryNormalCoefficient_local_C1 (F : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 (F i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) :
    LocalC1Bound (boundaryNormalCoefficientData F).1 (36*q) := by
  let P (i : I) : X → ℝ := fun x => x i
  have hPS (i : I) : ContDiff ℝ ∞ (P i) := (EuclideanSpace.proj i : X →L[ℝ] ℝ).contDiff
  have hTerm (i j : I) : LocalC1Bound (fun x : X => x i*coefficientValue 2 (F i j) x*x j) (4*q) := by
    have hF : LocalC1Bound (coefficientValue 2 (F i j)) q := fun x hx => ⟨hValue i j x hx,hDerivative i j x hx⟩
    have h1 := localC1Bound_mul (hPS i) (contDiff_coefficientValue 2 (F i j)) zero_le_one hq
      (localC1Bound_coordinate i) hF
    have h2 := localC1Bound_mul ((hPS i).mul (contDiff_coefficientValue 2 (F i j))) (hPS j)
      (show 0 ≤ 2*1*q by positivity) zero_le_one h1 (localC1Bound_coordinate j)
    convert h2 using 1 <;> ring
  have hS := localC1Bound_sum
    (fun i : I => fun x : X => ∑ j : I,x i*coefficientValue 2 (F i j) x*x j) (fun _ : I => ∑ _ : I,4*q)
    (fun i => ContDiff.sum fun j hj => ((hPS i).mul (contDiff_coefficientValue 2 (F i j))).mul (hPS j))
    (fun i => localC1Bound_sum (fun j : I => fun x : X => x i*coefficientValue 2 (F i j) x*x j)
      (fun _ : I => 4*q)
      (fun j => ((hPS i).mul (contDiff_coefficientValue 2 (F i j))).mul (hPS j)) (hTerm i))
  convert hS using 1 <;> norm_num [boundaryNormalCoefficientData,coefficientSmoothData,Fin.sum_univ_three] <;> ring

/-- The same local C1 estimate controls the tangential coefficient after its
    exact normal component is removed. -/
theorem boundaryTangentCoefficient_local_C1 (F : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 (F i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q)
    (j : I) : LocalC1Bound (boundaryTangentCoefficientData F j).1 (78*q) := by
  let P (i : I) : X → ℝ := fun x => x i
  have hPS (i : I) : ContDiff ℝ ∞ (P i) := (EuclideanSpace.proj i : X →L[ℝ] ℝ).contDiff
  have hCol : LocalC1Bound (fun x : X => ∑ i : I,x i*coefficientValue 2 (F i j) x) (6*q) := by
    have hh := localC1Bound_sum (fun i : I => fun x : X => x i*coefficientValue 2 (F i j) x)
      (fun _ : I => 2*1*q) (fun i => (hPS i).mul (contDiff_coefficientValue 2 (F i j)))
      (fun i => localC1Bound_mul (hPS i) (contDiff_coefficientValue 2 (F i j)) zero_le_one hq
        (localC1Bound_coordinate i) (fun x hx => ⟨hValue i j x hx,hDerivative i j x hx⟩))
    convert hh using 1 <;> norm_num [Fin.sum_univ_three] <;> ring
  have hAnn := boundaryNormalCoefficient_local_C1 F q hq hValue hDerivative
  have hProd : LocalC1Bound (fun x : X => (boundaryNormalCoefficientData F).1 x*x j) (72*q) := by
    have hh := localC1Bound_mul (boundaryNormalCoefficientData F).2 (hPS j)
      (show 0 ≤ 36*q by positivity) zero_le_one hAnn (localC1Bound_coordinate j)
    convert hh using 1 <;> ring
  have hSub := localC1Bound_sub (ContDiff.sum fun i hi => (hPS i).mul (contDiff_coefficientValue 2 (F i j)))
    ((boundaryNormalCoefficientData F).2.mul (hPS j)) hCol hProd
  convert hSub using 1 <;> norm_num [boundaryTangentCoefficientData,coefficientSmoothData] <;> ring

end ShrinkingSpheres
