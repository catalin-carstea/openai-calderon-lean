module

public import Proof.CalderonN.Chart

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic

public section

set_option maxHeartbeats 2000000

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {d : ℕ}

@[expose] def productDirection (F : (X d) × (X d) → ℝ) (v : (X d) × (X d)) (q : (X d) × (X d)) : ℝ :=
  fderiv ℝ F q v

theorem contDiff_productDirection {F : (X d) × (X d) → ℝ} (hF : ContDiff ℝ ∞ F) (v : (X d) × (X d)) :
    ContDiff ℝ ∞ (productDirection F v) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem productDirection_comm {F : (X d) × (X d) → ℝ} (hF : ContDiff ℝ ∞ F)
    (a b : (X d) × (X d)) :
    productDirection (productDirection F a) b = productDirection (productDirection F b) a := by
  funext q
  have hD := hF.fderiv_right (m := ∞) (by simp)
  have h₁ (a b : (X d) × (X d)) :
      productDirection (productDirection F a) b q = fderiv ℝ (fderiv ℝ F) q b a := by
    unfold productDirection
    rw [fderiv_clm_apply (hD.differentiable (by simp) q) (differentiableAt_const a)]
    simp
  rw [h₁,h₁]
  exact hF.contDiffAt.isSymmSndFDerivAt (by simp) _ _

theorem fderiv_productSlice_left_apply {F : (X d) × (X d) → ℝ} (hF : ContDiff ℝ ∞ F) (x y v : (X d)) :
    fderiv ℝ (fun t => F (t,y)) x v = productDirection F (v,0) (x,y) := by
  have h := (((hF.differentiable (by simp) (x,y)).hasFDerivAt).comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)).fderiv
  change (fderiv ℝ (F ∘ fun t => (t,y)) x) v = _
  rw [h]
  rfl

theorem fderiv_productSlice_right_apply {F : (X d) × (X d) → ℝ} (hF : ContDiff ℝ ∞ F) (x y v : (X d)) :
    fderiv ℝ (fun t => F (x,t)) y v = productDirection F (0,v) (x,y) := by
  have h := (((hF.differentiable (by simp) (x,y)).hasFDerivAt).comp y
    (hasFDerivAt_prodMk_right x y)).fderiv
  change (fderiv ℝ (F ∘ Prod.mk x) y) v = _
  rw [h]
  rfl

private theorem laplace_productSlice_left_eq {F : (X d) × (X d) → ℝ} (hF : ContDiff ℝ ∞ F)
    (g : (MetricField d)) (x y : (X d)) :
    laplace g (fun t => F (t,y)) x =
      ∑ i, ∑ j, (g x)⁻¹ i j *
        (productDirection (productDirection F (axis j,0)) (axis i,0) (x,y) -
          ∑ k, christoffel g x k i j * productDirection F (axis k,0) (x,y)) := by
  have h₁ (j : (I d)) : coordDeriv j (fun t => F (t,y)) =
      fun t => productDirection F (axis j,0) (t,y) :=
    funext fun t => fderiv_productSlice_left_apply hF t y (axis j)
  have h₂ (i j : (I d)) :
      coordDeriv i (coordDeriv j (fun t => F (t,y))) x =
        productDirection (productDirection F (axis j,0)) (axis i,0) (x,y) := by
    rw [h₁]
    exact fderiv_productSlice_left_apply (contDiff_productDirection hF _) x y (axis i)
  simp only [laplace,h₂]
  simp only [h₁]

private theorem fderiv_sum_const_mul_at {ι : Type*} [Fintype ι] (A : ι → ℝ)
    (F : ι → (X d) → ℝ) {x : (X d)} (hF : ∀ i, DifferentiableAt ℝ (F i) x) (a : (X d)) :
    fderiv ℝ (fun y => ∑ i, A i * F i y) x a = ∑ i, A i * fderiv ℝ (F i) x a := by
  rw [fderiv_fun_sum (fun i _ => (hF i).const_mul (A i))]
  simp only [sum_apply,fderiv_const_mul,hF,_root_.smul_apply,smul_eq_mul]

/-- Differentiating the right variable preserves the left harmonic
equation because the latter's coefficients only depend on the left variable. -/
theorem harmonic_left_productDirection_right
    {F : (X d) × (X d) → ℝ} (hF : ContDiff ℝ ∞ F) {g : (MetricField d)}
    {D V : Set (X d)} (hV : IsOpen V)
    (hLap : ∀ q ∈ D ×ˢ V, laplace g (fun x => F (x,q.2)) q.1 = 0)
    (v : (X d)) {y : (X d)} (hy : y ∈ V) :
    Harmonic D g (fun t => productDirection F (0,v) (t,y)) := by
  let R : (X d) × (X d) := (0,v)
  let L (i : (I d)) : (X d) × (X d) := (axis i,0)
  let B (j : (I d)) := productDirection F (L j)
  let C (i j : (I d)) := productDirection (B j) (L i)
  have hB (i : (I d)) := contDiff_productDirection hF (L i)
  have hC (i j : (I d)) := contDiff_productDirection (hB j) (L i)
  have hR := contDiff_productDirection hF R
  refine ⟨(hR.comp (contDiff_id.prodMk contDiff_const)).contDiffOn,?_⟩
  intro x hx
  let J (i j : (I d)) (t : (X d)) := C i j (x,t) - ∑ k, christoffel g x k i j * B k (x,t)
  let E (t : (X d)) := ∑ i, ∑ j, (g x)⁻¹ i j * J i j t
  have hC' (i j : (I d)) : ContDiff ℝ ∞ (fun t : (X d) => C i j (x,t)) :=
    (hC i j).comp (contDiff_const.prodMk contDiff_id)
  have hB' (k : (I d)) : ContDiff ℝ ∞ (fun t : (X d) => B k (x,t)) :=
    (hB k).comp (contDiff_const.prodMk contDiff_id)
  have hJ (i j : (I d)) : ContDiff ℝ ∞ (J i j) :=
    (hC' i j).sub (ContDiff.sum fun k _ => contDiff_const.mul (hB' k))
  have hE : E =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hV.mem_nhds hy] with t ht
    exact (laplace_productSlice_left_eq hF g x t).symm.trans (hLap (x,t) ⟨hx,ht⟩)
  have hZero : fderiv ℝ E y v = 0 := by rw [hE.fderiv_eq]; simp
  have hF' (i : (I d)) : DifferentiableAt ℝ (fun t => ∑ j, (g x)⁻¹ i j * J i j t) y :=
    (ContDiff.sum fun j _ => contDiff_const.mul (hJ i j)).differentiable (by simp) y
  unfold E at hZero
  rw [fderiv_fun_sum (fun i _ => hF' i),sum_apply] at hZero
  simp_rw [fderiv_sum_const_mul_at _ _ (fun j => (hJ _ j).differentiable (by simp) y)] at hZero
  have hJ' (i j : (I d)) : fderiv ℝ (J i j) y v =
      productDirection (C i j) R (x,y) -
        ∑ k, christoffel g x k i j * productDirection (B k) R (x,y) := by
    unfold J
    rw [fderiv_fun_sub ((hC' i j).differentiable (by simp) y)
      ((ContDiff.sum fun k _ => contDiff_const.mul (hB' k)).differentiable (by simp) y),
      sub_apply,
      fderiv_productSlice_right_apply (hC i j),fderiv_sum_const_mul_at _ _
        (fun k => (hB' k).differentiable (by simp) y)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [fderiv_productSlice_right_apply (hB k)]
  have hComm₁ (k : (I d)) : productDirection (B k) R = productDirection (productDirection F R) (L k) :=
    productDirection_comm hF (L k) R
  have hComm₂ (i j : (I d)) :
      productDirection (C i j) R =
        productDirection (productDirection (productDirection F R) (L j)) (L i) := by
    calc
      _ = productDirection (productDirection (B j) R) (L i) :=
        productDirection_comm (hB j) (L i) R
      _ = _ := by rw [hComm₁]
  simp_rw [hJ',hComm₁,hComm₂] at hZero
  rw [laplace_productSlice_left_eq hR]
  exact hZero

end CalderonN
