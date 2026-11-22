module

public import Proof.CalderonN.SmoothWeakFluxPairing
public import Proof.CalderonN.SmoothZeroTraceMembership
public import Proof.CalderonN.SmoothMultiplierForcing

public import Proof.CalderonN.FixedBallSmoothEnergy

import Proof.CalderonN.BallRotationFlux
import Mathlib.Tactic

/-! The strong inverse and weak energy method control a zero-trace
solution forced by a finite sum of smooth divergence terms. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {ι : Type*} [Fintype ι]

theorem coordinateFluxDivergence_finsetSum (s : Finset ι) (F : ι → X dim → X dim)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (z : X dim) :
    coordinateFluxDivergence (∑ i ∈ s,F i) z = ∑ i ∈ s,coordinateFluxDivergence (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [coordinateFluxDivergence,coordDeriv,fderiv_fun_const]
  | insert i s hi ih =>
    have hS : ContDiff ℝ ∞ (∑ j ∈ s,F j) := by
      rw [show (∑ j ∈ s,F j) = fun x => ∑ j ∈ s,F j x from funext (fun x => Finset.sum_apply x s F)]
      exact ContDiff.sum fun j _ => hF j
    rw [Finset.sum_insert hi,Finset.sum_insert hi,coordinateFluxDivergence_add
      ((hF i).differentiable (by simp)) (hS.differentiable (by simp)),ih]

theorem norm_smoothBallSobolev_two_le_of_divergence_sum
    (F : SmoothCoefficientMatrix dim 2) {lo hi : ℝ}
    (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F) lo hi)
    (Inv : ℝ) (hInv : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ Inv)
    (a : ι → X dim → Mat dim) (ha : ∀ i, ContDiff ℝ ∞ (a i)) (u : ι → SmoothData dim)
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hGa : ∀ i z, z ∈ ball (0 : X dim) 1 → ‖a i z‖ ≤ q i ∧ ‖fderiv ℝ (a i) z‖ ≤ q i)
    (v : SmoothData dim) (hv : EqOn v.1 0 (standardSphere dim))
    (hEq : EqOn (negativeBallDivergence (coefficientMatrixField 2 F) v.1)
      (fun z => -(∑ i,negativeBallDivergence (a i) (u i).1 z)) (ball (0 : X dim) 1)) :
    ‖smoothBallSobolev 2 v‖ ≤ (Inv*fullC1OperatorBudget (dim:=dim))*
      ∑ i,q i*‖smoothBallSobolev 2 (u i)‖ := by
  let w (i : ι) : smoothBallDataSubmodule dim :=
    ⟨(smoothDivergenceForcing (ha i) (u i)).1,(smoothDivergenceForcing (ha i) (u i)).2⟩
  let g : SmoothData dim := ⟨(-(∑ i,w i)).1,smoothBallData_contDiff (-(∑ i,w i))⟩
  let L := smoothBallSobolevLinear dim 0
  have hg : EqOn (negativeBallDivergence (coefficientMatrixField 2 F) v.1) g.1 (ball (0 : X dim) 1) := by
    intro z hz
    rw [hEq hz]
    change _ = (-(∑ i,w i)).1 z
    simp only [Submodule.coe_neg,Pi.neg_apply,Submodule.coe_sum,Finset.sum_apply,w,smoothDivergenceForcing]
  have hGN : ‖smoothBallSobolev 0 g‖ ≤
      fullC1OperatorBudget (dim:=dim)*∑ i,q i*‖smoothBallSobolev 2 (u i)‖ := by
    change ‖L (-(∑ i,w i))‖ ≤ _
    rw [map_neg,norm_neg,map_sum,Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_smoothBallSobolev_negativeDivergence_le (ha i) (u i) (q i) (hq i) (hGa i)).trans_eq
      (mul_assoc _ _ _)
  have hInv₀ := (norm_nonneg _).trans hInv
  exact ((norm_smooth_zeroDirichlet_le_of_forcing F hEll v g hv hg).trans
    (mul_le_mul hInv hGN (norm_nonneg _) hInv₀)).trans_eq (by ring)

theorem energyFormH1_finsetSum_smoothFluxes_weak
    (s : Finset ι) (a : ι → X dim → Mat dim) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (u : ι → SmoothData dim) (v : FixedBallH1 dim) :
    (∑ i ∈ s, energyFormH1 (a i) 0 0 (smoothSobolev (u i)) v) =
      ∫ x in fixedBallOpens dim, ∑ j, W1p.gradient v x j * (∑ i ∈ s,smoothBallFlux (a i) (u i).1) x j := by
  simp_rw [energyFormH1_smooth_left]
  rw [← integral_finsetSum s (fun i _ =>
    integrable_smoothFlux_weak_pair _ (contDiff_smoothBallFlux (ha i) (u i)) v)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Finset.sum_apply]
  have hProj (j : Fin dim) : (∑ i ∈ s,smoothBallFlux (a i) (u i).1 x) j =
      ∑ i ∈ s,smoothBallFlux (a i) (u i).1 x j := by
    change (EuclideanSpace.proj (𝕜:=ℝ) j) (∑ i ∈ s,smoothBallFlux (a i) (u i).1 x) =
      ∑ i ∈ s,(EuclideanSpace.proj (𝕜:=ℝ) j) (smoothBallFlux (a i) (u i).1 x)
    rw [map_sum]
  simp only [hProj,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem norm_smoothSobolev_le_of_divergence_sum
    (F : SmoothCoefficientMatrix dim 2) {lo hi : ℝ}
    (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F) lo hi)
    (c : ℝ) (hc : 0 < c)
    (hCoer : ∀ u : FixedBallH1Zero dim,
      c*‖u‖^2 ≤ fixedBallSmoothEnergyL (contDiff_coefficientMatrixField 2 F).continuous
        (u : FixedBallH1 dim) (u : FixedBallH1 dim))
    (a : ι → X dim → Mat dim) (ha : ∀ i, ContDiff ℝ ∞ (a i)) (u : ι → SmoothData dim)
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hGa : ∀ i z, z ∈ ball (0 : X dim) 1 → ‖a i z‖ ≤ q i)
    (v : SmoothData dim) (hv : EqOn v.1 0 (standardSphere dim))
    (hEq : EqOn (negativeBallDivergence (coefficientMatrixField 2 F) v.1)
      (fun z => -(∑ i,negativeBallDivergence (a i) (u i).1 z)) (ball (0 : X dim) 1)) :
    ‖smoothSobolev v‖ ≤ ((dim:ℝ)^2/c)*∑ i,q i*‖smoothSobolev (u i)‖ := by
  let A := coefficientMatrixField 2 F
  let hA := contDiff_coefficientMatrixField 2 F
  let v₀ : FixedBallH1Zero dim := ⟨smoothSobolev v,smoothSobolev_mem_zero_of_eqOn_sphere F hEll v hv⟩
  let G (i : ι) := smoothBallFlux (a i) (u i).1
  let H := smoothBallFlux A v.1
  have hG (i : ι) : ContDiff ℝ ∞ (G i) := contDiff_smoothBallFlux (ha i) (u i)
  have hH : ContDiff ℝ ∞ H := contDiff_smoothBallFlux hA v
  have hF : ContDiff ℝ ∞ (∑ i,G i) := by
    rw [show (∑ i,G i) = fun x => ∑ i,G i x from funext (fun x => Finset.sum_apply x Finset.univ G)]
    exact ContDiff.sum fun i _ => hG i
  have hFlux : EqOn (coordinateFluxDivergence (H+∑ i,G i)) 0 (ball (0 : X dim) 1) := by
    intro z hz
    change coordinateFluxDivergence (H+∑ i,G i) z = 0
    rw [coordinateFluxDivergence_add (hH.differentiable (by simp)) (hF.differentiable (by simp)),
      coordinateFluxDivergence_finsetSum Finset.univ G hG]
    change coordinateFluxDivergence (smoothBallFlux A v.1) z+
      ∑ i,coordinateFluxDivergence (smoothBallFlux (a i) (u i).1) z = _
    simp_rw [coordinateFluxDivergence_smoothBallFlux]
    rw [show negativeBallDivergence A v.1 z = -(∑ i,negativeBallDivergence (a i) (u i).1 z) from hEq hz,
      neg_neg,Finset.sum_neg_distrib,add_neg_cancel]
  have hWeak := integral_smoothFlux_weak_zeroDirichlet _ (hH.add hF) hFlux v₀
  have hEnergy :
      fixedBallSmoothEnergyL hA.continuous (smoothSobolev v) (smoothSobolev v)+
        ∑ i,fixedBallSmoothEnergyL (ha i).continuous (smoothSobolev (u i)) (smoothSobolev v) = 0 := by
    simp only [fixedBallSmoothEnergyL_apply]
    rw [energyFormH1_smooth_left,energyFormH1_finsetSum_smoothFluxes_weak Finset.univ a ha u (smoothSobolev v)]
    rw [← integral_add (integrable_smoothFlux_weak_pair _ hH _) (integrable_smoothFlux_weak_pair _ hF _)]
    convert hWeak using 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [show (v₀ : FixedBallH1 dim) = smoothSobolev v from rfl,H,Pi.add_apply,PiLp.add_apply,mul_add,Finset.sum_add_distrib]
  have hForm (i : ι) :
      ‖fixedBallSmoothEnergyL (ha i).continuous‖ ≤ (dim:ℝ)^2*q i := by
    apply norm_fixedBallSmoothEnergyL_le (ha i).continuous (q i) (hq i)
    intro z hz k l
    rw [← Real.norm_eq_abs]
    exact (Matrix.norm_entry_le_entrywise_sup_norm (a i z)).trans (hGa i z hz)
  let N := ‖smoothSobolev v‖
  by_cases hN : N = 0
  · change N ≤ _
    rw [hN]
    exact mul_nonneg (div_nonneg (sq_nonneg _) hc.le) (Finset.sum_nonneg fun i _ => mul_nonneg (hq i) (norm_nonneg _))
  have hNpos : 0 < N := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hN)
  have hC := hCoer v₀
  change c*N^2 ≤ fixedBallSmoothEnergyL hA.continuous (smoothSobolev v) (smoothSobolev v) at hC
  have hB (i : ι) :
      ‖fixedBallSmoothEnergyL (ha i).continuous (smoothSobolev (u i)) (smoothSobolev v)‖ ≤
        ((dim:ℝ)^2*q i)*‖smoothSobolev (u i)‖*N :=
    ((fixedBallSmoothEnergyL (ha i).continuous).le_opNorm₂ _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hForm i) (norm_nonneg _)) (norm_nonneg _))
  have hControl : c*N^2 ≤
      (dim:ℝ)^2*(∑ i,q i*‖smoothSobolev (u i)‖)*N := by
    calc
      _ ≤ -(∑ i,fixedBallSmoothEnergyL (ha i).continuous (smoothSobolev (u i)) (smoothSobolev v)) :=
        hC.trans_eq (by linarith only [hEnergy])
      _ ≤ ‖∑ i,fixedBallSmoothEnergyL (ha i).continuous (smoothSobolev (u i)) (smoothSobolev v)‖ :=
        by rw [Real.norm_eq_abs]; exact neg_le_abs _
      _ ≤ ∑ i,((dim:ℝ)^2*q i)*‖smoothSobolev (u i)‖*N :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hB i)
      _ = _ := by rw [Finset.mul_sum,Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  have hh := le_of_mul_le_mul_right (show (c*N)*N ≤
    ((dim:ℝ)^2*(∑ i,q i*‖smoothSobolev (u i)‖))*N by nlinarith only [hControl]) hNpos
  change N ≤ _
  rw [div_mul_eq_mul_div,le_div_iff₀ hc,mul_comm N c]
  exact hh

end CalderonN
