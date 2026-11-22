module

public import Proof.CalderonN.SharpConormalHalfBound

import Mathlib.Tactic

/-! The very same finite conormal flux sum has a strong half-order
bound and a weak Green pairing bound. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Gradient Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5300000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {ι : Type*} [Fintype ι]

@[expose] def smoothConormalSumData
    (a : ι → X dim → Mat dim) (ha : ∀ i, ContDiff ℝ ∞ (a i)) (u : ι → SmoothData dim) :
    SmoothData dim :=
  ⟨fun z => ∑ i,(smoothConormalData (ha i) (u i)).1 z,
    ContDiff.sum fun i _ => (smoothConormalData (ha i) (u i)).2⟩

theorem norm_smoothConormalSumData_half_le (hn : 3 ≤ dim) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ι → X dim → Mat dim) (ha : ∀ i, ContDiff ℝ ∞ (a i))
      (u : ι → SmoothData dim) (q : ι → ℝ), (∀ i, 0 ≤ q i) →
      (∀ i, SmoothCoefficientC1Bound (a i) (q i)) →
      ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (smoothConormalSumData a ha u)‖ ≤
        C*∑ i,q i*‖smoothBallSobolev 2 (u i)‖ := by
  obtain ⟨C,hC,hNorm⟩ := norm_smoothConormalData_half_le hn
  refine ⟨C,hC,?_⟩
  intro a ha u q hq hB
  let B := smoothBoundarySobolevLinear hn (1/2 : ℝ) (by norm_num)
  let V (i : ι) : smoothBallDataSubmodule dim :=
    ⟨(smoothConormalData (ha i) (u i)).1,(smoothConormalData (ha i) (u i)).2⟩
  let Z : SmoothData dim := ⟨(∑ i,V i).1,smoothBallData_contDiff (∑ i,V i)⟩
  have hEq : EqOn (smoothConormalSumData a ha u).1 Z.1 (standardSphere dim) := by
    intro z _
    change (∑ i,(smoothConormalData (ha i) (u i)).1 z) = (∑ i,V i).1 z
    simp only [Submodule.coe_sum,Finset.sum_apply,V]
  rw [smoothBoundarySobolev_eq_of_eqOn hn (1/2 : ℝ) (by norm_num) _ Z hEq]
  change ‖B (∑ i,V i)‖ ≤ _
  rw [map_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (hNorm (ha i) (q i) (hq i) (hB i) (u i)).trans_eq (mul_assoc _ _ _))

theorem energyFormH1_finsetSum_smoothFluxes_eq_boundary
    (a : ι → X dim → Mat dim) (ha : ∀ i, ContDiff ℝ ∞ (a i)) (u : ι → SmoothData dim)
    (v : SmoothData dim)
    (hFlux : EqOn (coordinateFluxDivergence (∑ i,smoothBallFlux (a i) (u i).1)) 0
      (ball (0 : X dim) 1)) :
    (∑ i, energyFormH1 (a i) 0 0 (smoothSobolev (u i)) (smoothSobolev v)) =
      unitSphereArea dim * ∫ z : ↥(standardSphere dim),
        v.1 z*(smoothConormalSumData a ha u).1 z ∂(sphereProbability dim) := by
  let G (i : ι) := smoothBallFlux (a i) (u i).1
  let F := ∑ i,G i
  have hG (i : ι) : ContDiff ℝ ∞ (G i) := contDiff_smoothBallFlux (ha i) (u i)
  have hF : ContDiff ℝ ∞ F := by
    rw [show F = fun z => ∑ i,G i z from funext (fun z => Finset.sum_apply z Finset.univ G)]
    exact ContDiff.sum fun i _ => hG i
  rw [energyFormH1_finsetSum_smoothFluxes_weak Finset.univ a ha u (smoothSobolev v)]
  change (∫ x in fixedBallOpens dim, ∑ j, W1p.gradient (smoothSobolev v) x j * F x j) = _
  have hBulk : (∫ x in fixedBallOpens dim, ∑ j, W1p.gradient (smoothSobolev v) x j * F x j) =
      ∫ x in fixedBallOpens dim, ∑ j, gradient v.1 x j * F x j := by
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae v] with x hx
    rw [hx]
  rw [hBulk,integral_smoothFlux_gradient_eq_boundary F hF v hFlux]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have hL : ⟪z.1,F z⟫_ℝ = (smoothConormalSumData a ha u).1 z := by
    simp only [F,Finset.sum_apply,inner_sum,G,smoothConormalSumData,smoothConormalData,smoothBallConormal]
  rw [hL]

theorem abs_conormal_sum_pair_le_weak_bulk
    (a : ι → X dim → Mat dim) (ha : ∀ i, ContDiff ℝ ∞ (a i)) (u : ι → SmoothData dim)
    (v : SmoothData dim)
    (hFlux : EqOn (coordinateFluxDivergence (∑ i,smoothBallFlux (a i) (u i).1)) 0
      (ball (0 : X dim) 1))
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hA : ∀ i z, z ∈ ball (0 : X dim) 1 → ‖a i z‖ ≤ q i) :
    |∫ z : ↥(standardSphere dim), v.1 z*(smoothConormalSumData a ha u).1 z ∂(sphereProbability dim)| ≤
      ((dim:ℝ)^2/unitSphereArea dim)*(∑ i,q i*‖smoothSobolev (u i)‖)*‖smoothSobolev v‖ := by
  have hArea : 0 < unitSphereArea dim := unitSphereArea_pos
  have hPair := energyFormH1_finsetSum_smoothFluxes_eq_boundary a ha u v hFlux
  apply le_of_mul_le_mul_left _ hArea
  rw [← abs_of_pos hArea,← abs_mul,← hPair,abs_of_pos hArea,← mul_assoc,← mul_assoc,mul_div_cancel₀ _ hArea.ne']
  have hNorm (i : ι) : ‖fixedBallSmoothEnergyL (ha i).continuous‖ ≤ (dim:ℝ)^2*q i :=
    norm_fixedBallSmoothEnergyL_le _ _ (hq i) (fun z hz k l => by
      rw [← Real.norm_eq_abs]
      exact (Matrix.norm_entry_le_entrywise_sup_norm (a i z)).trans (hA i z hz))
  rw [← Real.norm_eq_abs]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i,((dim:ℝ)^2*q i)*‖smoothSobolev (u i)‖*‖smoothSobolev v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← fixedBallSmoothEnergyL_apply (ha i).continuous]
      exact ((fixedBallSmoothEnergyL (ha i).continuous).le_opNorm₂ _ _).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hNorm i) (norm_nonneg _)) (norm_nonneg _))
    _ = _ := by rw [Finset.mul_sum,Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

end CalderonN
