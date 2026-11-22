module

public import Proof.CalderonN.SmoothZeroTraceMembership
public import Proof.CalderonN.SmoothWeakFluxPairing
public import Proof.CalderonN.SmoothConormalTaylorSolutions

import Proof.CalderonN.BallRotationFlux
import Mathlib.Tactic

/-! Weak bulk Taylor control of the same actual Dirichlet solution.
The residual equation is tested against its own zero-trace representative. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothPoisson_weakTaylor_bound {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (F : SmoothCoefficientMatrix dim 2) {lo hi : ℝ}
    (hFE : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F) lo hi)
    {ell : X dim →L[ℝ] ℝ} {f : SmoothData dim} (U : ConormalTaylorSolutions A ell f)
    (r c P D G : ℝ) (hr : 0 ≤ r) (hc : 0 < c) (hP : 0 ≤ P) (hD : 0 ≤ D) (hG : 0 ≤ G) :
    let E_A := fixedBallSmoothEnergyL hA.continuous
    let E₀ := fixedBallFlatEnergyL dim
    let E₁ := fixedBallSmoothEnergyL (ell.continuous.smul (show Continuous (fun _ : X dim => (1 : Mat dim)) from continuous_const))
    (∀ v : FixedBallH1Zero dim,
      c*‖v‖^2 ≤ E_A (v : FixedBallH1 dim) (v : FixedBallH1 dim)) →
    (∀ v : FixedBallH1Zero dim,
      c*‖v‖^2 ≤ E₀ (v : FixedBallH1 dim) (v : FixedBallH1 dim)) →
    ‖E_A-E₀‖ ≤ P*r → ‖E_A-E₀-r • E₁‖ ≤ D*r^2 → ‖E₁‖ ≤ G →
    ‖smoothSobolev U.first‖ ≤ (G/c)*‖smoothSobolev U.flat‖ ∧
    ‖smoothSobolev U.actual-smoothSobolev U.flat-r • smoothSobolev U.first‖ ≤
      ((D+P*(G/c))/c)*r^2*‖smoothSobolev U.flat‖ := by
  dsimp only
  intro hCoerA hCoer₀ hP₀ hD₀ hG₀
  let A₀ : X dim → Mat dim := fun _ => 1
  let A₁ : X dim → Mat dim := fun z => ell z • 1
  have hA₁ : ContDiff ℝ ∞ A₁ := ell.contDiff.smul contDiff_const
  let E_A := fixedBallSmoothEnergyL hA.continuous
  let E₀ := fixedBallFlatEnergyL dim
  let E₁ := fixedBallSmoothEnergyL hA₁.continuous
  let u := smoothSobolev U.flat
  let q := smoothSobolev U.first
  let b := smoothSobolev U.actual
  let d : SmoothData dim := ⟨fun z => U.actual.1 z-U.flat.1 z-r*U.first.1 z,
    (U.actual.2.sub U.flat.2).sub (contDiff_const.mul U.first.2)⟩
  have hdT : EqOn d.1 0 (standardSphere dim) := by
    intro z hz
    change U.actual.1 z-U.flat.1 z-r*U.first.1 z = 0
    rw [show U.actual.1 z = f.1 z from U.actualTrace hz,show U.flat.1 z = f.1 z from U.flatTrace hz,
      show U.first.1 z = 0 from U.firstTrace hz]
    ring
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hFlux : EqOn (coordinateFluxDivergence
      (smoothBallFlux A₀ U.first.1+smoothBallFlux A₁ U.flat.1)) 0 (ball (0 : X dim) 1) := by
    intro z hz
    change coordinateFluxDivergence (smoothBallFlux A₀ U.first.1+smoothBallFlux A₁ U.flat.1) z = 0
    rw [coordinateFluxDivergence_add ((contDiff_smoothBallFlux hA₀ U.first).differentiable (by simp))
      ((contDiff_smoothBallFlux hA₁ U.flat).differentiable (by simp)),
      coordinateFluxDivergence_smoothBallFlux,coordinateFluxDivergence_smoothBallFlux]
    have hFirst : negativeBallDivergence A₀ U.first.1 z =
      -negativeBallDivergence A₁ U.flat.1 z := U.firstEquation hz
    rw [hFirst,neg_neg,add_neg_cancel]
  have hEqA (v : FixedBallH1Zero dim) : E_A b (v : FixedBallH1 dim) = 0 := by
    rw [show E_A = fixedBallSmoothEnergyL hA.continuous from rfl,fixedBallSmoothEnergyL_apply]
    exact energyFormH1_smooth_zeroDirichlet hA U.actual U.actualEquation v
  have hEq₀ (v : FixedBallH1Zero dim) : E₀ u (v : FixedBallH1 dim) = 0 := by
    rw [show E₀ = fixedBallFlatEnergyL dim from rfl,fixedBallFlatEnergyL,fixedBallSmoothEnergyL_apply]
    exact energyFormH1_smooth_zeroDirichlet hA₀ U.flat U.flatEquation v
  have hEq₁ (v : FixedBallH1Zero dim) : E₀ q (v : FixedBallH1 dim)+E₁ u (v : FixedBallH1 dim) = 0 := by
    rw [show E₀ = fixedBallFlatEnergyL dim from rfl,fixedBallFlatEnergyL,fixedBallSmoothEnergyL_apply,
      show E₁ = fixedBallSmoothEnergyL hA₁.continuous from rfl,fixedBallSmoothEnergyL_apply]
    exact energyFormH1_two_smoothFluxes_zeroDirichlet hA₀ hA₁ U.flat U.first hFlux v
  have hMem (v : SmoothData dim) (hv : EqOn v.1 0 (standardSphere dim)) :
      smoothSobolev v ∈ w1p0Submodule volume (fixedBallOpens dim) 2 :=
    smoothSobolev_mem_zero_of_eqOn_sphere F hFE v hv
  let q₀ : FixedBallH1Zero dim := ⟨q,hMem U.first U.firstTrace⟩
  let d₀ : FixedBallH1Zero dim := ⟨smoothSobolev d,hMem d hdT⟩
  have hq₀ : ‖q₀‖ = ‖q‖ := rfl
  have hd₀ : ‖d₀‖ = ‖smoothSobolev d‖ := rfl
  have hqd : (q₀ : FixedBallH1 dim) = q := rfl
  have hd : smoothSobolev d = b-u-r • q := by
    let B : smoothBallDataSubmodule dim := ⟨U.actual.1,U.actual.2⟩
    let U₀ : smoothBallDataSubmodule dim := ⟨U.flat.1,U.flat.2⟩
    let Q : smoothBallDataSubmodule dim := ⟨U.first.1,U.first.2⟩
    let L := smoothBallSobolevLinear dim 1
    have h := L.map_sub (B-U₀) (r • Q)
    rw [L.map_sub B U₀,L.map_smul r Q] at h
    exact h
  have hQ : ‖q‖ ≤ (G/c)*‖u‖ := by
    by_cases hq : ‖q‖ = 0
    · rw [hq]; positivity
    have hqpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq)
    have h1 := hCoer₀ q₀
    rw [hq₀,hqd] at h1
    have h2 := hEq₁ q₀
    rw [hqd] at h2
    have h3 := (E₁.le_opNorm₂ u q).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG₀ (norm_nonneg u)) (norm_nonneg q))
    have hb : c*‖q‖*‖q‖ ≤ G*‖u‖*‖q‖ := by
      rw [Real.norm_eq_abs] at h3
      nlinarith only [h1,h2,(abs_le.mp h3).1]
    have hh := (mul_le_mul_iff_of_pos_right hqpos).mp hb
    calc
      _ = (c*‖q‖)/c := by rw [mul_comm,mul_div_cancel_right₀ _ hc.ne']
      _ ≤ (G*‖u‖)/c := div_le_div_of_nonneg_right hh hc.le
      _ = _ := by ring
  refine ⟨hQ,?_⟩
  rw [← hd]
  let e := smoothSobolev d
  have hResidual :
      E_A e e+(E_A-E₀-r • E₁) u e+r*(E_A-E₀) q e = 0 := by
    have he := congrArg (fun x => E_A x e) hd
    rw [map_sub,map_sub,map_smul,sub_apply,sub_apply,smul_apply,smul_eq_mul] at he
    simp only [sub_apply,smul_apply,smul_eq_mul]
    have hA' := hEqA d₀
    have h₀' := hEq₀ d₀
    have h₁' := hEq₁ d₀
    change E_A b e = 0 at hA'
    change E₀ u e = 0 at h₀'
    change E₀ q e+E₁ u e = 0 at h₁'
    linear_combination he+hA'-h₀'-r*h₁'
  by_cases hZ : ‖e‖ = 0
  · change ‖e‖ ≤ _
    rw [hZ]
    positivity
  have hEpos : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hZ)
  have heco : c*‖e‖^2 ≤ E_A e e := hCoerA d₀
  have hdu := ((E_A-E₀-r • E₁).le_opNorm₂ u e).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD₀ (norm_nonneg u)) (norm_nonneg e))
  have hdq := ((E_A-E₀).le_opNorm₂ q e).trans
    (mul_le_mul (mul_le_mul hP₀ hQ (norm_nonneg _) (by positivity)) le_rfl (norm_nonneg _) (by positivity))
  rw [Real.norm_eq_abs] at hdu hdq
  have hh : c*‖e‖*‖e‖ ≤ (D+P*(G/c))*r^2*‖u‖*‖e‖ := by
    have hq' := mul_le_mul_of_nonneg_left (abs_le.mp hdq).1 hr
    nlinarith only [heco,hResidual,(abs_le.mp hdu).1,hq']
  have hLast := (mul_le_mul_iff_of_pos_right hEpos).mp hh
  change ‖e‖ ≤ _
  calc
    _ = (c*‖e‖)/c := by rw [mul_comm, mul_div_cancel_right₀ _ hc.ne']
    _ ≤ ((D+P*(G/c))*r^2*‖u‖)/c := div_le_div_of_nonneg_right hLast hc.le
    _ = _ := by ring

end CalderonN
