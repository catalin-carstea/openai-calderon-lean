module

public import Proof.CalderonN.LocalSmoothJetBudget
public import Proof.CalderonN.BanachInverseFamilyJetBounds
public import Proof.CalderonN.PoissonAffineRemainderHigherJets

import Mathlib.Tactic

/-! The released Poisson remainder estimate applied to an exact affine
factorization of the coefficient operators. Shared by the strong and
weak fixed-ball problems. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open ShrinkingSpheres

variable {P E F U H : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem exists_uniform_operator_inverse_near
    (A₀ : E →L[ℝ] F) (hA₀ : A₀.IsInvertible) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ‖A₀.inverse‖ ≤ C ∧
      ∀ A : E →L[ℝ] F, ‖A-A₀‖ < δ → A.IsInvertible ∧ ‖A.inverse‖ ≤ C := by
  let S : Set (E →L[ℝ] F) := {A | A.IsInvertible}
  have hS : S ∈ 𝓝 A₀ := ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hA₀
  have hC : ContinuousAt (fun A : E →L[ℝ] F => ‖A.inverse‖) A₀ :=
    (hA₀.contDiffAt_map_inverse (n:=0)).continuousAt.norm
  let C := ‖A₀.inverse‖+1
  have hC₀ : ‖A₀.inverse‖ ≤ C := le_add_of_nonneg_right zero_le_one
  have hI : {A : E →L[ℝ] F | ‖A.inverse‖ < C} ∈ 𝓝 A₀ :=
    hC (Iio_mem_nhds (lt_add_one _))
  obtain ⟨δ,hδ,hδS⟩ := Metric.mem_nhds_iff.mp (inter_mem hS hI)
  refine ⟨δ,C,hδ,(norm_nonneg _).trans hC₀,hC₀,fun A hA => ?_⟩
  obtain ⟨hInv,hCA⟩ := hδS (mem_ball.mpr (by rwa [dist_eq_norm]))
  exact ⟨hInv,le_of_lt hCA⟩

private theorem localSmoothJetBudget_affine_sub_flat
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A₁ A₂ : P → V} {x : P} {N : ℕ} {C : ℝ}
    (h₁ : LocalSmoothJetBudget A₁ x N C) (h₂ : LocalSmoothJetBudget A₂ x N C)
    (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    LocalSmoothJetBudget (fun p => r • A₁ p+r^2 • A₂ p) x N ((2*C)*r) := by
  refine ⟨(h₁.smooth.const_smul r).add (h₂.smooth.const_smul (r^2)),fun n hn => ?_⟩
  have h := norm_iteratedFDeriv_add_at_le (fun p => r • A₁ p) (fun p => r^2 • A₂ p)
    x (h₁.smooth.const_smul r) (h₂.smooth.const_smul (r^2)) n
  rw [norm_iteratedFDeriv_const_smul_at _ x h₁.smooth,norm_iteratedFDeriv_const_smul_at _ x h₂.smooth,
    abs_of_nonneg hr,abs_of_nonneg (sq_nonneg r)] at h
  have hC := h₁.nonneg
  have hSq : r^2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hr₁ hr]
  refine h.trans ((add_le_add (mul_le_mul_of_nonneg_left (h₁.bound n hn) hr)
    (mul_le_mul hSq (h₂.bound n hn) (norm_nonneg _) hr)).trans_eq ?_)
  ring

/-- The exact factorizations retain the two radius factors under all
admissible parameter derivatives of the same harmonic replacement. -/
theorem norm_iteratedFDeriv_factored_poisson_remainder_le
    (A₀ : E →L[ℝ] F) (T₀ : U →L[ℝ] F) (A₁ A₂ : P → E →L[ℝ] F) (T₁ T₂ : P → U →L[ℝ] F)
    (x : P) (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1)
    (N : ℕ) (C I : ℝ) (hC : 0 ≤ C) (hI : 0 ≤ I)
    (hA₀ : A₀.IsInvertible) (hI₀ : ‖A₀.inverse‖ ≤ I)
    (hA₁ : LocalSmoothJetBudget A₁ x N C) (hA₂ : LocalSmoothJetBudget A₂ x N C)
    (hT₁ : LocalSmoothJetBudget T₁ x N C) (hT₂ : LocalSmoothJetBudget T₂ x N C)
    (hA : (A₀+r • A₁ x+r^2 • A₂ x).IsInvertible)
    (hIA : ‖(A₀+r • A₁ x+r^2 • A₂ x).inverse‖ ≤ I)
    (L : H →L[ℝ] U) (hFlat : T₀.comp L = 0)
    (n : ℕ) (hn : n ≤ N) :
    let A (p : P) := A₀+r • A₁ p+r^2 • A₂ p
    let T (p : P) := T₀+r • T₁ p+r^2 • T₂ p
    let CI := I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*(2*C))^N)
    ‖iteratedFDeriv ℝ n (fun p => (A p).inverse.comp ((T p).comp L)-
      r • A₀.inverse.comp ((T₁ p).comp L)) x‖ ≤
      poissonAffineRemainderJetBudget N CI I (2*C) C C L*r^2 := by
  dsimp only
  let A (p : P) := A₀+r • A₁ p+r^2 • A₂ p
  let T (p : P) := T₀+r • T₁ p+r^2 • T₂ p
  let CI := I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*(2*C))^N)
  have hCI : 0 ≤ CI := by dsimp only [CI]; positivity
  have hAs : ContDiffAt ℝ ∞ A x :=
    (contDiffAt_const.add (hA₁.smooth.const_smul r)).add (hA₂.smooth.const_smul (r^2))
  have hTs : ContDiffAt ℝ ∞ T x :=
    (contDiffAt_const.add (hT₁.smooth.const_smul r)).add (hT₂.smooth.const_smul (r^2))
  have hDiff : LocalSmoothJetBudget (fun p => A p-A₀) x N ((2*C)*r) := by
    have hE : (fun p => A p-A₀) = fun p => r • A₁ p+r^2 • A₂ p := by
      funext p
      dsimp only [A]
      abel
    rw [hE]
    exact localSmoothJetBudget_affine_sub_flat hA₁ hA₂ r hr hr₁
  have hPosA (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) : ‖iteratedFDeriv ℝ j A x‖ ≤ 2*C := by
    have hh := hDiff.bound j hjN
    change ‖iteratedFDeriv ℝ j (A-(fun _ => A₀)) x‖ ≤ (2*C)*r at hh
    rw [iteratedFDeriv_sub_apply (hAs.of_le (by simp)) contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega : j ≠ 0),Pi.zero_apply,sub_zero] at hh
    exact hh.trans (mul_le_of_le_one_right (by positivity) hr₁)
  have hInv (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun p => (A p).inverse) x‖ ≤ CI :=
    norm_iteratedFDeriv_inverse_family_le_of_isInvertible A x hA hAs N I (2*C) hI (by positivity) hIA hPosA j hj
  have hRest (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun p => T p-T₀-r • T₁ p) x‖ ≤ C*r^2 := by
    have he : (fun p => T p-T₀-r • T₁ p) = fun p => r^2 • T₂ p := by
      funext p
      dsimp only [T]
      abel
    rw [he,norm_iteratedFDeriv_const_smul_at _ x hT₂.smooth,abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hT₂.bound j hj) (sq_nonneg r)).trans_eq (mul_comm _ _)
  exact norm_iteratedFDeriv_poisson_affine_remainder_le A A₀ T T₁ T₀ L x hAs hTs hT₁.smooth
    hA hA₀ hFlat N r CI I (2*C) C C hr hCI hI (by positivity) hC hC hI₀
    hInv hDiff.bound hT₁.bound hRest n hn

end CalderonN
