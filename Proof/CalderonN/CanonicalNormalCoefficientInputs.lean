module

public import Proof.CalderonN.UniformCanonicalFrameJets
public import Proof.CalderonN.LocalSmoothJetBudget
public import Proof.CalderonN.NormalCoefficientVelocityJets

import Proof.CalderonN.CompactLocalJetBounds
import Proof.CalderonN.ConnectionOperatorBounds
import Proof.CalderonN.FirstMetricConformalDepth
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Bounds for the reference frame operator and the scalar center
normalization used in the actual first coefficient. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem uniform_canonical_frameVectorLinear_jets (K : ℝ) (hK : 0 < K) {m : ℕ}
    (M : Fin (m+1) → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Set (X dim)} {g : MetricField dim}, IsOpen Ω →
      Elliptic Ω K g →
      (∀ (j : Fin (m+1)) i k, ∀ y ∈ Ω, ‖iteratedFDeriv ℝ j.val (fun x => g x i k) y‖ ≤ M j) →
      ∀ y ∈ Ω, LocalSmoothJetBudget
        (fun x => frameVectorLinear (fun z => smoothMetricFrame (g z)) x) y m C := by
  obtain ⟨B,hB,hFrame⟩ := uniform_canonical_metric_frame_jets (dim:=dim) K hK M
  let C := 1+(dim:ℝ)*B
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  refine ⟨C,le_add_of_nonneg_right (by positivity),?_⟩
  intro Ω g hΩ hE hJets y hy
  let e (z : X dim) := smoothMetricFrame (g z)
  let L (i : I dim) := ContinuousLinearMap.smulRightL ℝ (X dim) (X dim) (EuclideanSpace.proj i)
  have hSmooth : ∀ i, ContDiffAt ℝ ∞ (fun x => e x i) y :=
    fun i => (contDiffOn_smoothMetricFrame hE.1 (fun _ hx => hE.posDef hK hx) i).contDiffAt (hΩ.mem_nhds hy)
  have hL (i : I dim) : ‖L i‖ ≤ 1 := by
    haveI : Nontrivial (X dim) := nontrivial_of_ne (axis 0) 0 (by
      intro h
      have hh := congrArg norm h
      rw [norm_axis,norm_zero] at hh
      norm_num at hh)
    dsimp only [L]
    rw [ContinuousLinearMap.norm_smulRightL]
    exact norm_euclidean_proj_le_one i
  have hColumn (i : I dim) : LocalSmoothJetBudget (fun x => (EuclideanSpace.proj (𝕜:=ℝ) i).smulRight (e x i)) y m B := by
    have H : LocalSmoothJetBudget (fun x => e x i) y m B := ⟨hSmooth i,hFrame hΩ hE hJets y hy i⟩
    exact (H.linear_postcomp (L i)).enlarge (mul_le_of_le_one_left hB₀ (hL i))
  have h := LocalSmoothJetBudget.finite_sum Finset.univ _ (fun _ => B) (fun i _ => hColumn i)
  have hBound : (∑ _i : I dim, B) ≤ C := by
    simp only [C,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact le_add_of_nonneg_left zero_le_one
  change LocalSmoothJetBudget (fun x => frameVectorLinear e x) y m C
  rw [show (fun x => frameVectorLinear e x) =
    (fun x => ∑ i, (EuclideanSpace.proj (𝕜:=ℝ) i).smulRight (e x i)) from rfl]
  exact h.enlarge hBound

private def canonicalCenterDensityScaleInverse (dim : ℕ) (p : ℝ × ℝ) : ℝ :=
  (Real.exp (-((1/2:ℝ)*(Real.log p.1-Real.log p.2)))^(dim-2))⁻¹

theorem uniform_first_center_inverse_density_jets (K : ℝ) (hK : 0 < K) {m : ℕ}
    (M : Fin (m+1) → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Set (X dim)} {d : Data dim}, IsOpen Ω →
      Background Ω K M d.γ d.g₁ d.g₂ d.frame →
      ∀ y ∈ Ω, LocalSmoothJetBudget (fun x => (firstMetricDensityFactor d.γ d.g₁ x)⁻¹) y m C := by
  let J := Icc K⁻¹ K ×ˢ Icc K⁻¹ K
  let R := 1+∑ j,|M j|
  have hR : 1 ≤ R := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hBound (j : Fin (m+1)) : M j ≤ R := (le_abs_self _).trans
    ((Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left (zero_le_one : (0:ℝ) ≤ 1)))
  have hSmooth (p : ℝ × ℝ) (hp : p ∈ J) : ContDiffAt ℝ ∞ (canonicalCenterDensityScaleInverse dim) p := by
    have h₁ : 0 < p.1 := (inv_pos.mpr hK).trans_le hp.1.1
    have h₂ : 0 < p.2 := (inv_pos.mpr hK).trans_le hp.2.1
    have hF : ContDiffAt ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ) p := contDiffAt_fst
    have hS : ContDiffAt ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ) p := contDiffAt_snd
    exact (((contDiffAt_const.mul ((hF.log h₁.ne').sub (hS.log h₂.ne'))).neg.exp).pow _).inv
      (pow_ne_zero _ (Real.exp_pos _).ne')
  obtain ⟨B,hB,hJet⟩ := exists_uniform_local_finite_jet_bound (isCompact_Icc.prod isCompact_Icc) hSmooth m
  have hFac : (1:ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
  refine ⟨m.factorial*B*R^m,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hFac hB) (one_le_pow₀ hR),?_⟩
  intro Ω d hΩ hd y hy
  let A (x : X dim) := d.γ x 0 0
  let D (x : X dim) := d.g₁ x 0 0
  have hA : LocalSmoothJetBudget A y m R := ⟨(hd.1.1 0 0).contDiffAt (hΩ.mem_nhds hy),
    fun j hj => (hd.2.2.2.2.1 d.γ (by simp) ⟨j,by omega⟩ 0 0 y hy).trans (hBound _)⟩
  have hD : LocalSmoothJetBudget D y m R := ⟨(hd.2.1.1 0 0).contDiffAt (hΩ.mem_nhds hy),
    fun j hj => (hd.2.2.2.2.1 d.g₁ (by simp) ⟨j,by omega⟩ 0 0 y hy).trans (hBound _)⟩
  have hInput := (hA.prod hD).enlarge (le_of_eq (max_self R))
  have hPoint (g : MetricField dim) (hg : Elliptic Ω K g) : g y 0 0 ∈ Icc K⁻¹ K := by
    have H := (hg.2 y hy).2 (axis (0:I dim))
    simpa [metricPair,axis] using H
  have hJ : (A y,D y) ∈ J := ⟨hPoint d.γ hd.1,hPoint d.g₁ hd.2.1⟩
  have hOuter : LocalSmoothJetBudget (canonicalCenterDensityScaleInverse dim) (A y,D y) m B :=
    ⟨hSmooth _ hJ, hJet _ hJ⟩
  have h := hInput.comp hOuter hR
  have hEq : canonicalCenterDensityScaleInverse dim ∘ (fun y => (A y,D y)) =
      fun x => (firstMetricDensityFactor d.γ d.g₁ x)⁻¹ := by
    funext x
    simp only [Function.comp_apply,canonicalCenterDensityScaleInverse,A,D,firstMetricDensityFactor,
      firstMetricScale,firstMetricConformalDepth]
  rwa [hEq] at h

end CalderonN
