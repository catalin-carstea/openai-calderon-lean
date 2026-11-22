/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Ellipticity.Basic

public section

noncomputable section

open scoped NNReal

namespace LipschitzOnWith

variable {α 𝕜 : Type*} [PseudoMetricSpace α] [NormedDivisionRing 𝕜]

/-- The reciprocal of a `K`-Lipschitz function on `s` whose norm is at least `m > 0` on `s` is
`K / m²`-Lipschitz on `s`. -/
theorem inv_of_le_norm {f : α → 𝕜} {s : Set α} {K m : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hm : 0 < m) (hfm : ∀ x ∈ s, (m : ℝ) ≤ ‖f x‖) :
    LipschitzOnWith (K / m ^ 2) (fun x => (f x)⁻¹) s :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    have hx' : (0 : ℝ) < ‖f x‖ := (NNReal.coe_pos.2 hm).trans_le (hfm x hx)
    have hy' : (0 : ℝ) < ‖f y‖ := (NNReal.coe_pos.2 hm).trans_le (hfm y hy)
    rw [dist_inv_inv₀ (norm_pos_iff.1 hx') (norm_pos_iff.1 hy'),
      div_le_iff₀ (mul_pos hx' hy')]
    calc dist (f x) (f y) ≤ K * dist x y := hf.dist_le_mul x hx y hy
      _ = K / m ^ 2 * dist x y * (m * m) := by
          field_simp [(NNReal.coe_pos.2 hm).ne']
      _ ≤ (K / m ^ 2 : ℝ≥0) * dist x y * (‖f x‖ * ‖f y‖) := by
          push_cast
          gcongr
          exacts [hfm x hx, hfm y hy]

end LipschitzOnWith

namespace TauCeti.PDE
open Set
open scoped NNReal
variable {n : Type*} [Fintype n]
section Continuity

variable {X : Type*} [TopologicalSpace X]

/-- A coefficient field is continuous on a set as soon as its matrix bilinear forms vary
continuously there: the entry `aⁱʲ(x)` is the value of `matrixBilinearForm (a x)` on the `i`-th
and `j`-th standard basis vectors. -/
lemma continuousOn_of_continuousOn_matrixBilinearForm {s : Set X} {a : X → Matrix n n ℝ}
    (ha : ContinuousOn (fun x => matrixBilinearForm (a x)) s) : ContinuousOn a s := by
  classical
  have hM : Continuous fun B : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ =>
      Matrix.of fun i j => B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
    continuous_matrix fun i j =>
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).comp
        (ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i (1 : ℝ)))).continuous
  refine (hM.comp_continuousOn ha).congr fun x _ => ?_
  ext i j
  simp

/-- A coefficient field is continuous as soon as its matrix bilinear forms vary continuously. -/
lemma continuous_of_continuous_matrixBilinearForm {a : X → Matrix n n ℝ}
    (ha : Continuous fun x => matrixBilinearForm (a x)) : Continuous a :=
  continuousOn_univ.1 (continuousOn_of_continuousOn_matrixBilinearForm ha.continuousOn)

end Continuity
/-- The coefficients `x ↦ ⟪p, a(x) q⟫` of a coefficient field that is `K`-Lipschitz on `s` as a
bilinear form are `K ‖p‖ ‖q‖`-Lipschitz on `s`. -/
theorem lipschitzOnWith_matrixBilinearForm_apply_apply {X : Type*} [PseudoEMetricSpace X]
    {a : X → Matrix n n ℝ} {s : Set X} {K : ℝ≥0}
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) s)
    (p q : EuclideanSpace ℝ n) :
    LipschitzOnWith (K * ‖p‖₊ * ‖q‖₊) (fun x => matrixBilinearForm (a x) p q) s := by
  -- This is `x ↦ a x` followed by evaluation at `p` and then at `q`.
  have h := ((ContinuousLinearMap.lipschitzWith_apply q).comp
    (ContinuousLinearMap.lipschitzWith_apply p)).comp_lipschitzOnWith hK
  have hc : ‖q‖₊ * ‖p‖₊ * K = K * ‖p‖₊ * ‖q‖₊ := by ring
  rwa [hc] at h

/-- If `a` is uniformly elliptic and bounded on `s` and `x ↦ a(x)` is Lipschitz on `s` as a bilinear
form, then for `w ≠ 0` the form `a(x)(w, w)` is nonzero on `s` and its reciprocal is bounded and
Lipschitz on `s`. -/
theorem exists_lipschitzOnWith_inv_matrixBilinearForm_self {X : Type*} [PseudoMetricSpace X]
    [DecidableEq n] {a : X → Matrix n n ℝ} {s : Set X} {K : ℝ≥0} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn s a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) s)
    {w : EuclideanSpace ℝ n} (hw : w ≠ 0) :
    ∃ (L : ℝ≥0) (B : ℝ),
      LipschitzOnWith L (fun x => (matrixBilinearForm (a x) w w)⁻¹) s ∧
      (∀ x ∈ s, ‖(matrixBilinearForm (a x) w w)⁻¹‖ ≤ B) ∧
      ∀ x ∈ s, matrixBilinearForm (a x) w w ≠ 0 := by
  have hβL := lipschitzOnWith_matrixBilinearForm_apply_apply hK
  set m : ℝ := lam * ‖w‖ ^ 2
  have hm : 0 < m := mul_pos ha.pos (pow_pos (norm_pos_iff.2 hw) 2)
  have hcm : ∀ x ∈ s, m ≤ matrixBilinearForm (a x) w w :=
    fun x hx => by simpa only [m, matrixBilinearForm_self] using ha.lower_bound hx w
  have hrL : LipschitzOnWith (K * ‖w‖₊ * ‖w‖₊ / ⟨m, hm.le⟩ ^ 2)
      (fun x => (matrixBilinearForm (a x) w w)⁻¹) s :=
    (hβL w w).inv_of_le_norm (m := ⟨m,hm.le⟩) (NNReal.coe_pos.mp hm) fun x hx =>
      (hcm x hx).trans (Real.le_norm_self (matrixBilinearForm (a x) w w))
  refine ⟨_, m⁻¹, hrL, fun x hx => ?_, fun x hx => (hm.trans_le (hcm x hx)).ne'⟩
  have hx' := hm.trans_le (hcm x hx)
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hx']
  exact inv_anti₀ hm (hcm x hx)

end TauCeti.PDE
