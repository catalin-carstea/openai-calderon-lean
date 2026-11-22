module

public import Proof.CalderonPatch.NativeBoundaryLayerCoefficients
public import Proof.CalderonPatch.BoundaryLayerCutoffEstimate

import Mathlib.Tactic

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I MetricField contDiffOn_metric_inv_entry)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n + 1)

private theorem exists_uniform_normalFaceTaylor_bound
    {O : Set Z} (hO : IsOpen O) {f : Z → ℝ} (hf : ContDiffOn ℝ ∞ f O)
    {K : Set Y} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hRect : K ×ˢ Icc 0 r ⊆ signedLayerCoordinates ⁻¹' O) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ t ∈ Icc 0 r,
      ‖(f (signedLayerCoordinates (y,t)) : ℂ) -
        ∑ j ∈ Finset.range (N + 1), (t : ℂ) ^ j * normalFaceTaylor f j y‖ ≤ C * t ^ (N + 1) := by
  have hf' : ContDiffOn ℝ ∞ (f ∘ signedLayerCoordinates) (signedLayerCoordinates ⁻¹' O) :=
    hf.comp signedLayerCoordinates.contDiff.contDiffOn (mapsTo_preimage signedLayerCoordinates O)
  obtain ⟨C,hC,hB⟩ := exists_uniform_normal_taylor_bound
    (hO.preimage signedLayerCoordinates.continuous) hf' hK hr hRect N
  refine ⟨C,hC,fun y hy t ht => ?_⟩
  have h := hB y hy t ht
  have hCast :
      (∑ j ∈ Finset.range (N + 1), (t : ℂ) ^ j * normalFaceTaylor f j y) =
        ((∑ j ∈ Finset.range (N + 1), (t ^ j / (j.factorial : ℝ)) *
          iteratedDeriv j (fun s : ℝ => f (signedLayerCoordinates (y,s))) 0 : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    unfold normalFaceTaylor
    ring
  rw [hCast, ← Complex.ofReal_sub, Complex.norm_real]
  exact h

/-- The coefficient discrepancies used by the signed split negative
Laplacian have a true uniform Taylor remainder on a compact collar. -/
theorem exists_native_layerCoefficientTaylor_bound
    {O : Set Z} (hO : IsOpen O) (g : MetricField (n + 1))
    (hg : CalderonN.SmoothMetric O g) {U : Set Y}
    (hU : MapsTo (fun y : Y => signedLayerCoordinates (y,(0 : ℝ))) U O)
    (ξ : I n → ℝ) (hξ : ξ ≠ 0)
    {K : Set Y} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hRect : K ×ˢ Icc 0 r ⊆ signedLayerCoordinates ⁻¹' O) (N : ℕ) :
    let B := boundaryLayerCoefficientsOfMetric hO g hg hU ξ hξ
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ t ∈ Icc 0 r,
      let z := signedLayerCoordinates (y,t)
      (∀ i j : I n,
        ‖((g z)⁻¹ i.succ j.succ : ℝ) - B.matrixTaylor N y t i j‖ ≤ C * t ^ (N + 1)) ∧
      ‖((-2 * laplaceFirstCoeff g z 0 : ℝ) : ℂ) - B.normalTaylor N y t‖ ≤ C * t ^ (N + 1) ∧
      (∀ i : I n,
        ‖(laplaceFirstCoeff g z i.succ : ℂ) - B.tangentTaylor N y t i‖ ≤ C * t ^ (N + 1)) := by
  let B := boundaryLayerCoefficientsOfMetric hO g hg hU ξ hξ
  let A (i j : I n) (z : Z) := (g z)⁻¹ i.succ j.succ
  let b (z : Z) := (-2 : ℝ) * laplaceFirstCoeff g z 0
  let c (i : I n) (z : Z) := laplaceFirstCoeff g z i.succ
  have hA (i j : I n) : ContDiffOn ℝ ∞ (A i j) O :=
    contDiffOn_metric_inv_entry hg i.succ j.succ
  have hb : ContDiffOn ℝ ∞ b O := contDiffOn_const.mul (contDiffOn_laplaceFirstCoeff hO hg 0)
  have hc (i : I n) : ContDiffOn ℝ ∞ (c i) O := contDiffOn_laplaceFirstCoeff hO hg i.succ
  choose CA hCA hEA using fun i j : I n =>
    exists_uniform_normalFaceTaylor_bound hO (hA i j) hK hr hRect N
  obtain ⟨Cb,hCb,hEb⟩ := exists_uniform_normalFaceTaylor_bound hO hb hK hr hRect N
  choose Cc hCc hEc using fun i : I n =>
    exists_uniform_normalFaceTaylor_bound hO (hc i) hK hr hRect N
  let C := (∑ i : I n, ∑ j : I n, CA i j) + Cb + ∑ i : I n, Cc i
  have hCA₀ (i : I n) : 0 ≤ ∑ j : I n, CA i j := Finset.sum_nonneg fun j _ => hCA i j
  have hA₀ : 0 ≤ ∑ i : I n, ∑ j : I n, CA i j := Finset.sum_nonneg fun i _ => hCA₀ i
  have hc₀ : 0 ≤ ∑ i : I n, Cc i := Finset.sum_nonneg fun i _ => hCc i
  refine ⟨C,add_nonneg (add_nonneg hA₀ hCb) hc₀,fun y hy t ht => ⟨?_,?_,?_⟩⟩
  · intro i j
    have h₀ := Finset.single_le_sum (s := Finset.univ) (f := CA i)
      (fun k _ => hCA i k) (Finset.mem_univ j)
    have h₁ := Finset.single_le_sum (s := Finset.univ) (f := fun i => ∑ j : I n, CA i j)
      (fun k _ => hCA₀ k) (Finset.mem_univ i)
    have h₂ : CA i j ≤ C := (h₀.trans h₁).trans (by dsimp only [C]; linarith)
    exact (hEA i j y hy t ht).trans (mul_le_mul_of_nonneg_right h₂ (pow_nonneg ht.1 _))
  · have h : Cb ≤ C := by dsimp only [C]; linarith
    exact (hEb y hy t ht).trans (mul_le_mul_of_nonneg_right h (pow_nonneg ht.1 _))
  · intro i
    have h₀ := Finset.single_le_sum (s := Finset.univ) (f := Cc)
      (fun k _ => hCc k) (Finset.mem_univ i)
    have h₁ : Cc i ≤ C := h₀.trans (by dsimp only [C]; linarith)
    exact (hEc i y hy t ht).trans (mul_le_mul_of_nonneg_right h₁ (pow_nonneg ht.1 _))

end CalderonPatch.BoundaryLayer
