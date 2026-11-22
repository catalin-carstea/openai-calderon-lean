module

public import Proof.CalderonN.BundleTraceCalculus

import Mathlib.Tactic
import Proof.CalderonN.SmallJetBounds

/-! Adapted from `ConstantMovingTraceAlgebra` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def scaledFirstTrace (r : (X dim) → ℝ) (A : (TraceAdjoint dim)) (j : (I dim)) : (Field dim) :=
  baseMul r (adjointField A j (1 : (Field dim)))

theorem smoothNear_scaledFirstTrace {Y : Set (X dim)} {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)}
    {e : (Frame dim)} {r : (X dim) → ℝ} {A : (TraceAdjoint dim)}
    (hr : ContDiff ℝ ∞ r) (hA : IsMovingTraceAdjoint Y γ g e E r A) (j : (I dim)) :
    smoothNear (scaledFirstTrace r A j) (bundle Y γ) :=
  smoothNear_baseMul hr (hA j 1 (smoothNear_one_bundle Y γ)).1

/-- The only inverse radius in the trace operator on constants multiplies
a successive scaled angular adjoint with its radial contribution removed. -/
theorem movingTrace_one_eq_scaledFirstTrace {Y : Set (X dim)} {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)}
    {e : (Frame dim)} {r : (X dim) → ℝ} {A : (TraceAdjoint dim)}
    (hγ : SmoothMetric univ γ) (hE : ContDiff ℝ ∞ E) (hr : ContDiff ℝ ∞ r)
    (hDir : Dirichlet Y γ g E r)
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (hA : IsMovingTraceAdjoint Y γ g e E r A) (g₂ : (MetricField dim)) {q : (X dim) × (X dim)}
    (hq : q ∈ bundle Y γ) (hR : r q.1 ≠ 0) :
    let α := scaledFirstTrace r A
    movingTrace γ g₂ r A (1 : (Field dim)) q =
      (∑ i, ∑ j, (principal γ g₂ q.1 i j : ℂ) *
        (horizontal γ (α j) q.1 q.2 (axis i) +
          ((r q.1 : ℂ) * adjointField A i (α j) q -
            Complex.ofReal (coordDeriv i r q.1) * α j q)/(r q.1 : ℂ) -
          ∑ k, (christoffel γ q.1 k i j : ℂ) * α k q)) +
        ∑ k, (drift γ g₂ q.1 k : ℂ) * α k q := by
  let α := scaledFirstTrace r A
  let W (j : (I dim)) := traceDerivative γ A j (1 : (Field dim))
  have hW (j : (I dim)) : W j = adjointField A j (1 : (Field dim)) := by
    funext z
    change fderiv ℝ (fun _ : (X dim) × (X dim) => (1 : ℂ)) z
      (axis j,-connection γ z.1 (axis j) z.2) + adjointField A j 1 z = _
    simp
  have hα (j : (I dim)) : α j = baseMul r (W j) := by rw [hW]; rfl
  have ha (j : (I dim)) : α j q = (r q.1 : ℂ) * W j q := by rw [hα]; rfl
  have hRc : (r q.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  have hWq (j : (I dim)) : W j q = α j q / (r q.1 : ℂ) := by
    apply (eq_div_iff hRc).2
    rw [ha]
    ring
  have hSecond (i j : (I dim)) :
      (r q.1 : ℂ) * traceDerivative γ A i (W j) q =
        horizontal γ (α j) q.1 q.2 (axis i) +
          ((r q.1 : ℂ) * adjointField A i (α j) q -
            Complex.ofReal (coordDeriv i r q.1) * α j q)/(r q.1 : ℂ) := by
    have hWsm : smoothNear (W j) (bundle Y γ) :=
      (hW j).symm ▸ (hA j 1 (smoothNear_one_bundle Y γ)).1
    have h := traceDerivative_baseMul_on_bundle hγ hE hr hDir he hA hr hWsm i hq
    rw [← hα] at h
    change horizontal γ (α j) q.1 q.2 (axis i) + adjointField A i (α j) q =
      (r q.1 : ℂ) * traceDerivative γ A i (W j) q + Complex.ofReal (coordDeriv i r q.1) * W j q at h
    rw [hWq] at h
    rw [eq_sub_of_add_eq h.symm]
    field_simp [hRc]
    ring
  change (r q.1 : ℂ) * ((∑ i, ∑ j, (principal γ g₂ q.1 i j : ℂ) *
      (traceDerivative γ A i (W j) q - ∑ k, (christoffel γ q.1 k i j : ℂ) * W k q)) +
        ∑ k, (drift γ g₂ q.1 k : ℂ) * W k q) = _
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hSecond]
    rw [mul_left_comm,mul_sub,Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm,← ha]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm,← ha]

/-- An order-one radius error in the leading scaled adjoint and the
protected small coefficient perturbation give a constant-mode bound. -/
theorem norm_movingTrace_one_le_of_scaled_bounds {Y : Set (X dim)} {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)}
    {e : (Frame dim)} {r : (X dim) → ℝ} {A : (TraceAdjoint dim)}
    (hγ : SmoothMetric univ γ) (hE : ContDiff ℝ ∞ E) (hr : ContDiff ℝ ∞ r)
    (hDir : Dirichlet Y γ g E r)
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (hA : IsMovingTraceAdjoint Y γ g e E r A) (g₂ : (MetricField dim)) {q : (X dim) × (X dim)}
    (hq : q ∈ bundle Y γ) (hR : 0 < r q.1) {ε P G D H U B L : ℝ}
    (hSmall : smallJet γ g₂ q.1 ≤ ε * r q.1)
    (hP : ∀ i j, |principal γ g₂ q.1 i j| ≤ P)
    (hG : ∀ k i j, |christoffel γ q.1 k i j| ≤ G)
    (hD : ∀ k, |drift γ g₂ q.1 k| ≤ D)
    (hH : ∀ i j, ‖horizontal γ (scaledFirstTrace r A j) q.1 q.2 (axis i)‖ ≤ H)
    (hU : ∀ j, ‖scaledFirstTrace r A j q‖ ≤ U)
    (τ : (I dim) → (I dim) → ℂ) (hB : ∀ i j, ‖τ i j‖ ≤ B)
    (hzero : ∑ i, ∑ j, ((γ q.1)⁻¹ i j : ℂ) * τ i j = 0)
    (hL : ∀ i j, ‖(r q.1 : ℂ) * adjointField A i (scaledFirstTrace r A j) q -
      Complex.ofReal (coordDeriv i r q.1) * scaledFirstTrace r A j q - τ i j‖ ≤ L*r q.1) :
    ‖movingTrace γ g₂ r A (1 : (Field dim)) q‖ ≤ (dim:ℝ)^2*P*(H+(dim:ℝ)*G*U+L) + (dim:ℝ)^2*ε*B + (dim:ℝ)*D*U := by
  let α := scaledFirstTrace r A
  let R (i j : (I dim)) := (r q.1 : ℂ) * adjointField A i (α j) q -
    Complex.ofReal (coordDeriv i r q.1) * α j q
  let P₀ (i j : (I dim)) := principal γ g₂ q.1 i j
  let Q₀ (i j : (I dim)) := (γ q.1)⁻¹ i j
  let L₀ (i j : (I dim)) := horizontal γ (α j) q.1 q.2 (axis i) +
    (R i j - τ i j)/(r q.1 : ℂ) -
      ∑ k, (christoffel γ q.1 k i j : ℂ) * α k q
  let S := ∑ i : (I dim), ∑ j : (I dim), ((P₀ i j - Q₀ i j : ℝ) : ℂ) * τ i j
  let V := ∑ k : (I dim), (drift γ g₂ q.1 k : ℂ) * α k q
  have hSimp : ‖(r q.1 : ℂ)‖ = r q.1 := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  have hdifference (i j : (I dim)) : |P₀ i j-Q₀ i j| ≤ ε*r q.1 :=
    (abs_principal_sub_inverse_entry_le_smallJet γ g₂ q.1 i j).trans hSmall
  have hS : ‖S / (r q.1 : ℂ)‖ ≤ (dim:ℝ)^2*ε*B := by
    rw [norm_div,hSimp,div_le_iff₀ hR]
    have h := norm_coordinate_sum_le fun i => norm_coordinate_sum_le fun j =>
      norm_real_mul_le (hdifference i j) (hB i j)
    calc
      _ ≤ (dim:ℝ)*((dim:ℝ)*((ε*r q.1)*B)) := h
      _ = ((dim:ℝ)^2*ε*B)*r q.1 := by ring
  have hV : ‖V‖ ≤ (dim:ℝ)*(D*U) := norm_coordinate_sum_le fun k => norm_real_mul_le (hD k) (hU k)
  have hBase (i j : (I dim)) : ‖L₀ i j‖ ≤ H+(dim:ℝ)*G*U+L := by
    have hL' : ‖(R i j-τ i j)/(r q.1 : ℂ)‖ ≤ L := by
      rw [norm_div,hSimp,div_le_iff₀ hR]
      exact hL i j
    have hΓ := norm_coordinate_sum_le fun k => norm_real_mul_le (hG k i j) (hU k)
    dsimp only [L₀]
    calc
      ‖_ - _‖ ≤ ‖_‖ + ‖_‖ := norm_sub_le _ _
      _ ≤ (H+L) + (dim:ℝ)*(G*U) := add_le_add ((norm_add_le _ _).trans
        (add_le_add (hH i j) hL')) hΓ
      _ = _ := by ring
  have hSum : ‖∑ i : (I dim), ∑ j : (I dim), (P₀ i j : ℂ) * L₀ i j‖ ≤ (dim:ℝ)*((dim:ℝ)*(P*(H+(dim:ℝ)*G*U+L))) :=
    norm_coordinate_sum_le fun i => norm_coordinate_sum_le fun j => norm_real_mul_le (hP i j) (hBase i j)
  have hTotal : movingTrace γ g₂ r A (1:(Field dim)) q =
      ((∑ i : (I dim), ∑ j : (I dim), (P₀ i j : ℂ) * L₀ i j) + S/(r q.1 : ℂ)) + V := by
    rw [movingTrace_one_eq_scaledFirstTrace hγ hE hr hDir he hA g₂ hq hR.ne']
    change (∑ i, ∑ j, (P₀ i j : ℂ) *
      (horizontal γ (α j) q.1 q.2 (axis i) + R i j/(r q.1 : ℂ) -
        ∑ k, (christoffel γ q.1 k i j : ℂ) * α k q)) + V = _
    have hTerm (i j : I dim) :
        (P₀ i j : ℂ) *
          (horizontal γ (α j) q.1 q.2 (axis i) + R i j/(r q.1 : ℂ) -
            ∑ k, (christoffel γ q.1 k i j : ℂ) * α k q) =
        (P₀ i j : ℂ) * L₀ i j + (((P₀ i j - Q₀ i j : ℝ) : ℂ) * τ i j)/(r q.1 : ℂ) +
          ((Q₀ i j : ℂ) * τ i j)/(r q.1 : ℂ) := by
      dsimp only [L₀]
      rw [Complex.ofReal_sub]
      ring
    simp only [hTerm,Finset.sum_add_distrib,← Finset.sum_div,hzero,zero_div,add_zero,S,Q₀]

  rw [hTotal]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hSum hS)) hV)).trans_eq ?_
  ring

end CalderonN
