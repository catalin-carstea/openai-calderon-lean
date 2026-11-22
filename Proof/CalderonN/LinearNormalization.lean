module

public import Proof.CalderonN.LinearMetric

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

public section

/-! Linear coordinate normalization from the checked 3D chart proof.
The matrix congruence is unchanged. The positive square root and an
orthonormal basis extending the chosen normal replace the three
explicit frame vectors. -/
noncomputable section
open Set Matrix
open scoped ContDiff Matrix MatrixOrder InnerProductSpace

namespace CalderonN

variable {n : ℕ} [NeZero n]

theorem linearPullbackMetric_comp (g : MetricField n) (A B : X n ≃L[ℝ] X n) :
    linearPullbackMetric (linearPullbackMetric g A) B =
      linearPullbackMetric g (B.trans A) := by
  have h : (B.trans A).toContinuousLinearMap = A.toContinuousLinearMap.comp B.toContinuousLinearMap := by
    ext x
    rfl
  funext y
  simp only [linearPullbackMetric, h, coordinateMatrix_comp, Matrix.transpose_mul]
  change _ = (_ * _) * g (A (B y)) * (_ * _)
  simp only [Matrix.mul_assoc]

theorem linearPullbackMetric_eq_iff {g₁ g₂ : MetricField n} (A : X n ≃L[ℝ] X n) (y : X n) :
    linearPullbackMetric g₁ A y = linearPullbackMetric g₂ A y ↔ g₁ (A y) = g₂ (A y) := by
  constructor
  · intro h
    let M := coordinateMatrix A.toContinuousLinearMap
    let B := coordinateMatrix A.symm.toContinuousLinearMap
    have hMB : M * B = 1 := coordinateMatrix_mul_symm A
    have ht : Bᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hMB, Matrix.transpose_one]
    have hback (K : Mat n) : Bᵀ * (Mᵀ * K * M) * B = K := by
      calc
        _ = (Bᵀ * Mᵀ) * K * (M * B) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hMB, ht, one_mul, mul_one]
    have h' := congrArg (fun K : Mat n => Bᵀ * K * B) h
    change Bᵀ * (Mᵀ * g₁ (A y) * M) * B = Bᵀ * (Mᵀ * g₂ (A y) * M) * B at h'
    rwa [hback, hback] at h'
  · intro h
    simp [linearPullbackMetric, h]

private theorem exists_metric_orthonormalizing_equiv
    {M : Mat n} (hM : M.PosDef) :
    ∃ A : X n ≃L[ℝ] X n, linearPullbackMetric (fun _ => M) A = 1 := by
  let S : Mat n := CFC.sqrt M
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  have hSq : S * S = M := by
    simpa only [S, pow_two] using CFC.sq_sqrt M hM.posSemidef.nonneg
  have hD : S.det ≠ 0 := by
    intro hz
    have he := congrArg Matrix.det hSq
    rw [Matrix.det_mul, hz, zero_mul] at he
    exact hM.det_pos.ne' he.symm
  have hSD : IsUnit S.det := isUnit_iff_ne_zero.mpr hD
  have hF : (S⁻¹).det ≠ 0 :=
    isUnit_iff_ne_zero.mp (by simpa [Matrix.det_nonsing_inv] using hSD.inv)
  let A : X n ≃L[ℝ] X n := (Matrix.toEuclideanLin (S⁻¹)).equivOfDetNeZero
    (by change LinearMap.det (Matrix.toLpLin 2 2 (S⁻¹)) ≠ 0
        rw [LinearMap.det_toLpLin]; exact hF) |>.toContinuousLinearEquiv
  have hA : coordinateMatrix A.toContinuousLinearMap = S⁻¹ := by
    change Matrix.toEuclideanLin.symm (Matrix.toEuclideanLin (S⁻¹)) = S⁻¹
    exact LinearEquiv.symm_apply_apply _ _
  have hSt : Sᵀ = S := by
    have hs : Sᴴ = S := hS.isHermitian
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hs
  refine ⟨A, funext fun y => ?_⟩
  rw [linearPullbackMetric, hA, Matrix.transpose_nonsing_inv, hSt]
  change S⁻¹ * M * S⁻¹ = 1
  rw [← hSq, ← Matrix.mul_assoc (S⁻¹) S S, Matrix.nonsing_inv_mul _ hSD, one_mul, Matrix.mul_nonsing_inv _ hSD]

private theorem isometry_pullback_one (Q : X n ≃ₗᵢ[ℝ] X n) :
    linearPullbackMetric (1 : MetricField n) Q.toContinuousLinearEquiv = 1 := by
  funext y
  ext i j
  simp only [linearPullbackMetric, Pi.one_apply, Matrix.mul_one, Matrix.mul_apply,
    Matrix.transpose_apply, coordinateMatrix_apply, Matrix.one_apply]
  change (∑ a : I n, Q (axis i) a * Q (axis j) a) = if i = j then 1 else 0
  calc
    _ = ⟪Q (axis i), Q (axis j)⟫_ℝ := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, mul_comm]
    _ = ⟪axis i, axis j⟫_ℝ := Q.inner_map_map _ _
    _ = _ := by simp [axis, EuclideanSpace.inner_single_left, PiLp.single_apply, eq_comm]

private theorem exists_normalizing_isometry
    (j : I n) (l : X n →L[ℝ] ℝ) (hl : l ≠ 0) :
    ∃ Q : X n ≃ₗᵢ[ℝ] X n, ∃ c > (0 : ℝ), ∀ z : X n, l (Q z) = c * z j := by
  classical
  let v := (InnerProductSpace.toDual ℝ (X n)).symm l
  have hDual : InnerProductSpace.toDual ℝ (X n) v = l :=
    (InnerProductSpace.toDual ℝ (X n)).apply_symm_apply l
  have hv : v ≠ 0 := by
    intro he
    apply hl
    rw [← hDual, he, map_zero]
  have hvN : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hNu : ‖u‖ = 1 := by
    rw [show u = ‖v‖⁻¹ • v from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvN), inv_mul_cancel₀ hvN.ne']
  have hUv : v = ‖v‖ • u := by rw [show u = ‖v‖⁻¹ • v from rfl, smul_smul, mul_inv_cancel₀ hvN.ne', one_smul]
  have hO : Orthonormal ℝ (({j} : Set (I n)).domRestrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro a b
    have hab : a = b := Subtype.ext ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)
    simp only [Set.domRestrict_apply, hab, ite_true, real_inner_self_eq_norm_sq, hNu, one_pow]
  obtain ⟨B,hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hO
  let Q : X n ≃ₗᵢ[ℝ] X n := B.repr.symm
  have hQ : Q (axis j) = u := (B.repr_symm_single j).trans (hB j (Set.mem_singleton _))
  refine ⟨Q,‖v‖,hvN,fun z => ?_⟩
  calc
    l (Q z) = ⟪v, Q z⟫_ℝ := by rw [← hDual, InnerProductSpace.toDual_apply_apply]
    _ = ‖v‖ * ⟪u, Q z⟫_ℝ := (congrArg (fun w => ⟪w, Q z⟫_ℝ) hUv).trans
      (real_inner_smul_left _ _ _)
    _ = ‖v‖ * ⟪axis j, z⟫_ℝ := by rw [← hQ, Q.inner_map_map]
    _ = ‖v‖ * z j := by simp [axis, EuclideanSpace.inner_single_left]

/-- One change of coordinates normalizes the center metric and aligns the
nonzero separating covector with the selected coordinate. -/
theorem exists_metric_separator_normalization (j : I n) {M : Mat n} (hM : M.PosDef)
    (l : X n →L[ℝ] ℝ) (hl : l ≠ 0) :
    ∃ (A : X n ≃L[ℝ] X n) (c : ℝ), 0 < c ∧ linearPullbackMetric (fun _ => M) A 0 = 1 ∧
      ∀ v : X n, l (A v) = c * v j := by
  obtain ⟨A,hA⟩ := exists_metric_orthonormalizing_equiv hM
  let l₀ := l.comp A.toContinuousLinearMap
  have hl₀ : l₀ ≠ 0 := by
    intro he
    apply hl
    ext z
    have h := congrFun (congrArg (fun T : X n →L[ℝ] ℝ => (T : X n → ℝ)) he) (A.symm z)
    simpa [l₀] using h
  obtain ⟨Q,c,hc,hQ⟩ := exists_normalizing_isometry j l₀ hl₀
  refine ⟨Q.toContinuousLinearEquiv.trans A,c,hc,?_,hQ⟩
  rw [← linearPullbackMetric_comp, hA, isometry_pullback_one]
  rfl

end CalderonN
