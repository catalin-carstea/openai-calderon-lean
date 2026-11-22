module

public import Proof.CalderonN.EllipticCalculus
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

public section

/- Compact positivity in the elementary Euclidean norm. This is the
   zero-linear-constraint case of the rank-one compactness argument
   used by the 3D InteriorFluxEnergy proof. -/
noncomputable section
open Set Metric
namespace CalderonN.Elliptic

variable {d : ℕ} [NeZero d]

set_option maxHeartbeats 1000000 in
theorem lower_ellipticity_on_compact {P : Type*} [TopologicalSpace P]
    {a : Fin d → Fin d → P → ℝ} (ha : ∀ i j, Continuous (a i j))
    {K : Set P} (hK : IsCompact K) (hpos : ∀ p ∈ K, Matrix.PosDef (fun i j => a i j p : Mat d)) :
    ∃ lo : ℝ, 0 < lo ∧ ∀ p ∈ K, ∀ ξ : Fin d → ℝ,
      lo * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, ξ i * a i j p * ξ j := by
  rcases K.eq_empty_or_nonempty with rfl | hKn
  · exact ⟨1, one_pos, by simp⟩
  let S := Metric.sphere (0 : X d) 1
  let Q (x : P × X d) : ℝ := ∑ i, ∑ j, x.2 i * a i j x.1 * x.2 j
  have hQ : Continuous Q := by
    unfold Q
    exact continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ =>
        (((EuclideanSpace.proj i).continuous.comp continuous_snd).mul
          ((ha i j).comp continuous_fst)).mul ((EuclideanSpace.proj j).continuous.comp continuous_snd)
  have hS : S.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨p₀, hp₀, hmin⟩ := (hK.prod (isCompact_sphere (0 : X d) 1)).exists_isMinOn
    (hKn.prod hS) hQ.continuousOn
  have hposQ : 0 < Q p₀ := by
    have hn : ‖p₀.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp₀.2
    have hξ : (p₀.2 : Fin d → ℝ) ≠ 0 := by
      intro he
      have h0 : p₀.2 = 0 := WithLp.ofLp_injective 2 he
      simp [h0] at hn
    have hp := (hpos p₀.1 hp₀.1).dotProduct_mulVec_pos hξ
    unfold Q
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc] at hp ⊢
    exact hp
  refine ⟨Q p₀, hposQ, fun p hp ξ => ?_⟩
  let v : X d := WithLp.toLp 2 ξ
  by_cases hv : v = 0
  · have hξ : ξ = 0 := by simpa only [v, WithLp.toLp_eq_zero] using hv
    simp [hξ]
  have hvn := norm_pos_iff.mpr hv
  let u : X d := ‖v‖⁻¹ • v
  have hu : u ∈ S := by
    change u ∈ Metric.sphere (0 : X d) 1
    rw [mem_sphere_zero_iff_norm]
    change ‖‖v‖⁻¹ • v‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hvn.le),
      inv_mul_cancel₀ hvn.ne']
  have heq : v = ‖v‖ • u := by
    unfold u
    rw [smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
  have hHom : Q (p, v) = ‖v‖ ^ 2 * Q (p, u) := by
    conv_lhs => rw [heq]
    simp only [Q, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hKu : (p,u) ∈ K ×ˢ S := ⟨hp,hu⟩
  have hmin' : Q p₀ ≤ Q (p,u) := hmin hKu
  have hVnorm : ‖v‖ ^ 2 = ∑ i, ξ i ^ 2 := EuclideanSpace.real_norm_sq_eq v
  calc
    _ = ‖v‖ ^ 2 * Q p₀ := by rw [hVnorm, mul_comm]
    _ ≤ ‖v‖ ^ 2 * Q (p,u) := mul_le_mul_of_nonneg_left hmin' (sq_nonneg ‖v‖)
    _ = Q (p,v) := hHom.symm
    _ = _ := rfl

end CalderonN.Elliptic
