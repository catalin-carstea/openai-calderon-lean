module

public import Proof.CalderonN.PolynomialBallGreenPairing

import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! The homogeneous half-order trace estimate, using the energy
comparison from `NativeSmoothSharpTraceFinite` in the Proposition 5.3
release. The finite-mode argument directly uses the canonical
orthogonal projections and their harmonic polynomial representatives. -/

public section

noncomputable section
open scoped ContDiff ENNReal InnerProductSpace
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The nonconstant half-order boundary energy is bounded by the
bulk Dirichlet energy on the same smooth function. -/
theorem sum_halfTrace_energy_le (u : SmoothData dim) (s : Finset ℕ) :
    unitSphereArea dim * ∑ k ∈ s, (k : ℝ) *
      ‖harmonicProjection k (smoothSphereLift u.1 u.2)‖ ^ 2 ≤
    ‖TauCeti.W1p.gradient (smoothSobolev u)‖ ^ 2 := by
  let v := smoothSphereLift u.1 u.2
  let p (k : ℕ) := harmonicProjectionPolynomial k v
  let U (k : ℕ) : SmoothData dim :=
    ⟨polynomialEvaluation (p k).val,contDiff_polynomialEvaluation (p k).val⟩
  let g := TauCeti.W1p.gradient (smoothSobolev u)
  let w (k : ℕ) := TauCeti.W1p.gradient (smoothSobolev (U k))
  let G := ∑ k ∈ s, w k
  let M := unitSphereArea dim
  have hs (k : ℕ) : smoothSphereLift (U k).1 (U k).2 = (harmonicProjection k v : SphereL2 dim) :=
    (smoothSphereLift_polynomialEvaluation (p k).val).trans
      (polynomialSphereL2_harmonicProjectionPolynomial k v)
  have hp (k : ℕ) : polynomialSphereL2 (p k).val = (harmonicProjection k v : SphereL2 dim) :=
    polynomialSphereL2_harmonicProjectionPolynomial k v
  have hPair (i j : ℕ) :
      ⟪w i, w j⟫_ℝ = M * (j : ℝ) *
        ⟪(harmonicProjection i v : SphereL2 dim),(harmonicProjection j v : SphereL2 dim)⟫_ℝ := by
    have h := inner_nativeGradient_harmonicPolynomial (U i) j (p j).val (p j).property
    rw [hs i,hp j] at h
    exact h
  have hOrth (i j : ℕ) (hij : i ≠ j) : ⟪w i,w j⟫_ℝ = 0 := by
    rw [hPair,orthogonalSphereHarmonics dim i j hij _ (harmonicProjection i v).property
      _ (harmonicProjection j v).property,mul_zero]
  have hDiag (k : ℕ) : ⟪w k,w k⟫_ℝ = M * ((k : ℝ) * ‖harmonicProjection k v‖^2) := by
    rw [hPair,real_inner_self_eq_norm_sq,Submodule.norm_coe]
    ring
  have hAgainst (k : ℕ) : ⟪g,w k⟫_ℝ = M * ((k : ℝ) * ‖harmonicProjection k v‖^2) := by
    have e := inner_nativeGradient_harmonicPolynomial u k (p k).val (p k).property
    change ⟪g,w k⟫_ℝ = M * (k : ℝ) * ⟪v,polynomialSphereL2 (p k).val⟫_ℝ at e
    rw [hp k,← (harmonicSphereSubspace dim k).inner_orthogonalProjectionOnto_eq_of_mem_right
      (harmonicProjection k v) v] at e
    change ⟪g,w k⟫_ℝ = M * (k : ℝ) * ⟪harmonicProjection k v,harmonicProjection k v⟫_ℝ at e
    rw [real_inner_self_eq_norm_sq] at e
    rw [e]
    ring
  have hi : ⟪g,G⟫_ℝ = M * ∑ k ∈ s, (k : ℝ) * ‖harmonicProjection k v‖^2 := by
    simp only [G,inner_sum,hAgainst,Finset.mul_sum]
  have hn : ‖G‖^2 = M * ∑ k ∈ s, (k : ℝ) * ‖harmonicProjection k v‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [G,inner_sum,sum_inner,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single_of_mem j hj (fun i _ hij => hOrth i j hij),hDiag]
  have h := sq_nonneg ‖g-G‖
  rw [norm_sub_sq_real,hn,hi] at h
  change M * (∑ k ∈ s, (k : ℝ) * ‖harmonicProjection k v‖^2) ≤ ‖g‖^2
  linarith only [h]

theorem summable_halfTrace_energy (u : SmoothData dim) :
    Summable (fun k : ℕ => (k : ℝ) * ‖harmonicProjection k (smoothSphereLift u.1 u.2)‖^2) ∧
    (∑' k : ℕ, (k : ℝ) * ‖harmonicProjection k (smoothSphereLift u.1 u.2)‖^2) ≤
      ‖TauCeti.W1p.gradient (smoothSobolev u)‖^2 / unitSphereArea dim := by
  have h₀ (k : ℕ) : 0 ≤ (k : ℝ) * ‖harmonicProjection k (smoothSphereLift u.1 u.2)‖^2 :=
    by positivity
  have h (s : Finset ℕ) :
      (∑ k ∈ s, (k : ℝ) * ‖harmonicProjection k (smoothSphereLift u.1 u.2)‖^2) ≤
        ‖TauCeti.W1p.gradient (smoothSobolev u)‖^2 / unitSphereArea dim :=
    (le_div_iff₀ unitSphereArea_pos).mpr (by simpa only [mul_comm] using sum_halfTrace_energy_le u s)
  exact ⟨summable_of_sum_le h₀ h,Real.tsum_le_of_sum_le h₀ h⟩

end CalderonN
