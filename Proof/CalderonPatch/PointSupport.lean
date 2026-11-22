module

public import Proof.CalderonPatch.PointCutoff
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Filter Metric Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace CalderonPatch

variable {E : Type*} [NormedAddCommGroup E] {K : Compacts E}

section NormedSpace

variable [NormedSpace ℝ E]

/-- A continuous linear functional on smooth tests with a fixed compact support
is controlled by finitely many uniform derivative seminorms. -/
theorem exists_compactTest_finiteOrder (T : 𝓓_{K}(E, ℝ) →L[ℝ] ℝ) :
    ∃ m : ℕ, ∃ C > (0 : ℝ), ∀ (f : 𝓓_{K}(E, ℝ)) (ε : ℝ), 0 ≤ ε →
      (∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ ε) → ‖T f‖ ≤ C * ε := by
  let q : Seminorm ℝ 𝓓_{K}(E, ℝ) := (normSeminorm ℝ ℝ).comp T.toLinearMap
  let p := ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, _, hTC⟩ := Seminorm.bound_sum_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) q hq
  let D := (C : ℝ) * s.card + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨s.sup id, D, hD, ?_⟩
  intro f ε hε hf
  have hsum : (∑ j ∈ s, p j f) ≤ s.card * ε := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro j hj
    exact (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hε j f).2
      (hf j (Finset.le_sup (f := id) hj))
  calc
    ‖T f‖ ≤ (C : ℝ) * (∑ j ∈ s, p j f) := by
      have hSum : (∑ j ∈ s, p j) f = ∑ j ∈ s, p j f := by
        change (FunLike.coeAddMonoidHom _ _ _ (∑ j ∈ s, p j)) f = _
        rw [map_sum, Finset.sum_apply]
        rfl
      have h := hTC f
      change ‖T f‖ ≤ (C : ℝ) * (∑ j ∈ s, p j) f at h
      rwa [hSum] at h
    _ ≤ (C : ℝ) * (s.card * ε) := mul_le_mul_of_nonneg_left hsum C.coe_nonneg
    _ ≤ D * ε := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hε

/-- The derivative slots of a smooth test function at the origin. -/
def compactTestJet (K : Compacts E) (m : ℕ) :
    𝓓_{K}(E, ℝ) →ₗ[ℝ] (∀ j : Fin (m + 1), E [×(j : ℕ)]→L[ℝ] ℝ) where
  toFun f j := iteratedFDeriv ℝ j f 0
  map_add' f g := by
    funext j
    exact iteratedFDeriv_add_apply (f := (f : E → ℝ)) (g := (g : E → ℝ))
      (f.contDiff.contDiffAt.of_le (by simp)) (g.contDiff.contDiffAt.of_le (by simp))
  map_smul' c f := by
    funext j
    exact iteratedFDeriv_const_smul_apply (a := c) (f := (f : E → ℝ))
      (f.contDiff.contDiffAt.of_le (by simp))

end NormedSpace

variable [InnerProductSpace ℝ E] [ProperSpace E]

/-- A point-supported continuous functional kills any test whose finite jet
through its order vanishes. The point-support hypothesis is stated in germ
form on a compact neighborhood of the origin. -/
theorem exists_compactTest_order_of_point_support (T : 𝓓_{K}(E, ℝ) →L[ℝ] ℝ)
    (hK : (K : Set E) ∈ 𝓝 0)
    (hT : ∀ f : 𝓓_{K}(E, ℝ), (f : E → ℝ) =ᶠ[𝓝 0] 0 → T f = 0) :
    ∃ m : ℕ, (compactTestJet K m).ker ≤ T.toLinearMap.ker := by
  obtain ⟨m, C, hC, hBound⟩ := exists_compactTest_finiteOrder T
  obtain ⟨R, hR, hRK⟩ := Metric.mem_nhds_iff.mp hK
  refine ⟨m, fun f hf => LinearMap.mem_ker.mpr ?_⟩
  have hzero (j : ℕ) (hj : j ≤ m) : iteratedFDeriv ℝ j f 0 = 0 :=
    congrFun (LinearMap.mem_ker.mp hf) (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (m + 1))
  have hsmall (ε : ℝ) (hε : 0 < ε) : ‖T f‖ ≤ C * ε := by
    obtain ⟨g, hg, hsupp, heq, hsmall⟩ := exists_small_cutoff_of_flatJet
      f.contDiff m hzero (show 0 < R / 2 by positivity) hε
    have hsub : tsupport g ⊆ K := hsupp.trans
      ((closedBall_subset_ball (show R / 2 < R by linarith)).trans hRK)
    let gK : 𝓓_{K}(E, ℝ) := ⟨g, hg, fun x hx => by
      change g x = 0
      exact image_eq_zero_of_notMem_tsupport (fun hgx => hx (hsub hgx))⟩
    have hgerm : ((f - gK : 𝓓_{K}(E, ℝ)) : E → ℝ) =ᶠ[𝓝 0] 0 := by
      filter_upwards [heq] with x hx
      change f x - g x = 0
      exact sub_eq_zero.mpr hx.symm
    have hfg : T f = T gK := sub_eq_zero.mp ((map_sub T f gK).symm.trans (hT _ hgerm))
    rw [hfg]
    exact hBound gK ε hε.le (fun j hj x _ => hsmall j hj x)
  by_contra hne
  have hpos : 0 < ‖T f‖ := norm_pos_iff.mpr hne
  have h := hsmall (‖T f‖ / (C * 2)) (div_pos hpos (by positivity))
  rw [← div_div, ← mul_div_assoc, mul_div_cancel₀ _ hC.ne'] at h
  linarith

/-- On tests supported in any fixed compact neighborhood, a distribution
supported at the origin is a linear combination of the slots of a finite jet. -/
theorem exists_compactTest_jet_representation (T : 𝓓_{K}(E, ℝ) →L[ℝ] ℝ)
    (hK : (K : Set E) ∈ 𝓝 0)
    (hT : ∀ f : 𝓓_{K}(E, ℝ), (f : E → ℝ) =ᶠ[𝓝 0] 0 → T f = 0) :
    ∃ (m : ℕ) (A : (∀ j : Fin (m + 1), E [×(j : ℕ)]→L[ℝ] ℝ) →ₗ[ℝ] ℝ),
      T.toLinearMap = A.comp (compactTestJet K m) := by
  obtain ⟨m, hm⟩ := exists_compactTest_order_of_point_support T hK hT
  let J := compactTestJet K m
  let B := (J.ker.liftQ T.toLinearMap hm).comp J.quotKerEquivRange.symm.toLinearMap
  obtain ⟨A, hA⟩ := B.exists_extend
  refine ⟨m, A, ?_⟩
  ext f
  change T f = A (J f)
  rw [show A (J f) = B ⟨J f, LinearMap.mem_range_self J f⟩ from
    DFunLike.congr_fun hA ⟨J f, LinearMap.mem_range_self J f⟩]
  change T f = (J.ker.liftQ T.toLinearMap hm) (J.quotKerEquivRange.symm ⟨J f, _⟩)
  rw [J.quotKerEquivRange_symm_apply_image]
  change T f = (J.ker.liftQ T.toLinearMap hm) (Submodule.Quotient.mk f)
  exact (Submodule.liftQ_apply _ _ _).symm

end CalderonPatch
