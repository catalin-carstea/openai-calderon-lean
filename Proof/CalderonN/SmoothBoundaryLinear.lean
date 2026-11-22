module

public import Proof.CalderonN.SmoothBoundarySobolev

import Mathlib.Tactic

/-! Boundary weights on a single linear space of ambient smooth data. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SphereHarmonic

variable {dim : ℕ} [NeZero dim]

theorem smoothSphereLift_eq_of_eqOn (u v : SmoothData dim)
    (h : EqOn u.1 v.1 (standardSphere dim)) :
    smoothSphereLift u.1 u.2 = smoothSphereLift v.1 v.2 := by
  unfold smoothSphereLift
  congr 1
  apply ContinuousMap.ext
  intro w
  exact h w.2

theorem smoothBoundarySobolev_eq_of_eqOn (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (u v : SmoothData dim) (h : EqOn u.1 v.1 (standardSphere dim)) :
    smoothBoundarySobolev hn s hs u = smoothBoundarySobolev hn s hs v := by
  apply lp.ext
  funext k
  rw [smoothBoundarySobolev_apply,smoothBoundarySobolev_apply,smoothSphereLift_eq_of_eqOn u v h]

private theorem smoothSphereLift_smul (c : ℝ) (u : SmoothData dim) :
    smoothSphereLift (c • u.1) (u.2.const_smul c) = c • smoothSphereLift u.1 u.2 := by
  unfold smoothSphereLift
  rw [← map_smul]
  congr 1

@[expose] def smoothBoundarySobolevLinear (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2) :
    smoothBallDataSubmodule dim →ₗ[ℝ] SphereSobolev dim s where
  toFun u := smoothBoundarySobolev hn s hs ⟨u.1,smoothBallData_contDiff u⟩
  map_add' u v := by
    apply lp.ext
    funext k
    change smoothBoundarySobolev hn s hs ⟨(u+v).1,smoothBallData_contDiff (u+v)⟩ k =
      (smoothBoundarySobolev hn s hs ⟨u.1,smoothBallData_contDiff u⟩ +
        smoothBoundarySobolev hn s hs ⟨v.1,smoothBallData_contDiff v⟩) k
    rw [lp.coeFn_add,Pi.add_apply]
    simp only [smoothBoundarySobolev_apply]
    have h := smoothSphereLift_add u.1 v.1 (smoothBallData_contDiff u) (smoothBallData_contDiff v)
    change smoothSphereLift (u+v).1 (smoothBallData_contDiff (u+v)) = _ at h
    rw [h,map_add,smul_add]
  map_smul' c u := by
    apply lp.ext
    funext k
    change smoothBoundarySobolev hn s hs ⟨(c • u).1,smoothBallData_contDiff (c • u)⟩ k =
      (c • smoothBoundarySobolev hn s hs ⟨u.1,smoothBallData_contDiff u⟩) k
    rw [lp.coeFn_smul,Pi.smul_apply]
    simp only [smoothBoundarySobolev_apply]
    have h := smoothSphereLift_smul c (⟨u.1,smoothBallData_contDiff u⟩ : SmoothData dim)
    change smoothSphereLift (c • u).1 (smoothBallData_contDiff (c • u)) = _ at h
    rw [h,map_smul,smul_comm]

theorem smoothBoundarySobolevLinear_apply (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (u : smoothBallDataSubmodule dim) :
    smoothBoundarySobolevLinear hn s hs u =
      smoothBoundarySobolev hn s hs ⟨u.1,smoothBallData_contDiff u⟩ := by
  unfold smoothBoundarySobolevLinear
  rfl

end CalderonN
