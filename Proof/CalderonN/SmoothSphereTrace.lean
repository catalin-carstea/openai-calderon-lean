module

public import Proof.CalderonN.FiniteConormalResponseLinear
public import Proof.CalderonN.SmoothBoundaryMultiplier

import Mathlib.Tactic

/-! The smooth sphere core consists of actual traces of smooth ambient
functions. Operations that depend only on the trace descend to this core. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothSphereRestrictionL (dim : ℕ) :
    smoothBallDataSubmodule dim →ₗ[ℝ] (↥(standardSphere dim) → ℝ) where
  toFun u z := u.1 z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev SmoothSphereTrace (dim : ℕ) := (smoothSphereRestrictionL dim).range

@[expose] def smoothSphereTraceL (dim : ℕ) :
    smoothBallDataSubmodule dim →ₗ[ℝ] SmoothSphereTrace dim :=
  (smoothSphereRestrictionL dim).rangeRestrict

theorem smoothSphereTraceL_surjective : Function.Surjective (smoothSphereTraceL dim) := by
  intro u
  obtain ⟨v,hv⟩ := u.2
  exact ⟨v,Subtype.ext hv⟩

theorem smoothSphereTraceL_apply (u : smoothBallDataSubmodule dim) (z : ↥(standardSphere dim)) :
    (smoothSphereTraceL dim u).1 z = u.1 z := rfl

@[expose] def smoothSphereTrace (u : SmoothData dim) : SmoothSphereTrace dim :=
  smoothSphereTraceL dim ⟨u.1,u.2⟩

theorem smoothSphereTrace_apply (u : SmoothData dim) (z : ↥(standardSphere dim)) :
    (smoothSphereTrace u).1 z = u.1 z := rfl

theorem smoothSphereTrace_eq_iff (u v : SmoothData dim) :
    smoothSphereTrace u = smoothSphereTrace v ↔ EqOn u.1 v.1 (standardSphere dim) := by
  constructor
  · intro h z hz
    exact congrArg (fun x : SmoothSphereTrace dim => x.1 ⟨z,hz⟩) h
  · intro h
    apply Subtype.ext
    exact funext fun z => h z.2

@[expose] def smoothSphereTraceLift {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : smoothBallDataSubmodule dim →ₗ[ℝ] V)
    (hL : ∀ u v, EqOn u.1 v.1 (standardSphere dim) → L u = L v) :
    SmoothSphereTrace dim →ₗ[ℝ] V :=
  (smoothSphereTraceL dim).liftOfSurjective smoothSphereTraceL_surjective
    ⟨L,fun u hu => LinearMap.mem_ker.mpr (by
      rw [← L.map_zero]
      apply hL
      intro z hz
      exact congrArg (fun x : SmoothSphereTrace dim => x.1 ⟨z,hz⟩) (LinearMap.mem_ker.mp hu))⟩

theorem smoothSphereTraceLift_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : smoothBallDataSubmodule dim →ₗ[ℝ] V)
    (hL : ∀ u v, EqOn u.1 v.1 (standardSphere dim) → L u = L v)
    (u : smoothBallDataSubmodule dim) :
    smoothSphereTraceLift L hL (smoothSphereTraceL dim u) = L u := by
  unfold smoothSphereTraceLift
  exact LinearMap.equivOfSurjective_apply _ _

@[expose] def smoothSphereTraceMap
    (L : smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim)
    (hL : ∀ u v, EqOn u.1 v.1 (standardSphere dim) → EqOn (L u).1 (L v).1 (standardSphere dim)) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceLift ((smoothSphereTraceL dim).comp L)
    (fun u v h => by
      change smoothSphereTraceL dim (L u) = smoothSphereTraceL dim (L v)
      apply Subtype.ext
      exact funext fun z => hL u v h z.2)

theorem smoothSphereTraceMap_apply
    (L : smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim)
    (hL : ∀ u v, EqOn u.1 v.1 (standardSphere dim) → EqOn (L u).1 (L v).1 (standardSphere dim))
    (u : smoothBallDataSubmodule dim) :
    smoothSphereTraceMap L hL (smoothSphereTraceL dim u) = smoothSphereTraceL dim (L u) := by
  unfold smoothSphereTraceMap
  rw [smoothSphereTraceLift_apply,LinearMap.comp_apply]

@[expose] def smoothSphereTraceMul (m : SmoothData dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceMap (smoothBallDataMulL m) (smoothBallDataMulL_congr m)

theorem smoothSphereTraceMul_apply (m : SmoothData dim) (u : SmoothSphereTrace dim)
    (z : ↥(standardSphere dim)) :
    (smoothSphereTraceMul m u).1 z = m.1 z*u.1 z := by
  obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective u
  rw [smoothSphereTraceMul,smoothSphereTraceMap_apply,smoothSphereTraceL_apply,
    smoothBallDataMulL_apply]
  rfl

@[expose] def smoothSphereTraceRotation (i j : Fin dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceMap (smoothBallAngularDataL i j) (smoothBallAngularDataL_congr i j)

theorem smoothSphereTraceRotation_apply (i j : Fin dim) (u : SmoothData dim) :
    smoothSphereTraceRotation i j (smoothSphereTrace u) =
      smoothSphereTrace ⟨OAI.AnisotropicCalderon.SmoothSphereRotation.sphereRotationDerivative i j u.1,
        contDiff_sphereRotationDerivative i j u.1 u.2⟩ := by
  unfold smoothSphereTraceRotation smoothSphereTrace
  rw [smoothSphereTraceMap_apply]
  rfl

@[expose] def smoothSphereTraceSobolev (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2) :
    SmoothSphereTrace dim →ₗ[ℝ] SphereSobolev dim s :=
  smoothSphereTraceLift (smoothBoundarySobolevLinear hn s hs) (fun u v h => by
    rw [smoothBoundarySobolevLinear_apply,smoothBoundarySobolevLinear_apply]
    exact smoothBoundarySobolev_eq_of_eqOn hn s hs ⟨u.1,smoothBallData_contDiff u⟩
      ⟨v.1,smoothBallData_contDiff v⟩ h)

theorem smoothSphereTraceSobolev_apply (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2) (u : SmoothData dim) :
    smoothSphereTraceSobolev hn s hs (smoothSphereTrace u) = smoothBoundarySobolev hn s hs u := by
  unfold smoothSphereTraceSobolev smoothSphereTrace
  rw [smoothSphereTraceLift_apply,smoothBoundarySobolevLinear_apply]

@[expose] def smoothSphereTraceL2 (hn : 3 ≤ dim) : SmoothSphereTrace dim →ₗ[ℝ] SphereL2 dim :=
  smoothSphereTraceLift (smoothBoundaryLiftL hn) (fun u v h => by
    rw [smoothBoundaryLiftL_apply,smoothBoundaryLiftL_apply]
    exact smoothSphereLift_eq_of_eqOn ⟨u.1,smoothBallData_contDiff u⟩ ⟨v.1,smoothBallData_contDiff v⟩ h)

theorem smoothSphereTraceL2_apply (hn : 3 ≤ dim) (u : SmoothData dim) :
    smoothSphereTraceL2 hn (smoothSphereTrace u) = smoothSphereLift u.1 u.2 := by
  unfold smoothSphereTraceL2 smoothSphereTrace
  rw [smoothSphereTraceLift_apply,smoothBoundaryLiftL_apply]

end CalderonN
