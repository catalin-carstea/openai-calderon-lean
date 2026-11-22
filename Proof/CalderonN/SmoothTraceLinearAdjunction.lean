module

public import Proof.CalderonN.SmoothConormalTraceOperators
public import Proof.CalderonN.SmoothPairingCompletion

import Proof.CalderonN.SmoothConormalTaylorSymmetry
import Mathlib.Tactic

/-! Adjoint relations on the smooth trace core allow finite harmonic
bounds to be transferred without choosing a topology for smooth data. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def SmoothTraceAdjoint (hn : 3 ≤ dim) (T S : Module.End ℝ (SmoothSphereTrace dim)) : Prop :=
  ∀ u v, ⟪smoothSphereTraceL2 hn (T u),smoothSphereTraceL2 hn v⟫_ℝ =
    ⟪smoothSphereTraceL2 hn u,smoothSphereTraceL2 hn (S v)⟫_ℝ

theorem smoothTraceRotation_skew (hn : 3 ≤ dim) (i j : Fin dim) :
    SmoothTraceAdjoint hn (smoothSphereTraceRotation i j) (-smoothSphereTraceRotation i j) := by
  intro x y
  obtain ⟨u,rfl⟩ := smoothSphereTraceL_surjective x
  obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective y
  let U : SmoothData dim := ⟨u.1,smoothBallData_contDiff u⟩
  let V : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  let K := smoothSphereTraceRotation i j
  change ⟪smoothSphereTraceL2 hn (K (smoothSphereTrace U)),smoothSphereTraceL2 hn (smoothSphereTrace V)⟫_ℝ =
    ⟪smoothSphereTraceL2 hn (smoothSphereTrace U),smoothSphereTraceL2 hn (-(K (smoothSphereTrace V)))⟫_ℝ
  rw [map_neg,inner_neg_right]
  dsimp only [K]
  rw [smoothSphereTraceRotation_apply,smoothSphereTraceRotation_apply]
  simp only [smoothSphereTraceL2_apply]
  exact inner_sphereRotationDerivative_skew i j U.1 V.1 U.2 V.2

theorem SmoothTraceAdjoint.rotation_commutator_symmetric (hn : 3 ≤ dim)
    (i j : Fin dim) (T : Module.End ℝ (SmoothSphereTrace dim)) (hT : SmoothTraceAdjoint hn T T) :
    let K := smoothSphereTraceRotation i j
    SmoothTraceAdjoint hn (K*T-T*K) (K*T-T*K) := by
  dsimp only
  intro u v
  let K := smoothSphereTraceRotation i j
  let L := smoothSphereTraceL2 (dim:=dim) hn
  have hK (x y : SmoothSphereTrace dim) : ⟪L (K x),L y⟫_ℝ = -⟪L x,L (K y)⟫_ℝ := by
    simpa only [LinearMap.neg_apply,map_neg,inner_neg_right] using smoothTraceRotation_skew hn i j x y
  change ⟪L (K (T u)-T (K u)),L v⟫_ℝ = ⟪L u,L (K (T v)-T (K v))⟫_ℝ
  simp only [map_sub,inner_sub_left,inner_sub_right]
  have hT' : ∀ x y : SmoothSphereTrace dim, ⟪L (T x),L y⟫_ℝ = ⟪L x,L (T y)⟫_ℝ := hT
  rw [hK (T u) v,hT' u (K v),hT' (K u) v,hK u (T v)]
  ring

theorem smoothSphereTrace_remainder_symmetric (hn : 3 ≤ dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    (hSym : ∀ z ∈ ball (0 : X dim) 1,(A z).IsSymm)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (W : SmoothData dim)
    (hW : ∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim))
    (r : ℝ) :
    let R := smoothSphereTaylorResponses hA hEll S
    let A' := (LinearMap.fst ℝ _ _).comp R
    let B := (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
    let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
    let T := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
    SmoothTraceAdjoint hn T T := by
  dsimp only
  intro x y
  obtain ⟨u,rfl⟩ := smoothSphereTraceL_surjective x
  obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective y
  let U : SmoothData dim := ⟨u.1,smoothBallData_contDiff u⟩
  let V : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  let R := smoothSphereTaylorResponses hA hEll S
  let A' := (LinearMap.fst ℝ _ _).comp R
  let B := (LinearMap.fst ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let T := smoothSphereTraceMul W*A'-B-r • (smoothSphereTraceMul ⟨ell,ell.contDiff⟩*B+Q)
  have hT (p : SmoothData dim) :
      T (smoothSphereTrace p) = smoothSphereTrace ((S p).remainder hA r) :=
    (smoothSphereTaylorResponse_remainder hA hEll S W hW r p).symm
  change ⟪smoothSphereTraceL2 hn (T (smoothSphereTrace U)),smoothSphereTraceL2 hn (smoothSphereTrace V)⟫_ℝ =
    ⟪smoothSphereTraceL2 hn (smoothSphereTrace U),smoothSphereTraceL2 hn (T (smoothSphereTrace V))⟫_ℝ
  simp only [hT,smoothSphereTraceL2_apply]
  exact conormalTaylorSolutions_remainder_symmetric hn hA hSym (S U) (S V) r

end CalderonN
