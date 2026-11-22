module

public import Proof.CalderonN.FlatTraceRaisingIdentities
public import Proof.CalderonN.HarmonicRaisingRotation

import Mathlib.Tactic

/-! Covariance of raising and lowering under rotations, transferred
from the released harmonic block calculation to the actual smooth domain. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable (hn : 3 ≤ dim) {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

include hn in
theorem smoothTraceLowering_rotation_comm (i j a : I dim) :
    let B := smoothTraceFlatDegree hA hEll S
    let K := smoothSphereTraceRotation i j
    let L := smoothTraceLowering B
    K*L a-L a*K = (if a=j then L i else 0)-(if a=i then L j else 0) := by
  classical
  dsimp only
  let B := smoothTraceFlatDegree hA hEll S
  let K := smoothSphereTraceRotation i j
  let L := smoothTraceLowering B
  let R := smoothTraceRaising B
  have hK : SmoothTraceAdjoint hn K (-K) := smoothTraceRotation_skew hn i j
  have hL (b : I dim) : SmoothTraceAdjoint hn (L b) (R b) :=
    (smoothTraceRaising_adjoint hn B (smoothTraceFlatDegree_symmetric hn hA hEll S) b).symm
  have hZero : SmoothTraceAdjoint hn (0 : Module.End ℝ (SmoothSphereTrace dim)) 0 := by
    intro x y
    simp only [LinearMap.zero_apply,map_zero,inner_zero_left,inner_zero_right]
  have hCond (p : Prop) [Decidable p] (b : I dim) :
      SmoothTraceAdjoint hn (if p then L b else 0) (if p then R b else 0) := by
    split <;> first | exact hL b | exact hZero
  apply SmoothTraceAdjoint.eq_of_finite ((hK.mul (hL a)).sub ((hL a).mul hK))
    ((hCond (a=j) i).sub (hCond (a=i) j))
  have hEq : (K*L a-L a*K).comp finiteHarmonicSmoothTraceL =
      ((if a=j then L i else 0)-(if a=i then L j else 0)).comp finiteHarmonicSmoothTraceL := by
    ext k v : 2
    change K (L a (smoothHarmonicSingle k v))-L a (K (smoothHarmonicSingle k v)) =
      (if a=j then L i else 0) (smoothHarmonicSingle k v)-(if a=i then L j else 0) (smoothHarmonicSingle k v)
    cases k with
    | zero =>
      simp only [L,B,K,smoothTraceLowering_harmonicSingle_zero hn hA hEll S,
        smoothTraceRotation_harmonicSingle,map_zero,sub_self]
      split <;> split <;> simp only [smoothTraceLowering_harmonicSingle_zero hn hA hEll S,LinearMap.zero_apply,sub_zero]
    | succ k =>
      simp only [L,B,K,smoothTraceLowering_harmonicSingle_succ hn hA hEll S,smoothTraceRotation_harmonicSingle,
        ← map_sub]
      have h := congrArg (smoothHarmonicSingle k) (harmonicSphereRotation_derivative_commutator (sphereFischerInner dim) k i j a v)
      split_ifs at h ⊢ <;>
        simpa only [LinearMap.zero_apply,map_zero,map_sub,
          smoothTraceLowering_harmonicSingle_succ hn hA hEll S] using h
  exact fun f => congrArg (fun T : HarmonicFiniteCoefficients dim →ₗ[ℝ] SmoothSphereTrace dim => T f) hEq

include hn in
theorem smoothTraceRaising_rotation_comm (i j a : I dim) :
    let B := smoothTraceFlatDegree hA hEll S
    let K := smoothSphereTraceRotation i j
    let R := smoothTraceRaising B
    K*R a-R a*K = (if a=j then R i else 0)-(if a=i then R j else 0) := by
  classical
  dsimp only
  let B := smoothTraceFlatDegree hA hEll S
  let K := smoothSphereTraceRotation i j
  let L := smoothTraceLowering B
  let R := smoothTraceRaising B
  have hK : SmoothTraceAdjoint hn K (-K) := smoothTraceRotation_skew hn i j
  have hR (b : I dim) : SmoothTraceAdjoint hn (R b) (L b) :=
    smoothTraceRaising_adjoint hn B (smoothTraceFlatDegree_symmetric hn hA hEll S) b
  have hZero : SmoothTraceAdjoint hn (0 : Module.End ℝ (SmoothSphereTrace dim)) 0 := by
    intro x y
    simp only [LinearMap.zero_apply,map_zero,inner_zero_left,inner_zero_right]
  have hCond (p : Prop) [Decidable p] (b : I dim) :
      SmoothTraceAdjoint hn (if p then R b else 0) (if p then L b else 0) := by
    split <;> first | exact hR b | exact hZero
  have hAdj := (hK.mul (hR a)).sub ((hR a).mul hK)
  have hSimpl : L a*(-K)-(-K)*L a = K*L a-L a*K := by
    simp only [mul_neg,neg_mul,neg_sub_neg]
  have hRev : K*L a-L a*K = (if a=j then L i else 0)-(if a=i then L j else 0) :=
    smoothTraceLowering_rotation_comm hn hA hEll S i j a
  rw [hSimpl,hRev] at hAdj
  have hAdj' := (hCond (a=j) i).sub (hCond (a=i) j)
  let U := K*R a-R a*K
  let V := (if a=j then R i else 0)-(if a=i then R j else 0)
  change U = V
  ext u : 1
  apply smoothSphereTraceL2_injective hn
  let d := U u-V u
  have h := (hAdj u d).trans (hAdj' u d).symm
  change ⟪smoothSphereTraceL2 hn (U u),smoothSphereTraceL2 hn d⟫_ℝ =
    ⟪smoothSphereTraceL2 hn (V u),smoothSphereTraceL2 hn d⟫_ℝ at h
  have hd : ⟪smoothSphereTraceL2 hn d,smoothSphereTraceL2 hn d⟫_ℝ = 0 := by
    rw [show smoothSphereTraceL2 hn d = smoothSphereTraceL2 hn (U u)-smoothSphereTraceL2 hn (V u) from map_sub _ _ _,
      inner_sub_left,sub_eq_zero]
    simpa only [d,map_sub] using h
  exact sub_eq_zero.mp (by rw [← map_sub]; exact inner_self_eq_zero.mp hd)

end CalderonN
