module

public import Proof.CalderonN.FlatTraceRaisingIdentities

import Mathlib.Tactic

/-! The solid-harmonic blocks of raising and lowering on arbitrary
smooth traces, obtained from the genuine adjunction. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable (hn : 3 ≤ dim) {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

theorem harmonicProjection_smoothTraceRaising_zero (i : Fin dim) (u : SmoothSphereTrace dim) :
    harmonicProjection 0 (smoothSphereTraceL2 hn (smoothTraceRaising (smoothTraceFlatDegree hA hEll S) i u)) = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_zero_left,harmonicProjection_inner,← smoothSphereTraceL2_harmonicSingle hn 0 v]
  rw [smoothTraceRaising_adjoint hn _ (smoothTraceFlatDegree_symmetric hn hA hEll S) i,
    smoothTraceLowering_harmonicSingle_zero hn hA hEll S,map_zero,inner_zero_right]

theorem harmonicProjection_smoothTraceRaising_succ (i : Fin dim) (k : ℕ) (u : SmoothSphereTrace dim) :
    harmonicProjection (k+1) (smoothSphereTraceL2 hn (smoothTraceRaising (smoothTraceFlatDegree hA hEll S) i u)) =
      harmonicDerivativeAdjoint (sphereFischerInner dim) k i (harmonicProjection k (smoothSphereTraceL2 hn u)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_harmonicDerivativeAdjoint,harmonicProjection_inner,harmonicProjection_inner,
    ← smoothSphereTraceL2_harmonicSingle hn (k+1) v]
  rw [smoothTraceRaising_adjoint hn _ (smoothTraceFlatDegree_symmetric hn hA hEll S) i,
    smoothTraceLowering_harmonicSingle_succ hn hA hEll S,smoothSphereTraceL2_harmonicSingle]

theorem harmonicProjection_smoothTraceLowering (i : Fin dim) (k : ℕ) (u : SmoothSphereTrace dim) :
    harmonicProjection k (smoothSphereTraceL2 hn (smoothTraceLowering (smoothTraceFlatDegree hA hEll S) i u)) =
      harmonicDerivative (sphereFischerInner dim) k i (harmonicProjection (k+1) (smoothSphereTraceL2 hn u)) := by
  apply ext_inner_right ℝ
  intro v
  let w := harmonicProjection (k+1) (smoothSphereTraceL2 hn u)
  have hAdj' :
      ⟪harmonicDerivative (sphereFischerInner dim) k i w,v⟫_ℝ =
        ⟪w,harmonicDerivativeAdjoint (sphereFischerInner dim) k i v⟫_ℝ :=
    (real_inner_comm _ _).trans ((inner_harmonicDerivativeAdjoint (sphereFischerInner dim) k i v w).symm.trans
      (real_inner_comm _ _))
  dsimp only [w] at hAdj'
  rw [hAdj',harmonicProjection_inner,harmonicProjection_inner,
    ← smoothSphereTraceL2_harmonicSingle hn k v]
  rw [(smoothTraceRaising_adjoint hn _ (smoothTraceFlatDegree_symmetric hn hA hEll S) i).symm,
    smoothTraceRaising_harmonicSingle hn hA hEll S,smoothSphereTraceL2_harmonicSingle]

end CalderonN
