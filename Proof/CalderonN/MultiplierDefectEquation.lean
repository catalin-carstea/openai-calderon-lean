module

public import Proof.CalderonN.SmoothConormalTaylorSolutions

import Mathlib.Tactic

/-! Exact source terms for the fixed-ball multiplication defect and its
first variation. Every defect has zero boundary trace. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothMultiplierDefect (m u v : SmoothData dim) : SmoothData dim :=
  ⟨fun z => v.1 z-m.1 z*u.1 z,v.2.sub (m.2.mul u.2)⟩

theorem smoothMultiplierDefect_on_boundary (m u v f : SmoothData dim)
    (hu : EqOn u.1 f.1 (standardSphere dim))
    (hv : EqOn v.1 (fun z => m.1 z*f.1 z) (standardSphere dim)) :
    EqOn (smoothMultiplierDefect m u v).1 0 (standardSphere dim) := by
  intro z hz
  change v.1 z-m.1 z*u.1 z = 0
  rw [hu hz,show v.1 z = m.1 z*f.1 z from hv hz,sub_self]

theorem smoothMultiplierDefect_divergence
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (m u v : SmoothData dim) (z : X dim) (hSym : ∀ i j,A z i j = A z j i) :
    negativeBallDivergence A (smoothMultiplierDefect m u v).1 z =
      negativeBallDivergence A v.1 z-m.1 z*negativeBallDivergence A u.1 z-
        greenSourceCutoffError A m.1 u.1 z := by
  let w : SmoothData dim := ⟨fun z => m.1 z*u.1 z,m.2.mul u.2⟩
  change negativeBallDivergence A (v.1-w.1) z = _
  rw [negativeBallDivergence_sub_solution hA v w]
  change negativeBallDivergence A v.1 z-negativeBallDivergence A (fun x => m.1 x*u.1 x) z = _
  rw [negativeBallDivergence_mul_eq_at_symm hA m.2 u.2 z hSym]
  ring

theorem conormalTaylorSolutions_multiplierDefects
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ z ∈ ball (0 : X dim) 1, ∀ i j,A z i j = A z j i)
    {ell : X dim →L[ℝ] ℝ} {f : SmoothData dim}
    (m : SmoothData dim)
    (U : ConormalTaylorSolutions A ell f)
    (V : ConormalTaylorSolutions A ell ⟨fun z => m.1 z*f.1 z,m.2.mul f.2⟩) :
    let A₀ : X dim → Mat dim := fun _ => 1
    let A₁ : X dim → Mat dim := fun z => ell z • 1
    let w := smoothMultiplierDefect m U.actual V.actual
    let w₀ := smoothMultiplierDefect m U.flat V.flat
    let w₁ := smoothMultiplierDefect m U.first V.first
    EqOn w.1 0 (standardSphere dim) ∧ EqOn w₀.1 0 (standardSphere dim) ∧
    EqOn w₁.1 0 (standardSphere dim) ∧
    EqOn (negativeBallDivergence A w.1)
      (fun z => -greenSourceCutoffError A m.1 U.actual.1 z) (ball (0 : X dim) 1) ∧
    EqOn (negativeBallDivergence A₀ w₀.1)
      (fun z => -greenSourceCutoffError A₀ m.1 U.flat.1 z) (ball (0 : X dim) 1) ∧
    EqOn (negativeBallDivergence A₀ w₁.1)
      (fun z => -negativeBallDivergence A₁ w₀.1 z-greenSourceCutoffError A₁ m.1 U.flat.1 z -
        greenSourceCutoffError A₀ m.1 U.first.1 z) (ball (0 : X dim) 1) := by
  dsimp only
  let A₀ : X dim → Mat dim := fun _ => 1
  let A₁ : X dim → Mat dim := fun z => ell z • 1
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hA₁ : ContDiff ℝ ∞ A₁ := ell.contDiff.smul contDiff_const
  have hSym₀ (i j : Fin dim) (z : X dim) : A₀ z i j = A₀ z j i := Matrix.isSymm_one.apply j i
  have hSym₁ (i j : Fin dim) (z : X dim) : A₁ z i j = A₁ z j i :=
    (Matrix.isSymm_one.smul (ell z)).apply j i
  refine ⟨smoothMultiplierDefect_on_boundary m U.actual V.actual f U.actualTrace V.actualTrace,
    smoothMultiplierDefect_on_boundary m U.flat V.flat f U.flatTrace V.flatTrace,?_,?_,?_,?_⟩
  · intro z hz
    change V.first.1 z-m.1 z*U.first.1 z = 0
    rw [show V.first.1 z = 0 from V.firstTrace hz,show U.first.1 z = 0 from U.firstTrace hz,mul_zero,sub_self]
  · intro z hz
    change negativeBallDivergence A (smoothMultiplierDefect m U.actual V.actual).1 z =
      -greenSourceCutoffError A m.1 U.actual.1 z
    rw [smoothMultiplierDefect_divergence hA m _ _ z (hSym z hz),show negativeBallDivergence A V.actual.1 z = 0 from V.actualEquation hz,
      show negativeBallDivergence A U.actual.1 z = 0 from U.actualEquation hz,mul_zero,sub_zero,zero_sub]
  · intro z hz
    change negativeBallDivergence A₀ (smoothMultiplierDefect m U.flat V.flat).1 z =
      -greenSourceCutoffError A₀ m.1 U.flat.1 z
    rw [smoothMultiplierDefect_divergence hA₀ m _ _ z (fun i j => hSym₀ i j z),
      show negativeBallDivergence A₀ V.flat.1 z = 0 from V.flatEquation hz,
      show negativeBallDivergence A₀ U.flat.1 z = 0 from U.flatEquation hz,mul_zero,sub_zero,zero_sub]
  · intro z hz
    change negativeBallDivergence A₀ (smoothMultiplierDefect m U.first V.first).1 z =
      -negativeBallDivergence A₁ (smoothMultiplierDefect m U.flat V.flat).1 z -
        greenSourceCutoffError A₁ m.1 U.flat.1 z-greenSourceCutoffError A₀ m.1 U.first.1 z
    have hU : negativeBallDivergence A₀ U.first.1 z =
      -negativeBallDivergence A₁ U.flat.1 z := U.firstEquation hz
    have hV : negativeBallDivergence A₀ V.first.1 z =
      -negativeBallDivergence A₁ V.flat.1 z := V.firstEquation hz
    rw [smoothMultiplierDefect_divergence hA₀ m _ _ z (fun i j => hSym₀ i j z),smoothMultiplierDefect_divergence hA₁ m _ _ z (fun i j => hSym₁ i j z),hU,hV]
    ring

end CalderonN
