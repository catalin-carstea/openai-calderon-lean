module

public import Proof.CalderonN.SmoothFlatConormalResponse
public import Proof.CalderonN.AdmittedNormalPoissonEquation

import Proof.CalderonN.GreenSourceCutoff
import Mathlib.Tactic

/-! Common actual, flat and first-variation solutions for a smooth
boundary input, together with independence of their boundary outputs. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

structure ConormalTaylorSolutions (A : X dim → Mat dim) (ell : X dim →L[ℝ] ℝ)
    (f : SmoothData dim) where
  actual : SmoothData dim
  flat : SmoothData dim
  first : SmoothData dim
  actualTrace : EqOn actual.1 f.1 (standardSphere dim)
  actualEquation : EqOn (negativeBallDivergence A actual.1) 0 (ball (0 : X dim) 1)
  flatTrace : EqOn flat.1 f.1 (standardSphere dim)
  flatEquation : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) flat.1) 0 (ball (0 : X dim) 1)
  firstTrace : EqOn first.1 0 (standardSphere dim)
  firstEquation : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) first.1)
    (fun z => -negativeBallDivergence (fun w => ell w • (1 : Mat dim)) flat.1 z) (ball (0 : X dim) 1)

@[expose] def ConormalTaylorSolutions.degree {A : X dim → Mat dim} {ell : X dim →L[ℝ] ℝ}
    {f : SmoothData dim} (u : ConormalTaylorSolutions A ell f) : SmoothData dim :=
  smoothBallRadialDerivative u.flat

@[expose] def ConormalTaylorSolutions.affineConormal {A : X dim → Mat dim} {ell : X dim →L[ℝ] ℝ}
    {f : SmoothData dim} (u : ConormalTaylorSolutions A ell f) : SmoothData dim :=
  let v := smoothBallRadialDerivative u.first
  ⟨fun z => ell z*u.degree.1 z+v.1 z,(ell.contDiff.mul u.degree.2).add v.2⟩

@[expose] def ConormalTaylorSolutions.remainder {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {ell : X dim →L[ℝ] ℝ} {f : SmoothData dim} (u : ConormalTaylorSolutions A ell f) (r : ℝ) :
    SmoothData dim :=
  ⟨fun z => smoothBallConormal A u.actual.1 z-u.degree.1 z-r*u.affineConormal.1 z,
    ((contDiff_smoothBallConormal hA u.actual).sub u.degree.2).sub
      (contDiff_const.mul u.affineConormal.2)⟩

theorem exists_conormalTaylorSolutions_of_extension
    {A : X dim → Mat dim} (F F₀ : SmoothCoefficientMatrix dim 2)
    (hF₀ : ∀ z ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F₀ z = 1)
    (hFA : EqOn (coefficientMatrixField 2 F) A (ball (0 : X dim) 1))
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F) lo hi)
    (ell : X dim →L[ℝ] ℝ) (f : SmoothData dim) : Nonempty (ConormalTaylorSolutions A ell f) := by
  obtain ⟨b,hb,hbT,hbH,_⟩ := exists_native_classicalBallPoisson 0 F hEll f
  obtain ⟨u,q,huT,huH,hqT,hqH⟩ := exists_smooth_flat_response_and_variation F₀ hF₀ ell f
  refine ⟨⟨⟨b,hb⟩,u,q,hbT,?_,huT,huH,hqT,hqH⟩⟩
  intro z hz
  have hG : coefficientMatrixField 2 F =ᶠ[𝓝 z] A := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hFA hw
  rw [← negativeBallDivergence_congr_germ hG EventuallyEq.rfl]
  exact hbH hz

theorem conormalTaylorSolutions_agree_of_trace
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} {f g : SmoothData dim}
    (U : ConormalTaylorSolutions A ell f) (V : ConormalTaylorSolutions A ell g)
    (hfg : EqOn f.1 g.1 (standardSphere dim)) :
    EqOn U.actual.1 V.actual.1 (closedBall (0 : X dim) 1) ∧
    EqOn U.flat.1 V.flat.1 (closedBall (0 : X dim) 1) ∧
    EqOn U.first.1 V.first.1 (closedBall (0 : X dim) 1) := by
  have hEll₀ := uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))
  have hActual := eqOn_closedUnitBall_of_equal_ball_forcing hA hEll (fun _ _ => rfl) U.actual V.actual
    (fun z hz => (U.actualEquation hz).trans (V.actualEquation hz).symm)
    (U.actualTrace.trans (hfg.trans V.actualTrace.symm))
  have hFlat := eqOn_closedUnitBall_of_equal_ball_forcing contDiff_const hEll₀ (fun _ _ => rfl) U.flat V.flat
    (fun z hz => (U.flatEquation hz).trans (V.flatEquation hz).symm)
    (U.flatTrace.trans (hfg.trans V.flatTrace.symm))
  have hFirst := eqOn_closedUnitBall_of_equal_ball_forcing contDiff_const hEll₀ (fun _ _ => rfl) U.first V.first ?_
    (U.firstTrace.trans V.firstTrace.symm)
  · exact ⟨hActual,hFlat,hFirst⟩
  · intro z hz
    have hF : U.flat.1 =ᶠ[𝓝 z] V.flat.1 := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hFlat (ball_subset_closedBall hw)
    have hU : negativeBallDivergence (fun _ => (1 : Mat dim)) U.first.1 z =
      -negativeBallDivergence (fun w => ell w • (1 : Mat dim)) U.flat.1 z := U.firstEquation hz
    have hV : negativeBallDivergence (fun _ => (1 : Mat dim)) V.first.1 z =
      -negativeBallDivergence (fun w => ell w • (1 : Mat dim)) V.flat.1 z := V.firstEquation hz
    rw [hU,hV,negativeBallDivergence_congr_germ EventuallyEq.rfl hF]

theorem conormalTaylorSolutions_degree_eqOn
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} {f g : SmoothData dim}
    (U : ConormalTaylorSolutions A ell f) (V : ConormalTaylorSolutions A ell g)
    (hfg : EqOn f.1 g.1 (standardSphere dim)) : EqOn U.degree.1 V.degree.1 (standardSphere dim) :=
  eqOn_radialDerivative_of_eqOn_closedUnitBall (conormalTaylorSolutions_agree_of_trace hA hEll U V hfg).2.1

theorem conormalTaylorSolutions_remainder_eqOn
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} {f g : SmoothData dim}
    (U : ConormalTaylorSolutions A ell f) (V : ConormalTaylorSolutions A ell g)
    (hfg : EqOn f.1 g.1 (standardSphere dim)) (r : ℝ) :
    EqOn (U.remainder hA r).1 (V.remainder hA r).1 (standardSphere dim) := by
  obtain ⟨hb,hu,hq⟩ := conormalTaylorSolutions_agree_of_trace hA hEll U V hfg
  have hb' := eqOn_fderiv_closedUnitBall U.actual.2 V.actual.2 hb
  have hu' := eqOn_radialDerivative_of_eqOn_closedUnitBall hu
  have hq' := eqOn_radialDerivative_of_eqOn_closedUnitBall hq
  intro z hz
  have hF : smoothBallFlux A U.actual.1 z = smoothBallFlux A V.actual.1 z := by
    ext i
    simp only [smoothBallFlux_apply,coordDeriv,hb' (sphere_subset_closedBall hz)]
  change smoothBallConormal A U.actual.1 z-fderiv ℝ U.flat.1 z z -
      r*(ell z*fderiv ℝ U.flat.1 z z+fderiv ℝ U.first.1 z z) =
    smoothBallConormal A V.actual.1 z-fderiv ℝ V.flat.1 z z -
      r*(ell z*fderiv ℝ V.flat.1 z z+fderiv ℝ V.first.1 z z)
  have hC : smoothBallConormal A U.actual.1 z = smoothBallConormal A V.actual.1 z := by
    unfold smoothBallConormal
    rw [hF]
  have hU : fderiv ℝ U.flat.1 z z = fderiv ℝ V.flat.1 z z := hu' hz
  have hQ : fderiv ℝ U.first.1 z z = fderiv ℝ V.first.1 z z := hq' hz
  rw [hC,hU,hQ]

end CalderonN
