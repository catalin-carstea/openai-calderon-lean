module

public import Proof.CalderonN.BallRegularity.Spaces
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Density

/-! From Proof/Archive/CoordinateWeakIntegration.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory
open scoped ENNReal Distributions InnerProductSpace
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


 
def unitBallCoordinateGradientL (i : Fin dim) :=
  ((EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).compLpL 2
    ((volume : Measure (X dim)).restrict (fixedBallOpens dim))).comp
    (TauCeti.W1p.gradientL (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2))

theorem unitBallCoordinateGradientL_ae (i : Fin dim) (w : (FixedBallH1 dim)) :
    unitBallCoordinateGradientL i w =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
      fun x => (TauCeti.W1p.gradient w x) i := by
  exact (EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).coeFn_compLpL (TauCeti.W1p.gradient w)

 
theorem unitBall_coordinate_weak_integration (w : (FixedBallH1 dim))
    (i : Fin dim) (phi : 𝓓((fixedBallOpens dim), ℝ)) :
    (∫ x in (fixedBallOpens dim), lineDeriv ℝ (phi : (X dim) → ℝ) x (EuclideanSpace.single i 1) *
      TauCeti.W1p.value w x) =
    -(∫ x in (fixedBallOpens dim), phi x * (TauCeti.W1p.gradient w x) i) := by
  have h := (TauCeti.hasWeakFDerivOn_iff.mp (TauCeti.W1p.hasWeakFDerivOn w))
    (EuclideanSpace.single i 1)
  have hi := h.integral_lineDeriv_smul_eq_neg_integral_smul phi
  rw [← TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul phi,
    ← TauCeti.setIntegral_smul_eq_integral_smul phi] at hi
  simpa only [smul_eq_mul, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul] using hi

theorem unitBallCoordinateGradientL_testFunction_ae (i : Fin dim)
    (phi : 𝓓((fixedBallOpens dim), ℝ)) :
    unitBallCoordinateGradientL i (TauCeti.W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 phi)
      =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
      fun x => lineDeriv ℝ (phi : (X dim) → ℝ) x (EuclideanSpace.single i 1) := by
  filter_upwards [unitBallCoordinateGradientL_ae i
    (TauCeti.W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 phi),
    TauCeti.gradientTestFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2 phi]
      with x hx hg
  rw [TauCeti.W1p.gradient_ofTestFunctionₗ, hg] at hx
  rw [hx, (phi.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
  rw [← inner_gradient_left]
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul]

theorem unitBall_coordinate_testFunction_inner_integration (w : (FixedBallH1 dim))
    (i : Fin dim) (phi : 𝓓((fixedBallOpens dim), ℝ)) :
    ⟪unitBallCoordinateGradientL i w,
      TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 phi)⟫_ℝ =
    -⟪TauCeti.W1p.value w,
      unitBallCoordinateGradientL i (TauCeti.W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 phi)⟫_ℝ := by
  have hg : ⟪unitBallCoordinateGradientL i w,
      TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 phi)⟫_ℝ =
      ∫ x in (fixedBallOpens dim), phi x * (TauCeti.W1p.gradient w x) i := by
    rw [TauCeti.W1p.value_ofTestFunctionₗ, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [unitBallCoordinateGradientL_ae i w,
      TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2 phi] with x hx hp
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hx, hp]
  have hv : ⟪TauCeti.W1p.value w,
      unitBallCoordinateGradientL i (TauCeti.W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 phi)⟫_ℝ =
      ∫ x in (fixedBallOpens dim), lineDeriv ℝ (phi : (X dim) → ℝ) x (EuclideanSpace.single i 1) *
        TauCeti.W1p.value w x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [unitBallCoordinateGradientL_testFunction_ae i phi] with x hx
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hx]
  rw [hg, hv]
  have hi := unitBall_coordinate_weak_integration w i phi
  linarith

 
theorem unitBall_coordinate_inner_integration (w : (FixedBallH1 dim)) (i : Fin dim) (v : (FixedBallH1Zero dim)) :
    ⟪unitBallCoordinateGradientL i w, TauCeti.W1p.value (v : (FixedBallH1 dim))⟫_ℝ =
      -⟪TauCeti.W1p.value w, unitBallCoordinateGradientL i (v : (FixedBallH1 dim))⟫_ℝ := by
  have hs : IsClosed {z : (FixedBallH1 dim) |
      ⟪unitBallCoordinateGradientL i w, TauCeti.W1p.valueL z⟫_ℝ =
        -⟪TauCeti.W1p.value w, unitBallCoordinateGradientL i z⟫_ℝ} :=
    isClosed_eq
      ((innerSL ℝ (unitBallCoordinateGradientL i w)).continuous.comp
        TauCeti.W1p.valueL.continuous)
      (continuous_neg.comp ((innerSL ℝ (TauCeti.W1p.value w)).continuous.comp
        (unitBallCoordinateGradientL i).continuous))
  exact TauCeti.w1p0Submodule_subset_of_isClosed hs
    (fun phi => unitBall_coordinate_testFunction_inner_integration w i phi) v.2

end CalderonN.BallDirichlet
