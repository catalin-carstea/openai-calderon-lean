import Proof.EffectiveFirstAdjointFiveHalfBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma continuousOn_firstAdjointFiveHalfCoordinateBudget
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    ContinuousOn (firstAdjointFiveHalfCoordinateBudget d CG CK b) Y := by
  let H := fun y => (3*CG+CK)*(1+|d.radius y|)
  have hH : ContinuousOn H Y := continuousOn_const.mul
    (continuousOn_const.add hd.2.2.2.2.1.1.continuousOn.abs)
  have hQ (i j : I) := (hd.contDiffOn_framePrincipalCoefficient hSub hK i j).continuousOn
  have he (i : I) := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hT (i : I) := (contDiffOn_scaledFrameLogRadius hY hd.2.2.2.2.1.1
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne') he i).continuousOn
  have hCorr (i : I) : ContinuousOn (fun y => ‖firstFrameCorrectionAdjointFiveHalfL d y i‖) Y := by
    let Adj : (SphereSobolev (-(3/2:ℝ)) →L[ℝ] SphereSobolev (-(3/2:ℝ))) →L[ℝ]
        (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) :=
      ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
    exact ((Adj.contDiff.comp_contDiffOn
      (hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK (-(3/2:ℝ)) i)).clm_comp
      (contDiffOn_const (c:=sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))).continuousOn.norm
  have hF (j : I) : ContinuousOn (firstAdjointFiveHalfFrameBudget d CG CK j) Y := by
    exact ((continuousOn_finsetSum Finset.univ (fun i _ =>
      (((hQ i j).add (hQ j i)).mul (hT i)).abs.mul hH)).add
      (continuousOn_const.mul (continuousOn_finsetSum Finset.univ (fun i _ =>
        ((hQ i j).sub continuousOn_const).abs.mul hH)))).add
      (hd.2.2.2.2.1.1.continuousOn.abs.mul (continuousOn_finsetSum Finset.univ
        (fun i _ => ((hQ i j).add (hQ j i)).abs.mul ((hCorr i).add hH))))
  exact (continuousOn_finsetSum Finset.univ (fun j _ =>
    (((EuclideanSpace.proj (𝕜:=ℝ) b).contDiff.comp_contDiffOn (he j)).continuousOn.abs).mul (hF j))).add
      hw.continuousOn.abs

end ShrinkingSpheres
