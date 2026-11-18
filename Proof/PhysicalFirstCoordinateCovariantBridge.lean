import Proof.PhysicalFirstCoordinateCoarse
import Proof.BalancedCoarseHighTransport
import Proof.CovariantHalfCoarseBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma PhysicalPrincipalData.firstDerivativeCoordinate_coarse_high_compatible
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) {x : X} (hx : x ∈ Y) (b : I)
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hPair : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Hi=
      (P.firstDerivativeCoordinateHalfL x b).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
      (P.firstDerivativeCoordinateCoarseL b x).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) :=
  balanced_endpoint_high_of_coarse_low _ _ Hi
    (P.firstDerivativeCoordinate_coarse_low_compatible hd hY hx b) hPair

/-- The genuine coarse first jet represents the literal derivative of the
SAME physical coefficient for any already chosen compatible higher family. -/
theorem PhysicalPrincipalData.firstDerivativeCoordinate_covariant_eq_coarse
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (b : I) (a : X)
    (Hi : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hPair : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Hi y)=
      (P.firstDerivativeCoordinateHalfL y b).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hS : CoarseCovariantRotationGraph d y a (P.firstDerivativeCoordinateCoarseL b) S) :
    halfOperatorCovariantDerivativeL d (fun x => P.firstDerivativeCoordinateHalfL x b) Hi y a=
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) := by
  have hLow : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateCoarseL b x)=(P.firstDerivativeCoordinateHalfL x b).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact P.firstDerivativeCoordinate_coarse_low_compatible hd hY hx b
  exact halfOperatorCovariantDerivativeL_eq_coarse _ _ Hi S
    (((P.firstDerivativeCoordinateCoarse_smooth hd hY hΩ hSub hK b).contDiffAt
      (hY.mem_nhds hy)).differentiableAt (by simp))
    (((P.firstDerivativeCoordinateHalfL_smooth hY hΩ hd hK b).contDiffAt
      (hY.mem_nhds hy)).differentiableAt (by simp)) hLow
    (P.firstDerivativeCoordinate_coarse_high_compatible hd hY hy b (Hi y) hPair) hS

end ShrinkingSpheres
