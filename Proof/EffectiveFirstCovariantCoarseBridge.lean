import Proof.EffectiveFirstScalarDriftCommutator
import Proof.PhysicalFirstCoordinateCovariantBridge
import Proof.HalfCovariantAdjointPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma PhysicalPrincipalData.firstCovariantCoordinateHalfL_smooth
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hK : 0 < K) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    ContDiffOn ℝ ∞ (P.firstCovariantCoordinateHalfL b) Y :=
  (P.firstDerivativeCoordinateHalfL_smooth hY hΩ hd hK b).sub (hw.smul contDiffOn_const)

lemma PhysicalFirstCommutatorPacket.covariantCoordinateAdjointHigher_smooth
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data} {P : PhysicalPrincipalData Y d CF CT}
    (W : PhysicalFirstCommutatorPacket P CB CS ε) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    ContDiffOn ℝ ∞ (W.covariantCoordinateAdjointHigher b) Y :=
  (W.coordinateAdjointHigher_smooth hd b).sub (hw.smul contDiffOn_const)

lemma PhysicalPrincipalData.firstCovariantCoordinateAdjoint_smooth
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hK : 0 < K) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    ContDiffOn ℝ ∞ (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint) Y := by
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  exact Adj.contDiff.comp_contDiffOn (P.firstCovariantCoordinateHalfL_smooth hd hY hΩ hK b hw)

/-- The SAME actual effective coarse coefficient jet is the literal
covariant derivative of its balanced family. The higher graph is genuine;
no smoothness is demanded of a pointwise higher witness. -/
theorem PhysicalPrincipalData.firstCovariantCoordinate_covariant_eq_coarse
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hK : 0 < K) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y)
    (hB : ContDiffOn ℝ ∞ (P.firstCovariantCoordinateCoarseL b) Y)
    {y : X} (hy : y ∈ Y) (a : X)
    (Hi : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hPair : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Hi y)=
      (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hS : CoarseCovariantRotationGraph d y a (P.firstCovariantCoordinateCoarseL b) S) :
    halfOperatorCovariantDerivativeL d (P.firstCovariantCoordinateHalfL b) Hi y a=
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) := by
  have hLow : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstCovariantCoordinateCoarseL b x)=(P.firstCovariantCoordinateHalfL b x).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact P.firstCovariantCoordinate_coarse_half_compatible hd hY hx b
  have hHigh := balanced_endpoint_high_of_coarse_low _ _ (Hi y)
    (P.firstCovariantCoordinate_coarse_half_compatible hd hY hy b) hPair
  have hC := P.firstCovariantCoordinateHalfL_smooth hd hY hΩ hK b hw
  exact halfOperatorCovariantDerivativeL_eq_coarse _ _ Hi S
    ((hB.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hC.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hLow hHigh hS

end ShrinkingSpheres
