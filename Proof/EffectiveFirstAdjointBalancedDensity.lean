import Proof.EffectiveFirstAdjointDensityCore
import Proof.HalfCovariantOperatorSourceProduct
import Proof.UniformEffectiveFirstAdjointDerivativePair

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

def PhysicalPrincipalData.firstAdjointBalancedDensityRow
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) (y : X) : SphereSobolev (-(1/2:ℝ)) :=
  let L := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  metricDensity d.γ y •
    ((P.firstCovariantCoordinateHalfL b y).adjoint (halfSectionCovariantDerivativeL d L y (axis b))+
      WF.covariantCoordinateAdjointDerivative b b y (L y))+
    fderiv ℝ (metricDensity d.γ) y (axis b) • (P.firstCovariantCoordinateHalfL b y).adjoint
      (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y))

/-- The weak divergence expression is the actual source/adjoint-jet
Leibniz form used by the covariant Green theorem. -/
lemma PhysicalPrincipalData.firstAdjointWeakDensityRow_eq_balanced
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) {y : X} (hy : y ∈ Y) :
    P.firstAdjointWeakDensityRow WF U b y=P.firstAdjointBalancedDensityRow WF U b y := by
  let L := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let C := fun x => (P.firstCovariantCoordinateHalfL b x).adjoint
  let A := WF.covariantCoordinateAdjointHigher b
  let V := fun x => C x (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U x))
  have hL := (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp_contDiffOn hU
  have hC := P.firstCovariantCoordinateAdjoint_smooth hd hY hΩ hK b hw
  have hProduct := half_covariant_operator_source_product d C A L y (axis b)
    (hC.contDiffAt (hY.mem_nhds hy)) (hL.contDiffAt (hY.mem_nhds hy))
  have hFun : (fun x => C x (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (L x)))=V := by
    funext x
    simp only [L,V,sphereSobolevInclusionL_trans_apply]
  rw [hFun] at hProduct
  change fderiv ℝ V y (axis b)-
    frameAngularConnectionHalfL d y (axis b) (WF.covariantAdjointLowSection U b y)=
      C y (halfSectionCovariantDerivativeL d L y (axis b))+
        WF.covariantCoordinateAdjointDerivative b b y (L y) at hProduct
  change metricDensity d.γ y • fderiv ℝ V y (axis b)-
    metricDensity d.γ y • frameAngularConnectionHalfL d y (axis b) (WF.covariantAdjointLowSection U b y)+
    fderiv ℝ (metricDensity d.γ) y (axis b) • V y=_
  calc
    _ = metricDensity d.γ y • (fderiv ℝ V y (axis b)-
        frameAngularConnectionHalfL d y (axis b) (WF.covariantAdjointLowSection U b y))+
        fderiv ℝ (metricDensity d.γ) y (axis b) • V y := by rw [smul_sub]
    _ = metricDensity d.γ y • (C y (halfSectionCovariantDerivativeL d L y (axis b))+
        WF.covariantCoordinateAdjointDerivative b b y (L y))+
        fderiv ℝ (metricDensity d.γ) y (axis b) • V y :=
      congrArg (fun z => metricDensity d.γ y • z+fderiv ℝ (metricDensity d.γ) y (axis b) • V y) hProduct
    _ = _ := rfl

lemma PhysicalPrincipalData.firstAdjointDensityCoreRow_balanced_graph
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (P.firstAdjointDensityCoreRow WF WQ U b y)=P.firstAdjointBalancedDensityRow WF U b y :=
  (P.firstAdjointDensityCoreRow_graph hY hd WF WQ U hU b hw hy).trans
    (P.firstAdjointWeakDensityRow_eq_balanced hY hΩ hd hK WF U hU b hw hy)

end ShrinkingSpheres
