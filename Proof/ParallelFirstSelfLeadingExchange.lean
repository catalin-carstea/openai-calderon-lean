import Proof.ParallelFirstSelfLeadingAlgebra
import Proof.ParallelFirstSelfConditional
import Proof.UniformEffectiveFirstAngularCommutator
import Proof.BalancedCoarseHighTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma firstSelfSourceDerivative_to_one (d : Data)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hU : DifferentiableAt ℝ U y) (a : X) :
    sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (firstSelfSourceDerivative d U y a)=
      highSectionCovariantDerivative d (fiveHalfToTwoSection U) y a := by
  have h := gradedSphereSectionCovariantDerivative_inclusion (5/2:ℝ) 2 (by norm_num) d U y a hU
  have hI : sphereSobolevInclusionL ((5/2:ℝ)-1) ((2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) := by congr 1 <;> norm_num
  change sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
    (gradedSphereSectionCovariantDerivative (5/2:ℝ) d U y a)=
    highSectionCovariantDerivative d
      (fun x => sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) (U x)) y a
  rw [hI] at h
  exact h.trans (gradedSphereSectionCovariantDerivative_two d _ y a)


variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

/-- The crossed covariant derivative rows, before their base exchange is
integrated. The true-adjoint higher family is the SAME fixed WF. -/
def firstSelfCrossedAdjointDensity {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  metricDensity d.γ y*(∑ b : I,∑ c : I,
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (WF.covariantCoordinateAdjointHigher b y (firstSelfSourceDerivative d U y (axis c))),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (WF.covariantCoordinateAdjointHigher c y (firstSelfSourceDerivative d U y (axis b)))⟫_ℝ)

def firstSelfAngularDensity {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  metricDensity d.γ y*firstCommutatorForm (fun b c => WF.coordinateCommLow b c y)
    (fun b => halfSectionCovariantDerivativeL d
      (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (axis b))

def firstSelfExchangeDensity {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  firstSelfCrossedAdjointDensity WF U y-metricDensity d.γ y*‖firstAdjointLeadingCoreSection WF U y‖^2

/-- Actual leading-square cancellation: the angular commutator is
separated exactly, while the antisymmetric base exchange is retained. -/
theorem firstSelfLeadingDensity_eq_angular_exchange
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y)
    (hRaw : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    firstSelfLeadingDensity P WF U y=firstSelfAngularDensity WF U y+firstSelfExchangeDensity WF U y := by
  let V := fun b : I => firstSelfSourceDerivative d U y (axis b)
  have hH (b : I) := P.firstCovariantCoordinateHigherL_balanced b y (hRaw b)
  have hA (b : I) := WF.covariantCoordinateAdjointHigher_balanced b hy
  have hComm (b c : I) := WF.covariantCoordinateCommLow_graph b c hy (hRaw c)
  have hForward := first_forward_square_eq_commutator_cross
    (fun b => P.firstCovariantCoordinateHalfL b y) (fun b => P.firstCovariantCoordinateHigherL b y)
    (fun b => WF.covariantCoordinateAdjointHigher b y) (fun b c => WF.coordinateCommLow b c y)
    hH hA hComm V
  have hRow (b : I) : P.firstCovariantCoreRow (fiveHalfToTwoSection U) b y=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.firstCovariantCoordinateHigherL b y (V b)) := by
    have hHigh := balanced_endpoint_high_of_coarse_low _ _ _
      (P.firstCovariantCoordinate_coarse_half_compatible hd hY hy b) (hH b)
    have hPoint := DFunLike.congr_fun hHigh (V b)
    simp only [ContinuousLinearMap.comp_apply] at hPoint
    unfold PhysicalPrincipalData.firstCovariantCoreRow
    rw [←firstSelfSourceDerivative_to_one d U hU]
    exact hPoint.symm
  have hSum : P.firstCovariantCoreSection (fiveHalfToTwoSection U) y=
      ∑ b : I,sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.firstCovariantCoordinateHigherL b y (V b)) :=
    Finset.sum_congr rfl (fun b hb => hRow b)
  have hInputs : (fun b => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V b))=
      (fun b => halfSectionCovariantDerivativeL d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (axis b)) :=
    funext (fun b => firstSelfSourceDerivative_inclusion d U hU (axis b))
  rw [hInputs] at hForward
  unfold firstSelfLeadingDensity firstSelfAngularDensity firstSelfExchangeDensity firstSelfCrossedAdjointDensity
  rw [hSum,hForward]
  ring

/-- The forward-half route retains exchange and the full adjoint defect
together; no separate HIGH estimate for the adjoint derivative is assumed. -/
def firstSelfExchangeDefectDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  firstSelfExchangeDensity WF U y-firstSelfDefectCrossDensity P WF W U y-firstSelfDefectSquareDensity P WF W U y

lemma firstSelfDensity_eq_angular_exchange_defect
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y)
    (hRaw : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    firstSelfDensity P WF W U y=firstSelfAngularDensity WF U y+firstSelfExchangeDefectDensity P WF W U y := by
  have hLeading := firstSelfLeadingDensity_eq_angular_exchange hY hd P WF U hy hU hRaw
  rw [firstSelfDensity_core_split]
  unfold firstSelfLeadingDensity at hLeading
  unfold firstSelfExchangeDefectDensity firstSelfDefectCrossDensity firstSelfDefectSquareDensity
  linarith only [hLeading]

end ShrinkingSpheres.ParallelEnergy
