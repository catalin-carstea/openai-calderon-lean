import Proof.DegreeScalarHigherPacket
import Proof.FlatRaisingScalarHigherPacket
import Proof.NativeFirstErrorScalarHigherPacket
import Proof.NativeScalarBoundedHigherEnlarge
import Proof.UniformNativeScalarMixedAdjointData
import Proof.PhysicalPotentialGeneratorBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def nativePotentialGeneratorLow
    (E : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    PhysicalPotentialGeneratorIndex → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  | .inl _ => degreeHalfL
  | .inr (.inl i) => flatHalfRaisingL i
  | .inr (.inr i) => E i

def nativePotentialGeneratorHigh
    (E : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
    PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  | .inl _ => degreeHigherL
  | .inr (.inl i) => flatThreeHalfRaisingL i
  | .inr (.inr i) => E i

def nativePotentialScalarBudget (Q0 : SmoothCoefficientJets 2) (K M0 CC : ℝ) : ℝ :=
  max (4*firstErrorScalarFixedBudget Q0) (firstErrorScalarPacketBudget Q0 K M0 CC)

def nativePotentialAngularBudget (Q0 : SmoothCoefficientJets 2) (K M0 CC CR : ℝ) : ℝ :=
  max (76*firstErrorScalarFixedBudget Q0) (firstErrorScalarAngularCommonBudget Q0 K M0 CC CR)

structure NativePotentialScalarPacketFamily
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (EL : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (EH : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (CQB CZB CAug : ℝ) where
  base : ∀ a,NativeScalarBoundedEndpointData G (nativePotentialGeneratorLow EL a) (nativePotentialGeneratorHigh EH a)
    CQB CZB (potentialGeneratorWeight (d.radius y) a)
  higher : ∀ a,NativeScalarBoundedHigherData (base a) CAug

/-- One common scalar and higher budget for all degree/raising/axis-error
packets, with the SAME selected generator family and exact radius weights. -/
lemma native_potential_scalar_packet_family
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (M0 CC CR : ℝ) (hr : 0 ≤ d.radius y)
    (EL : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (EH : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (E : ∀ i,NativeFirstErrorScalarHigherPacket G (EL i) (EH i) Q0 M0 CC CR (d.radius y)) :
    Nonempty (NativePotentialScalarPacketFamily G EL EH (nativePotentialScalarBudget Q0 K M0 CC)
      (firstErrorScalarPacketBoundedBudget Q0 CQ K M0 CC) (nativePotentialAngularBudget Q0 K M0 CC CR)) := by
  let J := firstErrorScalarFixedBudget Q0
  let QB := nativePotentialScalarBudget Q0 K M0 CC
  let ZB := firstErrorScalarPacketBoundedBudget Q0 CQ K M0 CC
  let AB := nativePotentialAngularBudget Q0 K M0 CC CR
  have hJ : 0 ≤ J := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hZ : 0 ≤ ZB := (firstErrorScalarPacketBoundedBudget_bounds Q0 CQ K M0 CC).1
  have hQD : J ≤ QB := (show J ≤ 4*J by linarith).trans (le_max_left _ _)
  have hQR : 4*J ≤ QB := le_max_left _ _
  have hQE : firstErrorScalarPacketBudget Q0 K M0 CC ≤ QB := le_max_right _ _
  have hAD : J ≤ AB := (show J ≤ 76*J by linarith).trans (le_max_left _ _)
  have hAR : 76*J ≤ AB := le_max_left _ _
  have hAE : firstErrorScalarAngularCommonBudget Q0 K M0 CC CR ≤ AB := le_max_right _ _
  let P (a : PhysicalPotentialGeneratorIndex) :
      Σ B : NativeScalarBoundedEndpointData G (nativePotentialGeneratorLow EL a) (nativePotentialGeneratorHigh EH a)
        QB ZB (potentialGeneratorWeight (d.radius y) a),NativeScalarBoundedHigherData B AB := by
    rcases a with u | (i | i)
    · exact ⟨(G.degree_scalar_packet hF0 Q0 hQ0).enlarge zero_le_one hQD hZ,
        (G.degree_scalar_higher_packet hF0 Q0 hQ0).enlarge zero_le_one hQD hZ hAD⟩
    · exact ⟨(G.flat_raising_scalar_packet hF0 Q0 hQ0 i).enlarge zero_le_one hQR hZ,
        (G.flat_raising_scalar_higher_packet hF0 Q0 hQ0 i).enlarge zero_le_one hQR hZ hAR⟩
    · exact ⟨(E i).base.enlarge hr hQE le_rfl,(E i).higher.enlarge hr hQE le_rfl hAE⟩
  exact ⟨{base := fun a => (P a).1,higher := fun a => (P a).2}⟩

/-- The common uniform mixed producer acts on all49 generator pairs and
on ANY selected genuine higher adjoint endpoint. -/
lemma NativePotentialScalarPacketFamily.mixed_data
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {G : NativeTaylorGeneratorBounds s h hK CG}
    {EL : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {EH : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)} {CQB CZB CAug CS : ℝ}
    (P : NativePotentialScalarPacketFamily G EL EH CQB CZB CAug)
    (hMixed : NativeScalarPacketMixedAdjointData G CQB CZB CAug CS) (hr : 0 ≤ d.radius y)
    (a b : PhysicalPotentialGeneratorIndex)
    (Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHa : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (nativePotentialGeneratorLow EL a).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    Nonempty (GradedBalancedCommutatorBound
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (nativePotentialGeneratorLow EL a).adjoint (nativePotentialGeneratorLow EL b) Ha (nativePotentialGeneratorHigh EH b)
      (CS*potentialGeneratorWeight (d.radius y) a*potentialGeneratorWeight (d.radius y) b)) :=
  hMixed _ _ (potentialGeneratorWeight_nonneg hr a) (potentialGeneratorWeight_nonneg hr b) _ _ _ _
    (P.base a) (P.base b) (P.higher a) (P.higher b) Ha hHa
end ShrinkingSpheres
