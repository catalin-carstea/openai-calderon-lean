import Proof.NativeHalfTaylorHigherEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
open OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}
  {t : NormalFrameRelativeResponsePacket q}

lemma SymmetricAdjointDomain.higherTaylor_jet_bounds (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (J : ℕ) (BL BS : ℝ)
    (hL : SmoothFiniteJetBound q.halfTaylor p J BL)
    (hS : SmoothFiniteJetBound (V.degreeFamily h hK hZ) p J BS) :
    SmoothFiniteJetBound (V.forwardHigherTaylor h hK hZ) p J (BL+BS) ∧
      SmoothFiniteJetBound (V.adjointHigherTaylor h hK hZ) p J (BL+BS) := by
  constructor
  · change SmoothFiniteJetBound (fun x => halfDegreeHigherLift (q.halfTaylor x) (V.degreeFamily h hK hZ x)) p J _
    exact halfDegreeHigherLift_jet_bound hL hS
  · have hSA := hS.adjoint.const_smul (-1)
    simp only [abs_neg,abs_one,one_mul,neg_one_smul] at hSA
    change SmoothFiniteJetBound (fun x => halfDegreeHigherLift (q.halfTaylor x).adjoint (-(V.degreeFamily h hK hZ x).adjoint)) p J _
    exact halfDegreeHigherLift_jet_bound hL.adjoint hSA

lemma SymmetricAdjointDomain.contDiffOn_forwardHigherTaylor (V : t.SymmetricAdjointDomain)
    (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z) :
    ContDiffOn ℝ ∞ (V.forwardHigherTaylor h hK hZ) V.domain := by
  intro p hp
  exact (contDiffAt_halfDegreeHigherLift q.halfTaylor (V.degreeFamily h hK hZ) p
    (V.contDiffOn_halfTaylor.contDiffAt (V.domainOpen.mem_nhds hp))
    ((V.contDiffOn_degreeFamily hΩ h hK hZ).contDiffAt (V.domainOpen.mem_nhds hp))).contDiffWithinAt

lemma SymmetricAdjointDomain.contDiffOn_adjointHigherTaylor (V : t.SymmetricAdjointDomain)
    (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z) :
    ContDiffOn ℝ ∞ (V.adjointHigherTaylor h hK hZ) V.domain := by
  let A := (ContinuousLinearMap.adjoint :
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) ≃ₗᵢ[ℝ]
      (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (1/2:ℝ))).toContinuousLinearEquiv.toContinuousLinearMap
  have hL := A.contDiff.comp_contDiffOn V.contDiffOn_halfTaylor
  have hS := (A.contDiff.comp_contDiffOn (V.contDiffOn_degreeFamily hΩ h hK hZ)).neg
  intro p hp
  exact (contDiffAt_halfDegreeHigherLift _ _ p (hL.contDiffAt (V.domainOpen.mem_nhds hp))
    (hS.contDiffAt (V.domainOpen.mem_nhds hp))).contDiffWithinAt
end ShrinkingSpheres.NormalFrameRelativeResponsePacket
