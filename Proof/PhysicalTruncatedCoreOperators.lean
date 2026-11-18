import Proof.PhysicalScalarCoreDomain
import Proof.EffectiveFirstCoreAdjunction
import Proof.PhysicalPotentialCoreAdjunctionIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def fiveHalfToTwoSection (U : X → SphereSobolev (5/2:ℝ)) : X → SphereSobolev 2 :=
  fun y => sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) (U y)

namespace PhysicalPrincipalData
variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

def truncatedCovariantCoreSection (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : SphereSobolev 0 :=
  scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U) y+
    P.firstCovariantCoreSection (fiveHalfToTwoSection U) y+P.potentialQuadraticCoreSection W U y

def truncatedFormalAdjointCore (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : SphereSobolev 0 :=
  scalarCovariantSecondTransposeSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
      (fiveHalfToTwoSection U) y+
    P.firstFormalAdjointCore WF W U y+P.potentialQuadraticAdjointCoreSection W U y

/-- The assembled fibre L2 output represents the SAME actual truncated
residual, through the genuine negative Sobolev inclusion. -/
lemma truncatedCovariantCoreSection_balanced (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.truncatedCovariantCoreSection W U y)=
      P.truncatedResidualValue (fiveHalfToTwoSection U) y := by
  have hU2 : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  rw [P.truncatedResidualValue_covariant_derivative_normal_form hd hY hΩ hK _ hU2.contDiffOn hy]
  simp only [truncatedCovariantCoreSection,scalarCovariantSecondSection,firstCovariantCoreSection,
    firstCovariantCoreRow,map_add,potentialQuadraticCoreSection,dite_eq_left hy]
  rw [P.potentialQuadraticCoreL_balanced hy (W y hy)]
  simp only [fiveHalfToTwoSection,sphereSobolevInclusionL_trans_apply]

lemma truncatedCoreOperators_memLp (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (p : ℝ≥0∞) :
    MemLp (P.truncatedCovariantCoreSection W U) p (volume.restrict Y) ∧
      MemLp (P.truncatedFormalAdjointCore WF W U) p (volume.restrict Y) := by
  have hU2 : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have h0U2 (y) (hy : y ∉ S) : fiveHalfToTwoSection U y=0 := by simp only [fiveHalfToTwoSection,h0U y hy,map_zero]
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK
  have hScalar := physical_scalar_principal_core_memLp hY hSub hd hK _ hU2 S hS hSY h0U2 p
  have hF := P.firstCovariantCoreSection_memLp hY hΩ hSub hd hK _ hU2 S hS hSY h0U2 hw p
  have hFA := P.firstFormalAdjointCore_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY h0U hw p
  have hQ := P.potentialQuadraticCoreSection_memLp hY hSub hd hK W hCK U hU S hS hSY h0U p
  have hQA := P.potentialQuadraticAdjointCoreSection_memLp hY hSub hd hK W hCG hCK U hU S hS hSY h0U p
  exact ⟨(hScalar.1.add hF).add hQ,(hScalar.2.add hFA).add hQA⟩

lemma truncatedCoreOperators_zero_off (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) {y : X} (hy : y ∉ S) :
    P.truncatedCovariantCoreSection W U y=0 ∧ P.truncatedFormalAdjointCore WF W U y=0 := by
  have h0U2 (x) (hx : x ∉ S) : fiveHalfToTwoSection U x=0 := by simp only [fiveHalfToTwoSection,h0U x hx,map_zero]
  have hScalar := scalarCovariantSecondSection_zero_off d (scalarPrincipalMatrix d.γ d.g₂ d.radius) _ S hS h0U2 y hy
  have hScalarA := scalarCovariantSecondTransposeSection_zero_off d (metricDensity d.γ)
    (scalarPrincipalMatrix d.γ d.g₂ d.radius) _ S hS h0U2 y hy
  have hF : P.firstCovariantCoreSection (fiveHalfToTwoSection U) y=0 := by
    unfold firstCovariantCoreSection firstCovariantCoreRow
    simp only [highSectionCovariantDerivative_zero_off d _ S hS h0U2 _ y hy,map_zero,Finset.sum_const_zero]
  have hFA := P.firstFormalAdjointCore_zero_off hY hd WF W U hU S hS hSY h0U
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK) hy
  simp only [truncatedCovariantCoreSection,truncatedFormalAdjointCore,hScalar,hScalarA,hF,hFA,
    P.potentialQuadraticCoreSection_zero_of_source_zero W U (h0U y hy),
    P.potentialQuadraticAdjointCoreSection_zero_of_source_zero W U (h0U y hy),add_zero,zero_add,and_self]

theorem truncatedCoreOperators_weighted_square_integrable (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) :
    IntegrableOn (fun y => metricDensity d.γ y*‖P.truncatedCovariantCoreSection W U y‖^2) Y ∧
      IntegrableOn (fun y => metricDensity d.γ y*‖P.truncatedFormalAdjointCore WF W U y‖^2) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have hLp := P.truncatedCoreOperators_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY h0U 2
  have h0 (y) (hy : y ∉ S) := P.truncatedCoreOperators_zero_off hY hSub hd hK WF W U hU S hS.isClosed hSY h0U hy
  exact ⟨integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _ hLp.1
    (fun y _ hs => (h0 y hs).1) _ (hg.contDiffOn_density hK).continuousOn (fun _ _ => Real.sqrt_nonneg _),
    integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _ hLp.2
    (fun y _ hs => (h0 y hs).2) _ (hg.contDiffOn_density hK).continuousOn (fun _ _ => Real.sqrt_nonneg _)⟩

end PhysicalPrincipalData
end ShrinkingSpheres
