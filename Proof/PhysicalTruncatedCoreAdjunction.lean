import Proof.PhysicalTruncatedCoreOperators
import Proof.PhysicalScalarCoreAdjunction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Actual adjunction of the complete SAME scalar/first/potential
truncated residual and its constructed physical formal adjoint. -/
theorem PhysicalPrincipalData.truncatedCoreOperators_green
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U V : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) :
    IntegrableOn (fun y => metricDensity d.γ y*
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),P.truncatedCovariantCoreSection W V y⟫_ℝ) Y ∧
    IntegrableOn (fun y => metricDensity d.γ y*
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (V y),P.truncatedFormalAdjointCore WF W U y⟫_ℝ) Y ∧
    (∫ y in Y,metricDensity d.γ y*
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),P.truncatedCovariantCoreSection W V y⟫_ℝ)=
      (∫ y in Y,metricDensity d.γ y*
        ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (V y),P.truncatedFormalAdjointCore WF W U y⟫_ℝ) := by
  let U2 := fiveHalfToTwoSection U
  let V2 := fiveHalfToTwoSection V
  let U0 := fun y => sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y)
  let V0 := fun y => sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (V y)
  let μ := metricDensity d.γ
  let a := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let LS := fun y => μ y*⟪U0 y,scalarCovariantSecondSection d a V2 y⟫_ℝ
  let RS := fun y => μ y*⟪V0 y,scalarCovariantSecondTransposeSection d μ a U2 y⟫_ℝ
  let LF := fun y => μ y*⟪U0 y,P.firstCovariantCoreSection V2 y⟫_ℝ
  let RF := fun y => μ y*⟪V0 y,P.firstFormalAdjointCore WF W U y⟫_ℝ
  let LQ := fun y => μ y*⟪U0 y,P.potentialQuadraticCoreSection W V y⟫_ℝ
  let RQ := fun y => μ y*⟪V0 y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ
  have hU2 : ContDiff ℝ ∞ U2 := (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have hV2 : ContDiff ℝ ∞ V2 := (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hV
  have h0U2 (y) (hy : y ∉ S) : U2 y=0 := by simp only [U2,fiveHalfToTwoSection,h0U y hy,map_zero]
  have h0V2 (y) (hy : y ∉ S) : V2 y=0 := by simp only [V2,fiveHalfToTwoSection,h0V y hy,map_zero]
  have hScalar := physical_scalar_principal_core_green hY hSub hd hK U2 V2 hU2 hV2 S hS hSY h0U2 h0V2
  have hS' : IntegrableOn LS Y ∧ IntegrableOn RS Y ∧ (∫ y in Y,LS y)=(∫ y in Y,RS y) := by
    simpa only [LS,RS,U2,V2,U0,V0,fiveHalfToTwoSection,sphereSobolevInclusionL_trans_apply] using hScalar
  have hFirst := P.firstCoreOperators_green hY hΩ hSub hd hK WF W hCG hCK U V2 hU hV2 S hS hSY h0U h0V2
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK)
  have hF' : IntegrableOn LF Y ∧ IntegrableOn RF Y ∧ (∫ y in Y,LF y)=(∫ y in Y,RF y) := by
    simpa only [LF,RF,U2,V2,U0,V0,fiveHalfToTwoSection,sphereSobolevInclusionL_trans_apply] using hFirst
  have hQ' : IntegrableOn LQ Y ∧ IntegrableOn RQ Y ∧ (∫ y in Y,LQ y)=(∫ y in Y,RQ y) :=
    P.potentialCoreOperators_green hY hSub hd hK W hCG hCK U V hU hV S hS hSY h0U h0V
  have hLeft : (fun y => μ y*⟪U0 y,P.truncatedCovariantCoreSection W V y⟫_ℝ)=
      fun y => LS y+LF y+LQ y := by
    funext y
    simp only [PhysicalPrincipalData.truncatedCovariantCoreSection,LS,LF,LQ,V2,a,inner_add_right,mul_add]
  have hRight : (fun y => μ y*⟪V0 y,P.truncatedFormalAdjointCore WF W U y⟫_ℝ)=
      fun y => RS y+RF y+RQ y := by
    funext y
    simp only [PhysicalPrincipalData.truncatedFormalAdjointCore,RS,RF,RQ,U2,a,μ,inner_add_right,mul_add]
  change IntegrableOn _ Y ∧ IntegrableOn _ Y ∧ _
  rw [hLeft,hRight]
  refine ⟨(hS'.1.add hF'.1).add hQ'.1,(hS'.2.1.add hF'.2.1).add hQ'.2.1,?_⟩
  rw [integral_add (f:=fun y => LS y+LF y) (g:=LQ) (hS'.1.add hF'.1) hQ'.1,
    integral_add (f:=LS) (g:=LF) hS'.1 hF'.1,
    integral_add (f:=fun y => RS y+RF y) (g:=RQ) (hS'.2.1.add hF'.2.1) hQ'.2.1,
    integral_add (f:=RS) (g:=RF) hS'.2.1 hF'.2.1,hS'.2.2,hF'.2.2,hQ'.2.2]

end ShrinkingSpheres
