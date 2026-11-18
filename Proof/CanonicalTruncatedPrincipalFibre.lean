import Proof.PhysicalTruncatedCoreOperators
import Proof.HarmonicHigherTestSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

private lemma residual_rearrange {A : Type*} [AddCommGroup A] (a t j r u : A)
    (h : a-t-j-r=u) : a=t+u+j+r := by
  have hh := sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp h))
  rw [hh]
  abel

/-- The actual principal trace has the exact fibre decomposition into
twice the selected raising output, the constructed truncated residual and
the same two original complementary operators. -/
theorem PhysicalPrincipalData.canonical_truncated_plus_complements_ae
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (hφ : Test Y d.γ d.frame φ) (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (L : ℂ →L[ℝ] ℝ) (C : AngularComponentData E d.radius L) {y : X} (hy : y ∈ Y) :
    let F := fun p => L (E.representative p)
    let hF : ContDiff ℝ ∞ F := L.contDiff.comp E.representativeSmooth
    let U := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) F hF
    let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
    Z.symm ((2:ℝ) • Z (C.raisingOutput y)+P.truncatedCovariantCoreSection W U y+
      firstCorrectionCrossRemainderL Q d y (ambientSobolevSection 1 (by norm_num) F hF y)+
      P.potentialRemainderCoarseL y (ambientSobolevSection 1 (by norm_num) F hF y)) =ᵐ[sphereProbability]
      fun v : UnitSphere => L (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ (y,frameVector d.frame y v.val)) := by
  extract_lets F hF U Z
  let U2 := ambientSobolevSection 2 (by norm_num) F hF
  have hU : ContDiff ℝ ∞ U := contDiff_ambientHigherSobolevSection (5/2:ℝ) (by norm_num) F hF
  have hU2 : fiveHalfToTwoSection U=U2 := funext (fun x =>
    ambientHigherSobolevSection_inclusion (5/2:ℝ) 2 (by norm_num) (by norm_num) (by norm_num) F hF x)
  obtain ⟨S,hS⟩ := P.canonical_principal_truncated_residual hY hd hK Q hQ hφ E L C
  have hCore := P.truncatedCovariantCoreSection_balanced hY hΩ hd hK W U hU hy
  rw [hU2] at hCore
  have hEq := (hS y hy).trans hCore.symm
  have hActual := (sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)) hEq
  have hOne := ambientSobolevSection_inclusion 2 1 (by norm_num) (by norm_num) (by norm_num) F hF y
  change sphereSobolevInclusionL 2 1 (by norm_num) (U2 y)=ambientSobolevSection 1 (by norm_num) F hF y at hOne
  have hExpanded0 := residual_rearrange _ _ _ _ _ hActual
  have hExpanded := hExpanded0.trans (congrArg (fun z : SphereSobolev 1 =>
    (2:ℝ) • Z (C.raisingOutput y)+P.truncatedCovariantCoreSection W U y+
      firstCorrectionCrossRemainderL Q d y z+P.potentialRemainderCoarseL y z) hOne)
  have hRep := S.principal_ae hY hSub hd hK hφ.1 hy
  have hSphereEq := congrArg (fun z : SphereSobolev 0 => Z.symm z) hExpanded
  rw [hSphereEq] at hRep
  exact hRep

end ShrinkingSpheres
