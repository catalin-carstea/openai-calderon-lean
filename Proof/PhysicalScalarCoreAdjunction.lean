import Proof.PhysicalScalarCoreDomain
import Proof.ScalarCovariantSecondAdjunction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

theorem physical_scalar_principal_core_green
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (U V : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) :
    let μ := metricDensity d.γ
    let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
    let L := fun y => μ y*⟪sphereSobolevInclusionL 2 0 (by norm_num) (U y),scalarCovariantSecondSection d A V y⟫_ℝ
    let R := fun y => μ y*⟪sphereSobolevInclusionL 2 0 (by norm_num) (V y),scalarCovariantSecondTransposeSection d μ A U y⟫_ℝ
    IntegrableOn L Y ∧ IntegrableOn R Y ∧ (∫ y in Y,L y)=(∫ y in Y,R y) := by
  let μ := metricDensity d.γ
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let L := fun y => μ y*⟪sphereSobolevInclusionL 2 0 (by norm_num) (U y),scalarCovariantSecondSection d A V y⟫_ℝ
  let Lr := fun y => μ y*⟪scalarCovariantSecondSection d A V y,sphereSobolevInclusionL 2 0 (by norm_num) (U y)⟫_ℝ
  let R := fun y => μ y*⟪sphereSobolevInclusionL 2 0 (by norm_num) (V y),scalarCovariantSecondTransposeSection d μ A U y⟫_ℝ
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun y => d.frame y i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hData := scalar_covariant_second_transpose_adjoint_data hY d hg hK he μ (hg.contDiffOn_density hK)
    (fun y hy => metricDensity_pos hg hK hy) A (hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK)
    V U hV hU S hS hSY h0V h0U
  have hData' : Integrable Lr ∧ Integrable R ∧ (∫ y,Lr y)=(∫ y,R y) := by
    simpa only [Lr,R,ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hData
  have hLR : L=Lr := funext (fun y => congrArg (fun z => μ y*z) (real_inner_comm _ _))
  change IntegrableOn L Y ∧ IntegrableOn R Y ∧ (∫ y in Y,L y)=(∫ y in Y,R y)
  rw [hLR]
  refine ⟨hData'.1.integrableOn,hData'.2.1.integrableOn,?_⟩
  have h0Uout (y) (hy : y ∉ Y) : U y=0 := h0U y (fun hs => hy (hSY hs))
  have h0Vout (y) (hy : y ∉ Y) : V y=0 := h0V y (fun hs => hy (hSY hs))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    simp only [Lr,h0Uout y hy,map_zero,inner_zero_right,mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    simp only [R,h0Vout y hy,map_zero,inner_zero_left,mul_zero])]
  exact hData'.2.2

end ShrinkingSpheres
