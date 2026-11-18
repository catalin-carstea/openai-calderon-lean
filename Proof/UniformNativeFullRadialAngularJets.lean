import Proof.NativeFullRadialAngularRegularity
import Proof.UniformNativeTaylorAngularJets
import Proof.UniformRelativeAngularDerivativeJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

theorem uniform_native_full_radial_angular_field_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η B : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ B ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ CF0 CA0 CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM,
      ∃ V : s.response.SymmetricAdjointDomain,
        CoarseAngularFields.JetBound s.response.fullAdjointAngularFields
          ((y,frameVectorLinear d.frame y),0) 3 B := by
  obtain ⟨η,BT,hη,hη1,hBT,hTaylorData⟩ := uniform_native_taylor_angular_field_three_jets
    hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0
  let B := BT+(CoarseAngularFields.ofPacket degreeCoarseAdjointPacket).budget+firstRadialAngularFieldJetBudget*CQ
  have hB : 0 ≤ B := by
    have hDegree := (CoarseAngularFields.ofPacket degreeCoarseAdjointPacket).budget_nonneg
    have hFirst := firstRadialAngularFieldJetBudget_nonneg
    dsimp only [B]
    positivity
  refine ⟨η,B,hη,hη1,hB,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  obtain ⟨V,hT⟩ := hTaylorData floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans (hSmall.trans hη1)
  have hrr : (d.radius y)^2 ≤ 1 := by nlinarith only [hr.le,hr1]
  have hTaylor := hT.weaken ((mul_le_mul_of_nonneg_left hrr hBT).trans_eq (mul_one _))
  have hEll : SmoothFiniteJetBound (normalFrameRelativeFirstCovector d.γ d.g₁) p0 3 CQ :=
    ⟨hCQ,s.coefficients.covectorSmooth.contDiffAt (s.coefficients.domainOpen.mem_nhds s.coefficients.pointMem),
      fun n hn => s.coefficients.firstCovectorJets (by norm_num) n hn⟩
  exact ⟨V,s.response.fullAdjointAngularFields_jet_bound p0 3 BT CQ hTaylor hEll hr.le hr1⟩

end ShrinkingSpheres
