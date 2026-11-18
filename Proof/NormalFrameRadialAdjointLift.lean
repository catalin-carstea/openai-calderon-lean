import Proof.MidpointRadialAdjointNative
import Proof.NormalizedCoefficientBoundaryData
import Proof.UniformNormalFrameRadialFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def commonSupportRadialAdjointFamily
    (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
    (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (p : NormalFrameParameter) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  radialAdjointFromResponseL (commonSupportMatrixFamily 2 A hA S hS hz p) (R p+sphereSobolevDegreeL)

/-- Any chosen genuine smooth master radial family has a smooth physical
    adjoint on an open neighborhood of the same actual parameter. The
    pairing holds at every actual profile parameter in that neighborhood. -/
theorem uniform_normalFrame_radial_adjoint_lift {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ A : NormalFrameParameter × X → Mat,∀ hA : ContDiff ℝ ∞ A,
      ∀ S : Set X,∀ hS : IsCompact S,∀ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∀ V : Set NormalFrameParameter,IsOpen V → (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V →
      (∀ p ∈ V,p.1 ∈ Y) →
      (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
        A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap) →
      ∀ R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ R V →
      (∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) →
      (∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
        (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible) →
      (∀ p ∈ V,(negativeBoundaryCoefficientMulL
        (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz p))).IsInvertible) →
      (∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
          (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p))) →
      ∃ W : Set NormalFrameParameter,IsOpen W ∧
        (y,(d.radius y,frameVectorLinear d.frame y)) ∈ W ∧ W ⊆ V ∧
        ContDiffOn ℝ ∞ (commonSupportRadialAdjointFamily A hA S hS hz R) W ∧
        (∀ p ∈ W,(oneBoundaryCoefficientMulL
          (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz p))).IsInvertible) ∧
        ∀ x : X,(x,(d.radius x,frameVectorLinear d.frame x)) ∈ W → ∀ u v,
          ⟪(R (x,(d.radius x,frameVectorLinear d.frame x))+sphereSobolevDegreeL) u,
            sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
            commonSupportRadialAdjointFamily A hA S hS hz R (x,(d.radius x,frameVectorLinear d.frame x)) v⟫_ℝ := by
  obtain ⟨η,hη,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy A hA S hS hz V hV hp0 hCenter hRep R hR hCoercive hStrong hNormal hRestrict
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let M1 := fun p => oneBoundaryCoefficientMulL (normalCoefficientJet (F p))
  have hM : ContDiff ℝ ∞ M1 := contDiff_commonSupport_oneNormalMul A hA S hS hz
  have hData (x : X) (hx : (x,(d.radius x,frameVectorLinear d.frame x)) ∈ V) :
      (∀ w : UnitSphere,0 < coefficientValue 2
        (normalCoefficientJet (F (x,(d.radius x,frameVectorLinear d.frame x)))) w.val) ∧
      (M1 (x,(d.radius x,frameVectorLinear d.frame x))).IsInvertible ∧
      ∀ᵐ z ∂((volume:Measure X).restrict ballOpens),
        (A ((x,(d.radius x,frameVectorLinear d.frame x)),z)).IsSymm := by
    have hxY : x ∈ Y := hCenter _ hx
    have hEll := hElliptic floor hf ε hε hSmall d hd x hxY d.g₁ (by simp)
    have hKP : 1 ≤ 4*K^2 := by nlinarith [sq_nonneg (K-1)]
    have hField (z : X) (hzB : z ∈ (ballOpens:Set X)) :
        coefficientMatrixField 2 (F (x,(d.radius x,frameVectorLinear d.frame x))) z = normalizedFirstNormalCoefficient d x z := by
      rw [coefficientMatrixField_commonSupportMatrixFamily]
      exact ((hRep _ hx z (unitBall_subset_closedBall_two hzB)).eq_of_nhds).trans
        (normalFrameNormalizedCoefficient_framed d.γ d.g₁ d.expMap d.frame x z (d.radius x))
    have hB := normalized_coefficient_boundary_data d x _ (4*K^2) hKP hEll hField
    refine ⟨hB.1,hB.2.1,?_⟩
    simpa only [F,coefficientMatrixField_commonSupportMatrixFamily] using hB.2.2
  let W := V ∩ {p : NormalFrameParameter | (M1 p).IsInvertible}
  have hW : IsOpen W := hV.inter
    (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hM.continuous)
  have hpW : p0 ∈ W := ⟨hp0,(hData y hp0).2.1⟩
  have hSub : W ⊆ V := fun _ h => h.1
  have hOne : ∀ p ∈ W,(oneBoundaryCoefficientMulL (normalCoefficientJet (F p))).IsInvertible := fun _ h => h.2
  have hSmooth := contDiffOn_commonSupport_radialAdjointFromResponse A hA S hS hz
    (fun p => R p+sphereSobolevDegreeL) W ((hR.mono hSub).add contDiffOn_const) hOne
  refine ⟨W,hW,hpW,hSub,hSmooth,hOne,?_⟩
  intro x hx
  have hxV := hSub hx
  have hB := hData x hxV
  exact midpoint_radialAdjointFromResponse_pairing
    (commonSupportEnergyMemLp A hA (x,(d.radius x,frameVectorLinear d.frame x)))
    (hCoercive _ hxV) hB.2.2 (F (x,(d.radius x,frameVectorLinear d.frame x)))
    (fun z _ => congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 A hA S hS hz _) z)
    (hStrong _ hxV) (hNormal _ hxV) hB.1 (R (x,(d.radius x,frameVectorLinear d.frame x))) (hRestrict _ hxV)

end ShrinkingSpheres
