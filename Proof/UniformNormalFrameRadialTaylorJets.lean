import Proof.UniformNormalFrameCovariantTaylorJet
import Proof.UniformNormalFrameAngularTaylorJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- One actual native midpoint family simultaneously has the quadratic
    point, angular commutator and moving-radius covariant center bounds.
    Its actual response and all native inverse witnesses are retained. -/
theorem uniform_normalFrame_radial_taylor_jets {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 CC CD : ℝ,0 < η ∧ 0 ≤ C0 ∧ 0 ≤ CC ∧ 0 ≤ CD ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A : NormalFrameParameter × X → Mat,∃ hA : ContDiff ℝ ∞ A,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∃ V : Set NormalFrameParameter,IsOpen V ∧ (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V ∧
        (∀ p ∈ V,p.1 ∈ Y) ∧
        (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap) ∧
      ∃ R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ R V ∧ ContDiffOn ℝ ∞ (normalFrameRadialTaylorFamily d R) V ∧
        (∀ x : X,(x,(d.radius x,frameVectorLinear d.frame x)) ∈ V →
          RealizesActualMidpointRadialError d x (R (x,(d.radius x,frameVectorLinear d.frame x)))) ∧
        (∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
          (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible) ∧
        (∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) ∧
        (∀ p ∈ V,(negativeBoundaryCoefficientMulL
          (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz p))).IsInvertible) ∧
        (∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p))) ∧
        (∀ a : X,
          let H := normalFrameRadialTaylorFamily d R
          ‖deriv (fun t => H (normalFrameActualCurve d.frame d.radius y a t)) 0-
            ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
              deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤
            CD*(d.radius y)^2*beta d.γ d.radius y*‖a‖) ∧
        let H := normalFrameRadialTaylorFamily d R
        let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
        ‖H p0‖ ≤ C0*(d.radius y)^2 ∧ ∀ i j : I,
          let C := deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0
          ‖C‖ ≤ CC*(d.radius y)^2 ∧ ∀ f : SphereSobolev 2,
            sphereSobolevRotationL 0 i j (H p0 (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
              sphereSobolevInclusionL 0 (-1) (by norm_num)
                (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+H p0 (sphereSobolevRotationL 2 i j f)) := by
  obtain ⟨ηD,CD,hηD,hCD,hDerivative⟩ := uniform_normalFrame_covariant_radial_taylor_jet hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,C0,CC,hηA,hC0,hCC,hAngular⟩ := uniform_normalFrame_angular_radial_taylor_jet hY hΩ (by omega) K ρ c₀ M Cj hK hρ
  refine ⟨min ηD ηA,C0,CC,CD,lt_min hηD hηA,hC0,hCC,hCD,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨A,hA,S,hS,hz,V,hV,hpV,hCenter,hRep,R,hR,hH,hActual,hStrong,hCoercive,hNormal,hRestrict,hJet⟩ :=
    hDerivative floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  have hAngle := hAngular floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
    A hA S hS hz V hV hpV hRep R hR hCoercive hStrong hRestrict
  exact ⟨A,hA,S,hS,hz,V,hV,hpV,hCenter,hRep,R,hR,hH,hActual,hStrong,hCoercive,hNormal,hRestrict,hJet,hAngle⟩

end ShrinkingSpheres
