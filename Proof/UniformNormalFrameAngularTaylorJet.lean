import Proof.NormalFrameRadialRotationGraph
import Proof.NormalizedRadialRepresentativeUniqueness
import Proof.AngularCommutatorUniqueness
import Proof.UniformRadialAngularCommutator

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

/-- Uniform point and angular commutator bounds belong to the same master
    Taylor family used by the genuine moving-radius covariant jet estimate. -/
theorem uniform_normalFrame_angular_radial_taylor_jet {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CP CC : ℝ,0 < η ∧ 0 ≤ CP ∧ 0 ≤ CC ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
        (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
        (V : Set NormalFrameParameter) (hV : IsOpen V)
        (hp0 : (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V)
        (hRep : ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap)
        (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
        (hR : ContDiffOn ℝ ∞ R V)
        (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p)))
        (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
          (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
        (hRestrict : ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p))),
      let H := normalFrameRadialTaylorFamily d R
      let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
      ‖H p0‖ ≤ CP*(d.radius y)^2 ∧ ∀ i j : I,
        let C := deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0
        ‖C‖ ≤ CC*(d.radius y)^2 ∧ ∀ f : SphereSobolev 2,
          sphereSobolevRotationL 0 i j (H p0 (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
            sphereSobolevInclusionL 0 (-1) (by norm_num)
              (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+H p0 (sphereSobolevRotationL 2 i j f)) := by
  obtain ⟨η,CP,CC,hη,hCP,hCC,hData⟩ := uniform_actual_radial_angular_commutator hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CP,CC,hη,hCP,hCC,?_⟩
  intro floor hf ε hε hSmall d hd y hy A hA S hS hz V hV hp0 hRep R hR hCoercive hStrong hRestrict
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let H := normalFrameRadialTaylorFamily d R
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  have hField (z : X) (hzBall : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (F p0) z = normalizedFirstNormalCoefficient d y z := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact ((hRep p0 hp0 z (unitBall_subset_closedBall_two hzBall)).eq_of_nhds).trans
      (normalFrameNormalizedCoefficient_framed d.γ d.g₁ d.expMap d.frame y z (d.radius y))
  have hPointH : H p0 = R p0-d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num)) :=
    hd.1.normalFrameRadialTaylorFamily_actual hΩ (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy) R
  have hAll (i j : I) : ‖H p0‖ ≤ CP*(d.radius y)^2 ∧
      ‖deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤ CC*(d.radius y)^2 ∧
      ∀ f : SphereSobolev 2,sphereSobolevRotationL 0 i j (H p0 (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0 (sphereSobolevInclusionL 2 1 (by norm_num) f)+
            H p0 (sphereSobolevRotationL 2 i j f)) := by
    obtain ⟨R0,C0,hR0,hPointN,hC0,hGraph0⟩ := hData floor hf ε hε hSmall d hd y hy i j
    have hEq := actual_midpoint_eq_of_normalized_restriction d y R0 (R p0) (F p0) hR0 hField (hStrong p0 hp0) (hRestrict p0 hp0)
    have hP : R0-d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num)) = H p0 := by
      rw [hEq]
      exact hPointH.symm
    have hOldGraph (f : SphereSobolev 2) : sphereSobolevRotationL 0 i j (H p0 (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num) (C0 (sphereSobolevInclusionL 2 1 (by norm_num) f)+H p0 (sphereSobolevRotationL 2 i j f)) := by
      simpa only [hP] using hGraph0 f
    have hNewGraph (f : SphereSobolev 2) := hd.1.normalFrame_radial_taylor_rotation_distribution hΩ
      (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy) A hA S hS hz V hV hp0 hRep R hR hCoercive hStrong hRestrict i j f
    have hCEq := radial_rotation_commutator_unique i j (H p0)
      (deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0) C0 hNewGraph hOldGraph
    refine ⟨?_,?_,hNewGraph⟩
    · rw [hP] at hPointN
      exact hPointN
    · rw [hCEq]
      exact hC0
  exact ⟨(hAll 0 0).1,fun i j => (hAll i j).2⟩

end ShrinkingSpheres
