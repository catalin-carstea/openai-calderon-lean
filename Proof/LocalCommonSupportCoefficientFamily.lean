import Proof.JointMetricCoefficientRegularity
import Proof.GeneralLocalCommonSupportFamily
import Proof.Archive.CommonSupportMatrixInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.EnergyBridge

/-- A genuine smooth local coefficient field has one joint smooth compact
    representative, one spatial support, and a common center neighborhood.
    Agreement is a joint germ along every point of the entire closed ball. -/
theorem exists_local_commonSupport_matrix_family {Y : Set X} (hY : IsOpen Y)
    (a : X × X → Mat) (L : ℝ) (hL : 0 ≤ L)
    (ha : ContDiffOn ℝ ∞ a (Y ×ˢ Metric.ball (0:X) (L+1))) {y : X} (hy : y ∈ Y) :
    ∃ A : X × X → Mat,ContDiff ℝ ∞ A ∧ ∃ K : Set X,IsCompact K ∧
      (∀ p z,z ∉ K → A (p,z) = 0) ∧ ∃ V : Set X,IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧
      ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) L,A =ᶠ[𝓝 (p,z)] a := by
  have hSub : {y} ×ˢ Metric.closedBall (0:X) L ⊆ Y ×ˢ Metric.ball (0:X) (L+1) := by
    intro p hp
    have hpy : p.1 = y := hp.1
    refine ⟨hpy ▸ hy,?_⟩
    have hz : dist p.2 0 ≤ L := hp.2
    change dist p.2 0 < L+1
    linarith
  exact exists_local_commonSupport_matrix_family_on_open hY a L
    (Y ×ˢ Metric.ball (0:X) (L+1)) (hY.prod Metric.isOpen_ball) ha hy hSub

/-- The actual normalized geometric divergence coefficients admit smooth
    common-support parameter families near every admitted center. -/
theorem uniform_actual_normal_local_coefficient_family {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),
      ∃ A : X × X → Mat,ContDiff ℝ ∞ A ∧ ∃ S : Set X,IsCompact S ∧
        (∀ p z,z ∉ S → A (p,z) = 0) ∧ ∃ V : Set X,IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧
        ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) L,A =ᶠ[𝓝 (p,z)]
          (fun q : X × X => principalCoefficient (framedNormalMetric g d.frame d.expMap q.1
            (d.radius q.1)) q.2) := by
  obtain ⟨η,hη,hRegular⟩ := uniform_framed_normal_coefficient_joint_regular hY hΩ hm K ρ c₀ M Cj
    hK hρ (L+1) (by positivity)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem
  let a : X × X → Mat := fun q => principalCoefficient (framedNormalMetric g d.frame d.expMap q.1
    (d.radius q.1)) q.2
  have ha : ContDiffOn ℝ ∞ a (Y ×ˢ Metric.ball (0:X) (L+1)) := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j q hq
    exact (hRegular floor hf ε hε hSmall d hd q.1 hq.1 g hmem q.2
      (Metric.ball_subset_closedBall hq.2) i j).contDiffWithinAt
  exact exists_local_commonSupport_matrix_family hY a L hL ha hy

end ShrinkingSpheres
