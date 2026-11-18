import Proof.LocalCommonSupportCoefficientFamily
import Proof.CommonSupportPoissonRegularity
import Proof.EnlargedFramedEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 20
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- Actual geometric coefficients have local common-support Poisson families,
    smooth as genuine Sobolev operators. The shared joint germs cover the whole
    closed normal ball and hold for every center in the same open neighborhood. -/
theorem uniform_actual_normal_local_poisson_family {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),
      ∃ A : X × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ S : Set X,∃ hS : IsCompact S,
      ∃ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∃ V : Set X,IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧
        (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (p,z)]
          (fun q : X × X => principalCoefficient (framedNormalMetric g d.frame d.expMap q.1
            (d.radius q.1)) q.2)) ∧
        (∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
          (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible) ∧
        ContDiffOn ℝ ∞ (fun p => strongPoissonL (commonSupportMatrixFamily 2 A hA S hS hz p)) V ∧
        ContDiffOn ℝ ∞ (fun p => actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p)) V := by
  obtain ⟨ηF,hηF,hFamily⟩ := uniform_actual_normal_local_coefficient_family hY hΩ hm K ρ c₀ M Cj
    hK hρ 2 (by norm_num)
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηF ηE,lt_min hηF hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem
  have hFam := hFamily floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy g hmem
  obtain ⟨A,hA,S,hS,hz,V,hV,hyV,hVY,hRep⟩ := hFam
  have hK' : 1 ≤ 4*K^2 := by nlinarith [sq_nonneg (K-1)]
  have hInv (p : X) (hp : p ∈ V) : (strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible := by
    have hEll := hElliptic floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd p (hVY hp) g hmem
    have hUE := (hEll.principalCoefficient_tau hK').mono_set unitBall_subset_closedBall_two
    apply strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    refine ⟨hUE.1,hUE.2.1,?_⟩
    intro z hzBall
    simp only [(hRep p hp z (unitBall_subset_closedBall_two hzBall)).eq_of_nhds]
    exact hUE.2.2 hzBall
  exact ⟨A,hA,S,hS,hz,V,hV,hyV,hVY,hRep,hInv,
    contDiffOn_commonSupport_strongPoissonL A hA S hS hz V hInv,
    contDiffOn_commonSupport_highRadialErrorL A hA S hS hz V hInv⟩

end ShrinkingSpheres
