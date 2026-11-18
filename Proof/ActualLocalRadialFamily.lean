import Proof.ActualLocalPoissonFamily
import Proof.CommonSupportLowRadialRegularity
import Proof.NativeWeakInverseBound
import Proof.Archive.SphereSobolevCompatibleInterpolationTopology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Actual geometric low/high radial endpoints admit one compatible smooth
    interpolated H1-to-L2 family on a common open center neighborhood. -/
theorem uniform_actual_normal_local_radial_family {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A : X × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ S : Set X,∃ hS : IsCompact S,
      ∃ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∃ V : Set X,IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧
        (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (p,z)]
          (fun q : X × X => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap q.1
            (d.radius q.1)) q.2)) ∧
        ∃ R : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,ContDiffOn ℝ ∞ R V ∧
          ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
              (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p)) := by
  obtain ⟨ηP,hηP,hPoisson⟩ := uniform_actual_normal_local_poisson_family hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηP ηE,lt_min hηP hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hP := hPoisson floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy d.g₁ (by simp)
  obtain ⟨A,hA,S,hS,hz,V,hV,hyV,hVY,hRep,hStrong,hPoissonSmooth,hHighSmooth⟩ := hP
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  have hK' : 1 ≤ 4*K^2 := by nlinarith [sq_nonneg (K-1)]
  have hUE (p : X) (hp : p ∈ V) : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set X)
      (fun z => A (p,z)) ((metricDensityBudget (4*K^2))⁻¹*(4*K^2)⁻¹)
        (metricDensityBudget (4*K^2)*(4*K^2)) := by
    have hEll := hElliptic floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd p (hVY hp) d.g₁ (by simp)
    have hU := (hEll.principalCoefficient_tau hK').mono_set unitBall_subset_closedBall_two
    refine ⟨hU.1,hU.2.1,?_⟩
    intro z hzBall
    simp only [(hRep p hp z (unitBall_subset_closedBall_two hzBall)).eq_of_nhds]
    exact hU.2.2 hzBall
  have hMeas (p : X) : AEStronglyMeasurable (fun z => A (p,z))
      ((volume : Measure X).restrict ballOpens) :=
    (hA.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hCoercive (p : X) (hp : p ∈ V) : IsCoercive
      (TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X)) (Omega:=ballOpens)
        (a:=fun z => A (p,z)) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) (commonSupportEnergyMemLp A hA p)) :=
    isCoercive_unitBall_zeroDrift (hUE p hp) (hMeas p) (commonSupportEnergyMemLp A hA p)
  have hWeak (p : X) (hp : p ∈ V) : (commonSupportZeroWeakEnergy A hA p).IsInvertible :=
    isInvertible_of_bilinear_coercive _ (hCoercive p hp)
  have hNormal (p : X) (hp : p ∈ V) : (negativeBoundaryCoefficientMulL (normalCoefficientJet (F p))).IsInvertible := by
    apply negativeNormalCoefficient_isInvertible (F p) (normalCoefficientJet (F p))
      (coefficientSmoothData_normalCoefficientJet (F p)) _ _
    simpa only [F,coefficientMatrixField_commonSupportMatrixFamily] using hUE p hp
  let T : X → SphereSobolevEndpointPair := fun p =>
    (commonSupportLowRadialErrorL A hA S hS hz p,actualHighRadialErrorL (F p))
  have hCompatible (p : X) (hp : p ∈ V) : T p ∈ sphereSobolevCompatibleEndpoints := by
    have hPoint (z : X) (hzBall : z ∈ (ballOpens : Set X)) : coefficientMatrixField 2 (F p) z = A (p,z) := by
      simp only [F,coefficientMatrixField_commonSupportMatrixFamily]
    have hCompat := actual_radial_endpoints_compatible (commonSupportEnergyMemLp A hA p)
      (hCoercive p hp) (F p) hPoint (hStrong p hp) (hNormal p hp)
    have hIndex : (-1/2:ℝ) = -(1/2:ℝ) := by ring
    have hI := sphereSobolevInclusionL_eq_of_target_eq (1/2:ℝ) (-1/2:ℝ) (-(1/2:ℝ))
      (by norm_num) (by norm_num) hIndex
    exact (congrArg (fun J : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      J.comp (actualHighRadialErrorL (F p))) hI).trans hCompat
  have hLowSmooth := contDiffOn_commonSupportLowRadialErrorL A hA S hS hz V hWeak hNormal
  have hSmoothT : ContDiffOn ℝ ∞ T V := hLowSmooth.prodMk hHighSmooth
  let R := sphereSobolevCompatibleInterpolationFamily T V hCompatible
  refine ⟨A,hA,S,hS,hz,V,hV,hyV,hVY,hRep,R,
    contDiffOn_sphereSobolevCompatibleInterpolationFamily T V hV hCompatible hSmoothT,?_⟩
  intro p hp
  rw [show R p = sphereSobolevMidpointL (T p).1 (T p).2 (hCompatible p hp) from
    sphereSobolevCompatibleInterpolationFamily_of_mem T V hCompatible p hp]
  exact sphereSobolevMidpointL_inclusion (T p).1 (T p).2 (hCompatible p hp)

end ShrinkingSpheres
