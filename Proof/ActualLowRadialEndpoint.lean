import Proof.UniformBoundaryCoefficientData
import Proof.FlatConormalRadialTrace
import Proof.LowRadialPerturbation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

abbrev fixedSphereTangentialL (j : I) :=
  sphereTangentialDerivativeL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics j

/-- The low regularity radial error is obtained from the actual weak conormal
    solution and the exact normal/tangential coefficient decomposition. -/
def actualLowRadialErrorL (a : X → Mat)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens)) (F : SmoothCoefficientMatrix 2) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  radialErrorAssembly (nativeWeakConormalEndpoint a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner)
    (negativeBoundaryCoefficientMulL (normalCoefficientJet F)) fixedLowRadialL
    (fun j => negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)) fixedSphereTangentialL

/-- A common H1/2-to-H-1/2 radial error bound for the genuine normal chart.
    The required inverses and conormal comparison are consequences of the
    frozen geometry, with no additional analytic premise. -/
theorem uniform_actual_low_radial_endpoint {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CL : ℝ,0 < η ∧ 0 ≤ CL ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
      let KP := 4*K^2
      let C := 5*metricDensityBudget KP*KP
      let D := metricDensityBudget KP*KP
      ∃ F : SmoothCoefficientMatrix 2,∃ e : NativeWeakEnergyData (principalCoefficient H) C D,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
          coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => principalCoefficient H z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible ∧
        ‖actualLowRadialErrorL (principalCoefficient H) e.coefficient_bound F‖ ≤ CL*d.radius y := by
  obtain ⟨ηB,CI,CN,CT,hηB,hCI,hCN,hCT,hBoundary⟩ :=
    uniform_actual_boundary_coefficient_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,CC,hηW,hCC,hWeak⟩ := uniform_actual_weak_conormal_comparison
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  let CL := CI*(CC+CN*‖fixedLowRadialL‖+CT*∑ j : I,‖fixedSphereTangentialL j‖)
  have hCL : 0 ≤ CL := by dsimp [CL];positivity
  refine ⟨min ηB ηW,CL,lt_min hηB hηW,hCL,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  obtain ⟨F,c,hcBounds,hc,hScalar,hRep,hUE,hInv,hNormal,hTangent⟩ :=
    hBoundary floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨cw,hcwBounds,hcw,hScalarw,e,hConormal⟩ :=
    hWeak floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
  have hcEq : cw = c := by
    have hh := congrArg (fun A : Mat => A 0 0) (hScalarw.symm.trans hScalar)
    simpa [Matrix.smul_apply,Matrix.one_apply] using hh
  subst cw
  rw [nativeWeakConormal_flat_eq_smul] at hConormal
  have hStrong := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity 0 F hUE
  have hNormalInv := negativeNormalCoefficient_isInvertible F (normalCoefficientJet F)
    (coefficientSmoothData_normalCoefficientJet F) _ _ hUE
  refine ⟨F,e,hRep,hStrong,hNormalInv,?_⟩
  exact norm_radialErrorAssembly_le _ _ _ _ _ c (d.radius y) CI CC CN CT
    (hd.2.2.2.2.1.2 y hy).1.le hCI hCC hCN hCT hInv hConormal hNormal hTangent

end ShrinkingSpheres
