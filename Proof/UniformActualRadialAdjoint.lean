import Proof.UniformConormalOneData
import Proof.CanonicalFirstRadialCorrection
import Proof.ConormalRadialAdjointBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] conormalRadialL conormalRadialAdjointL oneBoundaryCoefficientMulL

/-- A uniform quadratic expansion of the actual radial adjoint, with a
    bounded L2 first correction. The forward map is the genuine Poisson
    radial response and both maps satisfy exact physical L2 adjunction. -/
theorem uniform_actual_midpoint_radial_adjoint_canonical {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CJ : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let B := firstRadialCorrectionL d y
      ∃ F : SmoothCoefficientMatrix 2,
      ∃ D Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x]
          (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ‖B‖ ≤ CB ∧
        ‖Da-sphereSobolevDegreeL-d.radius y • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 ∧
        (∀ u v,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ) ∧
        ∀ f : SphereSobolev (3/2:ℝ),D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
          sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
            (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL F f)) := by
  obtain ⟨ηD,P,Q,CN2,F0,hηD,hP,hQ,hCN2,hF0,hData⟩ :=
    uniform_actual_conormal_one_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  let PG := K^3*|M ⟨1,by omega⟩|
  let CB := 6*K*PG
  let CN1 := K*CB+72*P
  let CM1 := (73*36)*P
  let CI := 2*K
  let CRI := (2*K)*(K*((73*36)*Q)+K^2*((73*36)*P+(73*36)*Q)*((73*36)*P))
  let CT := (73*78)*Q
  let CJ := (2*K+CN1+CN2)*CRI+(CN1+CN2)*(K^2*CM1)+CN2*K+(boundaryTangentialAdjointBudget*CT)*CI
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hPG : 0 ≤ PG := by dsimp [PG];positivity
  have hCB : 0 ≤ CB := by dsimp [CB];positivity
  have hCM1 : 0 ≤ CM1 := by dsimp [CM1];positivity
  have hCI : 0 ≤ CI := by dsimp [CI];positivity
  have hCRI : 0 ≤ CRI := by dsimp [CRI];positivity
  have hCT : 0 ≤ CT := by dsimp [CT];positivity
  have hCJ : 0 ≤ CJ := by
    change 0 ≤ (2*K+(K*CB+72*P)+CN2)*CRI+((K*CB+72*P)+CN2)*(K^2*CM1)+CN2*K+
      (boundaryTangentialAdjointBudget*CT)*CI
    have := boundaryTangentialAdjointBudget_nonneg
    positivity
  refine ⟨min ηD 1,CB,CJ,lt_min hηD zero_lt_one,hCB,hCJ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  dsimp only at hHere
  obtain ⟨F,F1,e,ha1,N,hRep,hRep1,hInv,hInv0,hUE,hV1,hD1,hOne,hN⟩ := hHere
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let ell := firstDensityCenterLinearL d y
  let B := coarseFirstRadialVariationL c ell
  let D := conormalRadialL F N
  let Da := conormalRadialAdjointL F N
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hCenter := hd.2.1.center_mem hy
  have hcK : c ≤ K := hd.1.firstMetricDensityFactor_le hKpos hCenter
  have hciK : c⁻¹ ≤ K := hd.1.firstMetricDensityFactor_inverse_le hKpos hCenter
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  have hEllNorm : ‖ell‖ ≤ PG := by
    have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
    have hEn := hd.1.1.norm_frameVectorLinear_le hK hCenter d.frame hFrame
    have hDeriv := (hd.1.firstMetricDensityFactor_jet_bounds hΩ hKpos (by omega) hCenter).1
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hDeriv hEn (norm_nonneg _) (by positivity)).trans_eq (by dsimp [PG];ring))
  have hcAbs : |c⁻¹| ≤ K := by rw [abs_of_pos (inv_pos.mpr hc)];exact hciK
  have hBNorm : ‖B‖ ≤ CB := (norm_coarseFirstRadialVariationL_le c ell).trans (by
    change 6 * |c⁻¹| * ‖ell‖ ≤ 6*K*PG
    gcongr)
  have hAdjoint : ‖Da-sphereSobolevDegreeL-r • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*r^2 :=
    conormalRadialAdjoint_remainder_bound e.coefficient_bound F F0 F1 c r K P CB CN2 (2*K) ((73*36)*P) ((73*36)*Q)
      ((2*K)*((73*36)*P+(73*36)*Q)*K) CRI CT hc hcK hciK hr.le hr1 hKpos.le hP hCB hCN2 hCI hCM1 hCRI hCT ell
      hF0 (fun x hx i j => (hRep1 x hx i j).eq_of_nhds) ha1 hInv0 hV1 hD1 hBNorm hOne N hN
  have hPos (w : UnitSphere) : 0 < (boundaryNormalCoefficientData F).1 w.val :=
    boundaryNormalCoefficientData_pos F _ _ hUE w
  have hPoint (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F x =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  exact ⟨F,D,Da,hRep,hInv,hBNorm,hAdjoint,conormalRadialL_adjoint F N hPos hN.symmetric,
    conormalRadialL_high e.coefficient_bound e.coercive F N hPoint hInv hPos hN.weak_compatible⟩

/-- Existential compatibility interface, retaining the original public claim.
    The stronger producer above uses the explicit canonical correction. -/
theorem uniform_actual_midpoint_radial_adjoint_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CJ : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ F : SmoothCoefficientMatrix 2,
      ∃ D Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ B : SphereSobolev 0 →L[ℝ] SphereSobolev 0,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x]
          (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ‖B‖ ≤ CB ∧
        ‖Da-sphereSobolevDegreeL-d.radius y • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 ∧
        (∀ u v,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ) ∧
        ∀ f : SphereSobolev (3/2:ℝ),D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
          sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
            (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL F f)) := by
  have hTheorem := uniform_actual_midpoint_radial_adjoint_canonical (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CB,CJ,hη,hCB,hCJ,hProduce⟩ := hTheorem
  refine ⟨η,CB,CJ,hη,hCB,hCJ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hProduce floor hf ε hε hSmall d hd y hy
  dsimp only at hHere
  obtain ⟨F,D,Da,hRep,hInv,hB,hTaylor,hPair,hHigh⟩ := hHere
  exact ⟨F,D,Da,firstRadialCorrectionL d y,hRep,hInv,hB,hTaylor,hPair,hHigh⟩

end ShrinkingSpheres
