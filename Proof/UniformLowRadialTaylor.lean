import Proof.WeakConormalFirstNorm
import Proof.BoundaryAffineRemainder
import Proof.RadialFirstVariationBound
import Proof.ActualLowRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativePolynomialBulkMoments

def lowFirstRadialVariationL (c : ℝ) (F1 : SmoothCoefficientMatrix 2)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  c⁻¹ • (weakFirstConormalVariationL c (coefficientMatrixField 2 F1) ha1-
    (negativeBoundaryCoefficientMulL (normalCoefficientJet F1)).comp fixedLowRadialL)

/-- The genuine low radial endpoint has a common quadratic remainder after
    subtracting the affine first conormal/radial variation. -/
theorem uniform_actual_low_radial_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CL : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CL ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
      let KP := 4*K^2
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let ℓ := firstDensityCenterLinearL d y
      ∃ F0 F F1 : SmoothCoefficientMatrix 2,
      ∃ e : NativeWeakEnergyData a (5*metricDensityBudget KP*KP) (metricDensityBudget KP*KP),
      ∃ ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
        ((volume:Measure X).restrict ballOpens),
        (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j)) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => ℓ z*(1:Mat) i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible ∧
        (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible ∧
        ‖lowFirstRadialVariationL c F1 ha1‖ ≤ CB ∧
        ‖actualLowRadialErrorL a e.coefficient_bound F-d.radius y • lowFirstRadialVariationL c F1 ha1‖ ≤ CL*(d.radius y)^2 := by
  obtain ⟨ηW,P,Q,CP1,CP2,F0,hηW,hP,hQ,hCP1,hCP2,hF0,hWeak⟩ :=
    uniform_actual_weak_poisson_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let DA := metricDensityBudget (4*K^2)*(4*K^2)
  let N := ‖fixedHarmonicH1LiftL‖
  let CN1 := sphereSurfaceMass⁻¹*((K*CP1+9*P*N)*N)
  let QN := sphereSurfaceMass⁻¹*((DA*CP2+(9*P+9*Q)*CP1+9*Q*N)*N)
  let CM := boundaryHalfMultiplierBudget*36*P
  let QM := boundaryHalfMultiplierBudget*36*Q
  let QT := boundaryHalfMultiplierBudget*78*Q
  let DM := QM+CM
  let CB := K*(CN1+CM*‖fixedLowRadialL‖)
  let CL := (2*K)*(QN+QM*‖fixedLowRadialL‖+QT*∑ j : I,‖fixedSphereTangentialL j‖+DM*CB)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hDA : 0 ≤ DA := by dsimp [DA,metricDensityBudget];positivity
  have hArea : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  have hMult := boundaryHalfMultiplierBudget_nonneg
  have hNnonneg : 0 ≤ N := norm_nonneg _
  have hCN1 : 0 ≤ CN1 := by
    change 0 ≤ sphereSurfaceMass⁻¹*((K*CP1+9*P*N)*N)
    positivity
  have hQN : 0 ≤ QN := by
    change 0 ≤ sphereSurfaceMass⁻¹*((DA*CP2+(9*P+9*Q)*CP1+9*Q*N)*N)
    positivity
  have hCM : 0 ≤ CM := by dsimp [CM];positivity
  have hQM : 0 ≤ QM := by dsimp [QM];positivity
  have hQT : 0 ≤ QT := by dsimp [QT];positivity
  have hDM : 0 ≤ DM := add_nonneg hQM hCM
  have hCB : 0 ≤ CB := by
    change 0 ≤ K*(CN1+CM*‖fixedLowRadialL‖)
    positivity
  have hCL : 0 ≤ CL := by
    change 0 ≤ (2*K)*(QN+QM*‖fixedLowRadialL‖+QT*∑ j : I,‖fixedSphereTangentialL j‖+DM*CB)
    positivity
  let δ := 1/(2*(K*DM+1))
  have hδ : 0 < δ := by dsimp [δ];positivity
  refine ⟨min (min ηW ηE) (min 1 δ),CB,CL,lt_min (lt_min hηW hηE) (lt_min zero_lt_one hδ),hCB,hCL,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  obtain ⟨F,F1,hRep,hRep1,hStrong,hStrong0,hVal1,hDeriv1,hValR,hDerivR,t⟩ :=
    hWeak floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
  let a1 := coefficientMatrixField 2 F1
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let M0 := negativeBoundaryCoefficientMulL (normalCoefficientJet F)
  let M1 := negativeBoundaryCoefficientMulL (normalCoefficientJet F1)
  let N1 := weakFirstConormalVariationL c a1 t.first_coefficient_bound
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hci : c⁻¹ ≤ K := hd.1.firstMetricDensityFactor_inverse_le hKpos (hd.2.1.center_mem hy)
  have hcK : c ≤ K := hd.1.firstMetricDensityFactor_le hKpos (hd.2.1.center_mem hy)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hQrad : 0 ≤ Q*r^2 := mul_nonneg hQ (sq_nonneg _)
  have hN1 : ‖N1‖ ≤ CN1 := norm_weakFirstConormalVariationL_le c t.first_coefficient_bound K P CP1 hKpos.le hP hCP1
    ((flat_native_weak_energy_data c hc).energy_bound.trans hcK) t.first_energy_bound t.first_poisson_bound
  have hNR : ‖nativeWeakConormalEndpoint a 0 0 t.energy.coefficient_bound sphereFischerInner-
      c • fixedLowRadialL-r • N1‖ ≤ QN*r^2 :=
    t.conormal_remainder_bound hr.le hDA hP hQ hCP1 hCP2
  have hM1 : ‖M1‖ ≤ CM := (norm_negative_first_normal_coefficient_le F1 P hP hVal1 hDeriv1).trans_eq (by dsimp [CM];ring)
  have hMR : ‖M0-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-r • M1‖ ≤ QM*r^2 :=
    (norm_negative_normal_affine_remainder_le F F0 F1 c r (Q*r^2) hQrad hF0 hValR hDerivR).trans_eq (by dsimp [QM];ring)
  have hMDiff : ‖M0-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ DM*r :=
    norm_normal_first_difference_le M0 M1 c r QM CM hr.le hr1 hQM hCM hMR hM1
  have hScalar (w : UnitSphere) : coefficientMatrixField 2 F1 w.val = firstDensityCenterLinearL d y w.val • (1:Mat) := by
    have hw2 : w.val ∈ Metric.closedBall (0:X) 2 :=
      Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)
    ext i j
    exact (hRep1 w.val hw2 i j).eq_of_nhds
  have hTang (j : I) : ‖negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)‖ ≤ QT*r^2 :=
    (norm_negative_tangent_affine_remainder_le F F0 F1 c r (Q*r^2) hQrad
      (firstDensityCenterLinearL d y) hF0 hScalar hValR hDerivR j).trans_eq (by dsimp [QT];ring)
  have hEll := hE floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy d.g₁ (by simp)
  have hKP : 1 ≤ 4*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  have hPoint (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F x = a x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hUE := ((hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two).congr hPoint
  have hMInv := negativeNormalCoefficient_isInvertible F (normalCoefficientJet F) (coefficientSmoothData_normalCoefficientJet F) _ _ hUE
  have hNear : c⁻¹*‖M0-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ (1/2:ℝ) := by
    have hεDM : ε*(2*(K*DM+1)) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 2*(K*DM+1))).mp
      (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hb := mul_le_mul hci hMDiff (norm_nonneg _) hKpos.le
    have hb' := mul_le_mul_of_nonneg_left hrε (mul_nonneg hKpos.le hDM)
    nlinarith only [hb,hb',hεDM,hε]
  obtain ⟨hId,hIdNorm⟩ := scalar_identity_inverse_data (SphereSobolev (-(1/2:ℝ))) c hc
  have hMINorm : ‖M0.inverse‖ ≤ 2*K :=
    (inverse_norm_le_twice_of_half_perturbation M0 _ hMInv hId c⁻¹ (inv_nonneg.mpr hc.le) hIdNorm hNear).trans
      (mul_le_mul_of_nonneg_left hci (by norm_num))
  have hFirst : ‖lowFirstRadialVariationL c F1 t.first_coefficient_bound‖ ≤ CB := by
    change ‖c⁻¹ • (N1-M1.comp fixedLowRadialL)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
    exact (mul_le_mul hci ((norm_sub_le _ _).trans (add_le_add hN1
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hM1 (norm_nonneg _)))))
        (norm_nonneg _) hKpos.le)
  refine ⟨F0,F,F1,t.energy,t.first_coefficient_bound,hF0,hRep,hRep1,hStrong,hStrong0,hMInv,hFirst,?_⟩
  exact norm_radialErrorAssembly_first_remainder_le _ N1 fixedLowRadialL M0 M1 _ fixedSphereTangentialL
    c r (2*K) QN QM QT DM CB hc.ne' hr.le (by positivity) hQN hQM hQT hDM hCB
      hMInv hMINorm hNR hMR hTang hMDiff hFirst

end ShrinkingSpheres
