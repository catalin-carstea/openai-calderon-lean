import Proof.UniformEffectiveFirstBalancedDerivative
import Proof.UniformEffectiveFirstEndpointData
import Proof.HigherStrongFirstDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalFirstCommutatorPacket.effectiveAdjointCovariantDerivative
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (W : PhysicalFirstCommutatorPacket P CB CS ε) (b i : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  halfOperatorCovariantDerivativeL d (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint)
    (W.covariantCoordinateAdjointHigher b) y (axis i)

lemma abs_higher_strong_first_pairing_le
    (A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (F : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {CA CD ε β : ℝ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hA : ‖A‖ ≤ CA*ε/β) (hL : ‖L‖ ≤ CD*ε)
    (hF : F=L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (u v : SphereSobolev (3/2:ℝ)) :
    |sphereSobolevDualPairing (1/2:ℝ) (A u) (F v)| ≤
      (CA*CD)*ε^2*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v‖*‖u‖ := by
  have hAN : ‖A u‖ ≤ (CA*ε)*‖u‖ :=
    (A.le_opNorm u).trans (mul_le_mul_of_nonneg_right
      (hA.trans (div_le_self (mul_nonneg hCA hε) hβ)) (norm_nonneg _))
  have hFN : ‖F v‖ ≤ (CD*ε)*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v‖ := by
    rw [hF,ContinuousLinearMap.comp_apply]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  exact (abs_sphereSobolevDualPairing_le _ _ _).trans
    ((mul_le_mul hAN hFN (norm_nonneg _) (by positivity)).trans_eq (by ring))

/-- One actual full-first derivative/coefficient product sector is
integrable and has the original physical energy bound. This uses the
literal coefficient and true adjoint derivative of ANY already selected
packet; no higher witness is assumed measurable. -/
theorem uniform_effective_first_adjoint_derivative_product_integral
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ CB CS : ℝ,
      ∀ W : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ b c i j : I,∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
        IntegrableOn (D.higherStrongFirstDensity (P.firstCovariantCoordinateHigherL c)
          (W.effectiveAdjointCovariantDerivative b i) j) Y ∧
        |∫ y in Y,D.higherStrongFirstDensity (P.firstCovariantCoordinateHigherL c)
          (W.effectiveAdjointCovariantDerivative b i) j y| ≤
            CE*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨ηA,CA,hηA,hηA1,hCA,hEndpoint⟩ := uniform_effective_first_higher_endpoint_data
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hDerivative⟩ := uniform_effective_first_balanced_derivative_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets
    hY hΩ (by omega) K ρ c₀ M Cj hK
  let CE := CA*CD
  have hCE : 0 ≤ CE := mul_nonneg hCA hCD
  refine ⟨min ηA ηD,CE,lt_min hηA hηD,(min_le_left _ _).trans hηA1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P CB CS W b c i j φ E D hφ
  have hε1 := hSmall.trans ((min_le_left _ _).trans hηA1)
  have hA := hEndpoint floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P c
  have hJet := hDerivative floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P CB CS W
  have hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y := (hWeight floor hf ε hε hε1 d hd b).1
  have hg : Elliptic Y K d.γ :=
    ⟨fun a e => (hd.1.1.1 a e).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (a : I) : ContDiffOn ℝ ∞ (fun x => d.frame x a) Y := (hd.1.2.2.2.2.2.2.1 a).mono hSub
  have hFrame : ∀ y ∈ Y,∀ a e,metricPair d.γ y (d.frame y a) (d.frame y e)=if a=e then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hF : ContDiffOn ℝ ∞ (W.effectiveAdjointCovariantDerivative b i) Y :=
    contDiffOn_halfOperatorCovariantDerivativeL hY d hg (zero_lt_one.trans_le hK) he _ _
      (P.firstCovariantCoordinateAdjoint_smooth hd hY hΩ (zero_lt_one.trans_le hK) b hw)
      (W.covariantCoordinateAdjointHigher_smooth hd b hw) i
  have hMeas := D.higherStrongFirstDensity_aestronglyMeasurable hY hg (zero_lt_one.trans_le hK)
    (P.firstCovariantCoordinateHigherL c) (W.effectiveAdjointCovariantDerivative b i) hA.1 hF j
  have hBound : ∀ᵐ y ∂volume.restrict Y,
      ‖D.higherStrongFirstDensity (P.firstCovariantCoordinateHigherL c)
        (W.effectiveAdjointCovariantDerivative b i) j y‖ ≤
        (CE*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    obtain ⟨L,H,hForward,hAdj,hHigh,hLN,hAdjN,hHN⟩ := hJet y hy b i
    rw [Real.norm_eq_abs]
    apply D.abs_higherStrongFirstDensity_le hFrame _ _ j hy hCE (sq_nonneg ε) (zero_lt_one.trans_le hβ)
    intro u v
    exact abs_higher_strong_first_pairing_le _ _ L.adjoint hCA hCD hε hβ
      (hA.2 y hy) hAdjN hAdj u v
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CE*ε^2)
  refine ⟨hDom.mono' hMeas hBound,?_⟩
  have hIntegral := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hIntegral

end ShrinkingSpheres
