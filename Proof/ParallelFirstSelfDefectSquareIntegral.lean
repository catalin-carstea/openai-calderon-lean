import Proof.ParallelFirstSelfDefectHigherBound
import Proof.ParallelFirstSelfConditional
import Proof.HalfCovariantEnergyControl

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma half_mass_sq_le_direction_energy (d : Data) (U : X → SphereSobolev (3/2:ℝ))
    (y a : X) {β : ℝ} (hβ : 1 ≤ β) :
    ‖U y‖^2 ≤ halfCovariantDirectionEnergy d U y β a := by
  have h1 := mul_le_mul_of_nonneg_right hβ (sq_nonneg ‖U y‖)
  have h2 := mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hβ))
    (sq_nonneg ‖halfSectionCovariantDerivativeL d U y a‖)
  dsimp only [halfCovariantDirectionEnergy]
  linarith only [h1,h2]

/-- The two common H3/2 masses are bounded by the original physical
energy; no norm of a chosen higher adjoint output enters. -/
lemma first_self_complex_mass_density_le {Y : Set X} {d : Data} {K : ℝ}
    (hY : IsOpen Y) (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (hFrame : ∀ x ∈ Y,∀ j k,metricPair d.γ x (d.frame x j) (d.frame x k)=if j=k then 1 else 0)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : Test Y d.γ d.frame φ) {y : X} (hy : y ∈ Y) (hβ : 1 ≤ beta d.γ d.radius y) :
    metricDensity d.γ y*(‖E.realSobolevSection (3/2:ℝ) (by norm_num) y‖^2+
      ‖E.imagSobolevSection (3/2:ℝ) (by norm_num) y‖^2) ≤
      (3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  have hR := half_mass_sq_le_direction_energy d (E.realSobolevSection (3/2:ℝ) (by norm_num)) y (axis 0) hβ
  have hI := half_mass_sq_le_direction_energy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y (axis 0) hβ
  exact (mul_le_mul_of_nonneg_left (add_le_add hR hI) (Real.sqrt_nonneg _)).trans
    (D.half_covariant_direction_energy_le hY hg hK he hFrame hφ.1 hy 0)

/-- Uniform bound for the EXACT defect-square premise of the first-self
core split. The stronger epsilon-squared factor is retained. -/
theorem uniform_first_self_defect_square_integral_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CB CG CK : ℝ)
    (hCB : 0 ≤ CB) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ η CD : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CD ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CS : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
      IntegrableOn (firstSelfDefectSquareComplexDensity P WF W E) Y ∧
        |∫ y in Y,firstSelfDefectSquareComplexDensity P WF W E y| ≤
          CD*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,CR,hη,hη1,hCR,hDefect⟩ := uniform_first_adjoint_defect_higher_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB hCB
  let CD := CR^2*(3*K^2+1)
  refine ⟨η,CD,hη,hη1,by dsimp only [CD];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CS P WF W φ E D hφ
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hInt := (firstSelf_complex_core_split_integrableOn hY hΩ hSub hd
    (zero_lt_one.trans_le hK) P WF W hCG hCK E).2.2
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖firstSelfDefectSquareComplexDensity P WF W E y‖ ≤
      (CD*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) :
        ‖firstAdjointDefectCoreSection P WF W U y‖^2 ≤
          (CR^2*ε^2)*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 := by
      obtain ⟨R,hR,hRN⟩ := hDefect floor hf ε hε hSmall d hd CF CT CS CG CK P WF W U hU y hy
      have hN : ‖firstAdjointDefectCoreSection P WF W U y‖ ≤ CR*ε*
          ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖ := by
        rw [hR]
        exact ((sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).le_opNorm R).trans
          (((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg R)).trans_eq
            (one_mul _)).trans hRN)
      exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hN).trans_eq (by ring)
    have hR := hPoint (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
      (E.contDiff_realHigherSobolevSection _ _).contDiffOn
    have hI := hPoint (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
      (E.contDiff_imagHigherSobolevSection _ _).contDiffOn
    rw [E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num)] at hR
    rw [E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num)] at hI
    have hMass := first_self_complex_mass_density_le hY hg hK he hFrame E D hφ hy hβ
    have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs,abs_of_nonneg (by
      unfold firstSelfDefectSquareComplexDensity firstSelfDefectSquareDensity
      positivity)]
    dsimp only [firstSelfDefectSquareComplexDensity,firstSelfDefectSquareDensity]
    calc
      _ ≤ metricDensity d.γ y*((CR^2*ε^2)*‖E.realSobolevSection (3/2:ℝ) (by norm_num) y‖^2)+
          metricDensity d.γ y*((CR^2*ε^2)*‖E.imagSobolevSection (3/2:ℝ) (by norm_num) y‖^2) :=
        add_le_add (mul_le_mul_of_nonneg_left hR hμ) (mul_le_mul_of_nonneg_left hI hμ)
      _ = (CR^2*ε^2)*(metricDensity d.γ y*(‖E.realSobolevSection (3/2:ℝ) (by norm_num) y‖^2+
          ‖E.imagSobolevSection (3/2:ℝ) (by norm_num) y‖^2)) := by ring
      _ ≤ (CR^2*ε^2)*((3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
        mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = _ := by dsimp only [CD];ring
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CD*ε^2)
  refine ⟨hInt,?_⟩
  have hN := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hN

end ShrinkingSpheres.ParallelEnergy
