import Proof.PhysicalCorrectionStrongHalfData
import Proof.UniformPrincipalFirstCorrectionCoordinateData
import Proof.UniformPrincipalFirstCorrectionCoordinateCoarseTwoJets
import Proof.PhysicalFirstCoordinateCoarse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- The complete weighted coordinate geometric correction has a genuine
strong half-domain covariant derivative, with the original epsilon bound. -/
theorem uniform_principal_first_correction_coordinate_strong_half_derivative
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ CE : ℝ,0 ≤ CE ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ b i : I,
      ∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        halfOperatorCovariantDerivativeL d
          (fun x => principalFirstCorrectionCoordinateHalfL d x b)
          (fun x => principalFirstCorrectionCoordinateHigherL d x b) y (axis i)=
          L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧ ‖L‖ ≤ CE*ε := by
  classical
  obtain ⟨QS,hQS,hStrong⟩ := uniform_physical_first_correction_strong_half_data hY hΩ hm K ρ c₀ M Cj hK
  let QB := physicalFirstCorrectionHalfBudget K (M 0) (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  let Q := QB+QS
  let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let CE := 6*B*Q
  have hQB : 0 ≤ QB := physicalFirstCorrectionHalfBudget_nonneg _ _ _ _ _ (zero_le_one.trans hK)
  have hQ : 0 ≤ Q := add_nonneg hQB hQS
  have hB : 0 ≤ B := principalFirstErrorCoordinateWeightBudget_nonneg _ _ (zero_le_one.trans hK) (abs_nonneg _)
  have hQBQ : QB ≤ Q := le_add_of_nonneg_right hQS
  have hQSQ : QS ≤ Q := le_add_of_nonneg_left hQB
  refine ⟨CE,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hε1 d hd y hy b i
  let Lo := fun (a : I) (x : X) => physicalFirstCorrectionHalfL d x (axis a)
  let Hi := fun (a : I) (x : X) => physicalFirstCorrectionHigherL d x (axis a)
  let w := fun (a : I) => principalFirstErrorCoordinateWeight d a b
  have hData (a : I) := hd.physicalFirstCorrection_half_data hY hΩ hm hK hf hε hε1 a
  have hWS (a : I) := hd.contDiffOn_principalFirstErrorCoordinateWeight (zero_lt_one.trans_le hK) a b
  choose D hD hDN using fun a : I => hStrong floor hf ε hε hε1 d hd y hy a i
  let L := fun a : I => directionalFDeriv (axis i) (w a) y • Lo a y+w a y • D a
  have hEach (a : I) : halfOperatorCovariantDerivativeL d
      (fun x => w a x • Lo a x) (fun x => w a x • Hi a x) y (axis i)=
      (L a).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
    half_covariant_strong_smul d (w a) (Lo a) (Hi a) y (axis i)
      ((hWS a).contDiffAt (hY.mem_nhds hy)) ((hData a).1.contDiffAt (hY.mem_nhds hy)) (D a) (hD a)
  have hSum := half_covariant_strong_sum_three d
    (fun a x => w a x • Lo a x) (fun a x => w a x • Hi a x) y (axis i)
    (fun a => ((hWS a).smul (hData a).1).contDiffAt (hY.mem_nhds hy)) L hEach
  have hGerm : (fun x => principalFirstCorrectionCoordinateHalfL d x b) =ᶠ[𝓝 y]
      (fun x => ∑ a : I,w a x • Lo a x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact principalFirstCorrectionCoordinateHalfL_eq d x (hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)) b
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hOne (a : I) : ‖L a‖ ≤ 2*B*Q*ε := by
    have hw := hd.principalFirstErrorCoordinateWeight_small_bounds hY (by omega) hK hf hε hε1 hy a b i
    have hW : |w a y| ≤ B*ε := hw.1.trans (div_le_self (mul_nonneg hB hε) hβ)
    have hC : ‖Lo a y‖ ≤ Q := ((hData a).2.2 y hy).1.trans hQBQ
    have hN : ‖D a‖ ≤ Q := (hDN a).trans hQSQ
    have h0 : ‖directionalFDeriv (axis i) (w a) y • Lo a y‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hw.2 hC (norm_nonneg _) (mul_nonneg hB hε)
    have h1 : ‖w a y • D a‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hW hN (norm_nonneg _) (mul_nonneg hB hε)
    exact ((norm_add_le _ _).trans (add_le_add h0 h1)).trans_eq (by ring)
  refine ⟨∑ a : I,L a,?_,?_⟩
  · rw [halfOperatorCovariantDerivativeL_congr_germ d _ _
      (fun x => principalFirstCorrectionCoordinateHigherL d x b) y (axis i) hGerm]
    convert hSum using 1
    rfl
  · exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun a _ => hOne a)).trans_eq
      (by simp only [Fin.sum_univ_three,CE];ring))

/-- The SAME smooth coarse coordinate correction jets retain that strong
half-domain graph. All families are fixed before every test. -/
theorem uniform_principal_first_correction_coordinate_strong_half
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 8 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ∀ y ∈ Y,
          CoarseCovariantRotationGraph d y (axis i) (principalFirstCorrectionCoordinateCoarseL d b) (S b i y) ∧
          ∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
            (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b i y)=
              L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧ ‖L‖ ≤ CE*ε := by
  obtain ⟨CE,hCE,hStrong⟩ := uniform_principal_first_correction_coordinate_strong_half_derivative
    hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨η,CS,hη,hη1,hCS,hJets⟩ := uniform_principal_first_correction_coordinate_coarse_two_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨C0,hC0,hCoeff⟩ := uniform_principal_first_correction_coordinate_data hY hΩ (by omega) K ρ c₀ M Cj hK
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd
  have hε1 := hSmall.trans hη1
  obtain ⟨S,hS⟩ := hJets floor hf ε hε hSmall d hd
  refine ⟨S,?_⟩
  intro b i
  refine ⟨(hS b i).1,?_⟩
  intro y hy
  obtain ⟨L,hL,hLN⟩ := hStrong floor hf ε hε hε1 d hd y hy b i
  have hH := hd.principalFirstCorrectionCoordinateCoarse_smooth hY hΩ (zero_lt_one.trans_le hK) b
  have hC := (hCoeff floor hf ε hε hε1 d hd b).1
  have hLow : ∀ᶠ x in 𝓝 y,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (principalFirstCorrectionCoordinateCoarseL d b x)=
      (principalFirstCorrectionCoordinateHalfL d x b).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact principalFirstCorrectionCoordinate_coarse_low_compatible d x
      (hd.1.2.2.2.2.2.2.2 x (hSub hx)) b
  have hWeak := halfOperatorCovariantDerivativeL_eq_coarse (principalFirstCorrectionCoordinateCoarseL d b)
    (fun x => principalFirstCorrectionCoordinateHalfL d x b) (fun x => principalFirstCorrectionCoordinateHigherL d x b)
    (S b i y) ((hH.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hC.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hLow
    (principalFirstCorrectionCoordinate_coarse_high_compatible d y b) ((hS b i).2 y hy).1
  exact ⟨((hS b i).2 y hy).1,L,coarse_half_endpoint_of_weak_strong (S b i y) L (hWeak.symm.trans hL),hLN⟩

end ShrinkingSpheres
