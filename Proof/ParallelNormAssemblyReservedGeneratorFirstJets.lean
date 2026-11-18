import Proof.ParallelNormAssemblyReservedNormalizedHigherFirst
import Proof.ParallelNormAssemblyReservedNormalizedErrorJets
import Proof.ParallelNormAssemblyReservedRaisingJets
import Proof.ParallelScalarFirstRaisingHalfTwoJets
import Proof.UniformPrincipalModelCovariantHigher
import Proof.DegreeHalfCovariantData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma normalized_potential_generators_smooth {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (a : PhysicalPotentialGeneratorIndex) :
    ContDiffOn ℝ ∞ (fun x => normalizedPotentialGeneratorLow P x a) Y ∧
      ContDiffOn ℝ ∞ (fun x => normalizedPotentialGeneratorHigh P x a) Y := by
  have hw := hd.2.2.2.2.1.1.inv (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  rcases a with u | (a | a)
  · simpa only [normalizedPotentialGeneratorLow,normalizedPotentialGeneratorHigh,potentialGeneratorWeight,
      potentialCoordinateGeneratorLow,potentialCoordinateGeneratorHigh,inv_one,one_smul] using
      (show ContDiffOn ℝ ∞ (fun _ : X => sphereSobolevShiftedDegreeL (1/2:ℝ)) Y ∧
        ContDiffOn ℝ ∞ (fun _ : X => sphereSobolevShiftedDegreeL (3/2:ℝ)) Y from
        ⟨contDiffOn_const,contDiffOn_const⟩)
  · simpa only [normalizedPotentialGeneratorLow,normalizedPotentialGeneratorHigh,potentialGeneratorWeight,
      potentialCoordinateGeneratorLow,potentialCoordinateGeneratorHigh,inv_one,one_smul] using
      And.intro (hd.framedRaisingHalf_smooth (axis a)).1 (hd.framedRaisingHalf_smooth (axis a)).2.1
  · exact ⟨hw.smul (coordinate_error_low_smooth P hd a),hw.smul (coordinate_error_high_smooth P hd a)⟩

/-- ALL normalized potential generators retain one smooth LOW first-jet
family and a compatible genuine HIGH first jet, with beta bounds. Only
existing native producers are reused; no second HIGH endpoint is assumed. -/
theorem uniform_normalized_potential_generator_first_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CL CH : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CL ∧ 0 ≤ CH ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,
    ∀ P : PhysicalPrincipalData Y d CF CT,
    ∃ DL : I → PhysicalPotentialGeneratorIndex → X →
      SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    ∀ i : I,∀ a : PhysicalPotentialGeneratorIndex,
      ContDiffOn ℝ ∞ (DL i a) Y ∧ ∀ y ∈ Y,
      halfOperatorCovariantDerivativeL d (fun x => normalizedPotentialGeneratorLow P x a)
        (fun x => normalizedPotentialGeneratorHigh P x a) y (axis i)=
        (DL i a y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖DL i a y‖ ≤ CL*beta d.γ d.radius y ∧
      ∃ DH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        higherOperatorCovariantDerivativeL d (fun x => normalizedPotentialGeneratorHigh P x a) y (axis i)=
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
            (DH.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) ∧
        ‖DH‖ ≤ CH*beta d.γ d.radius y := by
  classical
  obtain ⟨ηL,CN1,CN2,hηL,hηL1,hCN1,hCN2,hLow⟩ :=
    uniform_normalized_coordinate_error_strong_half_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηH,CNH,hηH,hηH1,hCNH,hHigh⟩ :=
    uniform_normalized_coordinate_error_covariant_higher_first hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let Q0 := framedRaisingHalfBudget K (M 0) (M ⟨1,by omega⟩)
  let G := 9*K*|M ⟨1,by omega⟩|
  let Q1 := 3*G*Q0
  let CL := CN1+Q1
  let CH := CNH+Q1
  have hK0 := zero_le_one.trans hK
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hQ0 : 0 ≤ Q0 := framedRaisingHalfBudget_nonneg _ _ _ hK0
  have hQ1 : 0 ≤ Q1 := by dsimp only [Q1];positivity
  have hCL0 : 0 ≤ CL := add_nonneg hCN1 hQ1
  have hCH0 : 0 ≤ CH := add_nonneg hCNH hQ1
  refine ⟨min ηL ηH,CL,CH,lt_min hηL hηH,(min_le_left _ _).trans hηL1,
    by dsimp only [CL];positivity,by dsimp only [CH];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨S,L,hSL⟩ := hLow floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CT P
  let DL : I → PhysicalPotentialGeneratorIndex → X →
      SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := fun i a => match a with
    | .inl _ => fun _ => 0
    | .inr (.inl a) => framedRaisingFirstHalfJet d i a
    | .inr (.inr a) => L a i
  refine ⟨DL,?_⟩
  intro i a
  rcases a with u | (a | a)
  · refine ⟨contDiffOn_const,?_⟩
    intro y hy
    have hNorm : 0 ≤ CL*beta d.γ d.radius y := mul_nonneg hCL0 (Real.sqrt_nonneg _)
    refine ⟨?_,by simpa only [DL,norm_zero] using hNorm,(0 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)),?_,
      by rw [norm_zero];exact mul_nonneg hCH0 (Real.sqrt_nonneg _)⟩
    · simpa only [normalizedPotentialGeneratorLow,normalizedPotentialGeneratorHigh,potentialGeneratorWeight,
        potentialCoordinateGeneratorLow,potentialCoordinateGeneratorHigh,inv_one,one_smul,DL,ContinuousLinearMap.zero_comp,degreeHalfL,degreeHigherL] using
        degreeHalf_covariant_derivative_zero d y (axis i)
    · have hJ := higher_covariant_derivative_of_coarse (fun _ => sphereSobolevDegreeL)
        (fun _ => degreeHigherL) 0 0 (differentiableAt_const _) (differentiableAt_const _)
        (Eventually.of_forall (fun _ => degreeHigherL_coarse))
        (sphereSobolevDegreeL_covariant_graph d y (axis i)) (by simp)
      simpa only [normalizedPotentialGeneratorHigh,potentialGeneratorWeight,potentialCoordinateGeneratorHigh,
        inv_one,one_smul,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,degreeHigherL] using hJ
  · refine ⟨framedRaisingFirstHalfJet_smooth hΩ hd (zero_lt_one.trans_le hK) i a,?_⟩
    intro y hy
    have hβ1 : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hβ0 := zero_le_one.trans hβ1
    have hMetric (b c : I) : ‖fderiv ℝ (fun x => d.γ x b c) y‖ ≤ |M ⟨1,by omega⟩| :=
      (hd.1.reference_fderiv_bound (by omega) (hSub hy) b c).trans (le_abs_self _)
    have hGamma (b : I) : |christoffel d.γ y b i a| ≤ G :=
      hd.1.1.christoffel_entry_bound (zero_lt_one.trans_le hK) (hSub hy) _ (abs_nonneg _) hMetric b i a
    have hR (b : I) := hd.framedRaisingHalf_covariant_data hY hΩ (by omega) hK b y hy
    have hLNorm : ‖framedRaisingFirstHalfJet d i a y‖ ≤ Q1 :=
      norm_weighted_sum_three_le _ _ G Q0 hG hGamma (fun b => (hR b).1)
    have hHNorm : ‖framedRaisingFirstHigherJet d i a y‖ ≤ Q1 :=
      norm_weighted_sum_three_le _ _ G Q0 hG hGamma (fun b => (hR b).2.1)
    have hCL : Q1 ≤ CL := by dsimp only [CL];linarith only [hCN1]
    have hCH : Q1 ≤ CH := by dsimp only [CH];linarith only [hCNH]
    have hGrow (C : ℝ) (hC : Q1 ≤ C) : Q1 ≤ C*beta d.γ d.radius y := by
      have hMul : Q1 ≤ Q1*beta d.γ d.radius y := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ1 hQ1
      exact hMul.trans (mul_le_mul_of_nonneg_right hC hβ0)
    refine ⟨?_,hLNorm.trans (hGrow CL hCL),framedRaisingFirstHigherJet d i a y,?_,hHNorm.trans (hGrow CH hCH)⟩
    · simpa only [normalizedPotentialGeneratorLow,normalizedPotentialGeneratorHigh,potentialGeneratorWeight,
        potentialCoordinateGeneratorLow,potentialCoordinateGeneratorHigh,inv_one,one_smul,DL] using
        framed_raising_strong_half_graph hY hΩ hd (zero_lt_one.trans_le hK) hy i a
    · have hSmooth := hd.framedRaisingHalf_smooth (axis a)
      have hJ := higher_covariant_derivative_of_coarse
        (fun x => framedFlatRaisingSobolevL 1 d.γ d.frame x (axis a))
        (fun x => framedRaisingHigherL d x (axis a)) (framedRaisingFirstCoarseJet d i a y)
        (framedRaisingFirstHigherJet d i a y)
        ((hSmooth.2.2.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        ((hSmooth.2.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (Eventually.of_forall (fun x => framedRaisingHigherL_coarse d x (axis a)))
        (hd.framedRaising_first_second_covariant_graphs hY hΩ (zero_lt_one.trans_le hK) hy i i a).1
        (framedRaisingFirstHigherJet_coarse d i a y)
      simpa only [normalizedPotentialGeneratorHigh,potentialGeneratorWeight,potentialCoordinateGeneratorHigh,
        inv_one,one_smul] using hJ
  · refine ⟨(hSL a i).2.1,?_⟩
    intro y hy
    have hJ := (hSL a i).2.2 y hy
    obtain ⟨N,hN,hDN,hNN⟩ := hHigh floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P a
      (S a) (fun i x hx => ((hSL a i).2.2 x hx).2.2.2.1) i y hy
    refine ⟨hJ.1,hJ.2.1.trans ?_,N,hDN,hNN.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (show CN1 ≤ CL by dsimp only [CL];linarith only [hQ1]) (Real.sqrt_nonneg _)
    · exact mul_le_mul_of_nonneg_right (show CNH ≤ CH by dsimp only [CH];linarith only [hQ1]) (Real.sqrt_nonneg _)

end ShrinkingSpheres.ParallelEnergy
