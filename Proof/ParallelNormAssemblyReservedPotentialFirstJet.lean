import Proof.ParallelNormAssemblyReservedGeneratorFirstJets
import Proof.ParallelNormAssemblyReservedQuadraticMatrixJet
import Proof.ParallelNormAssemblyReservedUniformPotentialCoefficients
import Proof.ParallelNormAssemblyReservedNormalizedWordLifts

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

lemma norm_quadratic_word_first_jet_le {ι : Type*} [Fintype ι]
    (p dp : ι → ι → ℝ)
    (L DL : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H DH : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (CP CG CL CH ε β : ℝ) (hCP : 0 ≤ CP) (hCG : 0 ≤ CG)
    (hCL : 0 ≤ CL) (hCH : 0 ≤ CH) (hε : 0 ≤ ε) (hβ : 0 ≤ β)
    (hp : ∀ a b,|p a b| ≤ CP*ε) (hdp : ∀ a b,|dp a b| ≤ CP*ε*β)
    (hL : ∀ a,‖L a‖ ≤ CG) (hH : ∀ a,‖H a‖ ≤ CG)
    (hDL : ∀ a,‖DL a‖ ≤ CL*β) (hDH : ∀ a,‖DH a‖ ≤ CH*β) :
    ‖quadraticWordFirstJetL p dp L DL H DH‖ ≤
      (Fintype.card ι:ℝ)^2*CP*(CG^2+CG*(CL+CH))*ε*β := by
  have hEach (a b : ι) := weighted_quadratic_first_jet_norm (L a) (DL a) (H b) (DH b)
    (p a b) (dp a b) CP CG CL CH ε β hCP hCG hCL hCH hε hβ
    (hp a b) (hdp a b) (hL a) (hH b) (hDL a) (hDH b)
  exact ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b _ => hEach a b))))).trans_eq
      (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring)

/-- The complete SAME actual quadratic potential has a genuine strong
first covariant jet H3/2→H−1/2 of size C*epsilon*beta. The derivative is
identified on the true H5/2 core through H−3/2, using ANY fixed W before
tests. Only FIRST LOW/HIGH generator jets are used. -/
theorem uniform_physical_quadratic_potential_first_covariant_jet {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT CG CK : ℝ,
    ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ i : I,∀ y ∈ Y,∃ DQ : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      quadraticOperatorCovariantDerivativeL d (fun x => P.potentialQuadraticHalfL x) y (axis i)=
        (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
          (DQ.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) ∧
      ‖DQ‖ ≤ C*ε*beta d.γ d.radius y := by
  classical
  obtain ⟨η,CL,CH,hη,hη1,hCL,hCH,hJets⟩ := uniform_normalized_potential_generator_first_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨CG0,hCG0,hBase⟩ := uniform_normalized_potential_generator_bounds hY hΩ hSub (by omega) K ρ c₀ M Cj hK CF
  obtain ⟨CP,hCP,hCoeff⟩ := uniform_normalized_potential_coefficients_two_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  let C := 49*CP*(CG0^2+CG0*(CL+CH))
  refine ⟨η,C,hη,hη1,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT CG CK P W i y hy
  obtain ⟨DL,hDL⟩ := hJets floor hf ε hε hSmall d hd CT P
  have hP := hCoeff floor hf ε hε (hSmall.trans hη1) d hd
  choose DH hDH hDN using fun b : PhysicalPotentialGeneratorIndex => ((hDL i b).2 y hy).2.2
  let DQ := quadraticWordFirstJetL (fun a b => normalizedPotentialWordCoefficient d y a b)
    (fun a b => coordDeriv i (fun x => normalizedPotentialWordCoefficient d x a b) y)
    (fun a => normalizedPotentialGeneratorLow P y a) (fun a => DL i a y)
    (fun a => normalizedPotentialGeneratorHigh P y a) DH
  have hNorm := norm_quadratic_word_first_jet_le _ _ _ _ _ _ CP CG0 CL CH ε (beta d.γ d.radius y)
    hCP hCG0 hCL hCH hε (Real.sqrt_nonneg _)
    (fun a b => (hP.2 y hy a b).value) (fun a b => (hP.2 y hy a b).first i)
    (fun a => (hBase floor ε d hd CT P y hy a).1) (fun a => (hBase floor ε d hd CT P y hy a).2)
    (fun a => ((hDL i a).2 y hy).2.1) hDN
  refine ⟨DQ,?_,?_⟩
  · have hEq : (fun x => P.potentialQuadraticHalfL x)=ᶠ[𝓝 y]
        (fun x => ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
          normalizedPotentialWordCoefficient d x a b •
            (normalizedPotentialGeneratorLow P x a).comp (normalizedPotentialGeneratorHigh P x b)) := by
      filter_upwards [hY.mem_nhds hy] with x hx
      exact potential_quadratic_normalized_coordinate_words P x (hd.2.2.2.2.1.2 x hx).1
        (hd.1.2.2.2.2.2.2.2 x (hSub hx))
    rw [quadratic_covariant_congr_germ hEq]
    apply ContinuousLinearMap.ext
    intro u
    exact quadratic_matrix_covariant_first_jet d
      (fun a b x => normalizedPotentialWordCoefficient d x a b)
      (fun a x => normalizedPotentialGeneratorLow P x a) (fun a x => normalizedPotentialGeneratorHigh P x a)
      y (axis i) (fun a b => (hP.1 a b).contDiffAt (hY.mem_nhds hy))
      (fun a => ((normalized_potential_generators_smooth P hd a).1).contDiffAt (hY.mem_nhds hy))
      (fun a => ((normalized_potential_generators_smooth P hd a).2).contDiffAt (hY.mem_nhds hy))
      (fun a => DL i a y) DH (fun a => normalized_generator_balanced P hy a)
      (fun a => ((hDL i a).2 y hy).1) hDH u
      (fun a => normalizedGeneratorForwardFirstWordHigherL P (W y hy) a u)
      (fun a => normalized_generator_forward_first_word_lift P hy (W y hy) a u)
  · have hCard : (Fintype.card PhysicalPotentialGeneratorIndex:ℝ)^2=49 := by
      norm_num [PhysicalPotentialGeneratorIndex]
    simpa only [hCard,C,DQ] using hNorm

end ShrinkingSpheres.ParallelEnergy
