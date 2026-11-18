import Proof.ParallelNormAssemblyReservedAdjointQuadratic
import Proof.ParallelNormAssemblyReservedPotentialFirstJet
import Proof.StrongHalfCovariantAdjoint
import Proof.PhysicalPotentialWordMass

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

structure PotentialAdjointFirstJetPacket {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (ε CN CJ : ℝ) where
  weak : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  smooth : ContDiffOn ℝ ∞ weak Y
  norm_bound : ∀ y ∈ Y,‖weak y‖ ≤ CN*ε
  actual_graph : ∀ CG CK : ℝ,∀ y ∈ Y,∀ W : PhysicalPotentialQuarticData P y CG CK,
    ∀ u : SphereSobolev (3/2:ℝ),quadraticWordAdjointWeakValue P W (PhysicalPrincipalData.potentialWordCoefficient d y) u=weak y u
  jet : ∀ CG CK : ℝ,∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ i : I,∀ y ∈ Y,∃ DQ : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      quadraticOperatorCovariantDerivativeL d weak y (axis i)=
        (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
          (DQ.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) ∧
      ‖DQ‖ ≤ CJ*ε*beta d.γ d.radius y

lemma normalized_potential_adjoint_weak_transpose {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (A : PhysicalPotentialGeneratorIndex → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y : X) :
    normalizedPotentialAdjointWeakL P A y=
      ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
        normalizedPotentialWordCoefficient d y b a • (normalizedPotentialGeneratorLow P y a).adjoint.comp (A b y) := by
  rw [normalizedPotentialAdjointWeakL,Finset.sum_comm]

/-- The actual reflected quadratic potential has a canonically smooth
weak coefficient and genuine FIRST H3/2→H−1/2 covariant jet C epsilon beta,
with the SAME arbitrary W retained before tests. No HIGH2 is assumed. -/
theorem uniform_physical_potential_adjoint_first_covariant_jet {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CN CJ : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CN ∧ 0 ≤ CJ ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
    Nonempty (PotentialAdjointFirstJetPacket P ε CN CJ) := by
  classical
  obtain ⟨ηA,CA0,CA1,hηA,hηA1,hCA0,hCA1,hAdj⟩ := uniform_normalized_generator_adjoint_first_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηL,CL,CH,hηL,hηL1,hCL,hCH,hLow⟩ := uniform_normalized_potential_generator_first_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨CG0,hCG0,hBase⟩ := uniform_normalized_potential_generator_bounds hY hΩ hSub (by omega) K ρ c₀ M Cj hK CF
  obtain ⟨CP,hCP,hCoeff⟩ := uniform_normalized_potential_coefficients_two_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  let G := max CG0 CA0
  let CN := 49*CP*G^2
  let CJ := 49*CP*(G^2+G*(CL+CA1))
  have hG : 0 ≤ G := hCG0.trans (le_max_left _ _)
  refine ⟨min ηA ηL,CN,CJ,lt_min hηA hηL,(min_le_left _ _).trans hηA1,
    by dsimp only [CN];positivity,by dsimp only [CJ];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  have hε1 := ((hSmall.trans (min_le_left _ _)).trans hηA1)
  obtain ⟨A⟩ := hAdj floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P
  obtain ⟨DL,hDL⟩ := hLow floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CT P
  have hP := hCoeff floor hf ε hε hε1 d hd
  let CA := normalizedPotentialAdjointWeakL P A.high
  let Adj := (ContinuousLinearMap.adjoint :
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) ≃ₗᵢ[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))))
  have hLS (a : PhysicalPotentialGeneratorIndex) :
      ContDiffOn ℝ ∞ (fun x => (normalizedPotentialGeneratorLow P x a).adjoint) Y :=
    Adj.contDiff.comp_contDiffOn (normalized_potential_generators_smooth P hd a).1
  have hLN (a : PhysicalPotentialGeneratorIndex) (y : X) (hy : y ∈ Y) :
      ‖(normalizedPotentialGeneratorLow P y a).adjoint‖ ≤ G := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact ((hBase floor ε d hd CT P y hy a).1).trans (le_max_left _ _)
  have hAN (a : PhysicalPotentialGeneratorIndex) (y : X) (hy : y ∈ Y) : ‖A.high a y‖ ≤ G :=
    (A.norm_bound a y hy).trans (le_max_right _ _)
  have hSmooth : ContDiffOn ℝ ∞ CA Y := by
    apply ContDiffOn.sum
    intro c _
    apply ContDiffOn.sum
    intro e _
    exact (hP.1 c e).smul ((hLS e).clm_comp (A.smooth c))
  refine ⟨{ weak := CA,smooth := hSmooth,norm_bound := ?_,actual_graph := ?_,jet := ?_ }⟩
  · intro y hy
    rw [show CA y=_ from normalized_potential_adjoint_weak_transpose P A.high y]
    have hWord := norm_finite_quadratic_words_le_mass
      (fun a b => normalizedPotentialWordCoefficient d y b a)
      (fun a => (normalizedPotentialGeneratorLow P y a).adjoint) (fun b => A.high b y)
      (fun _ => (1:ℝ)) hG (fun _ => zero_le_one)
      (fun a => by simpa only [mul_one] using hLN a y hy)
      (fun b => by simpa only [mul_one] using hAN b y hy)
    simp only [mul_one] at hWord
    have hMass : (∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
        |normalizedPotentialWordCoefficient d y b a|) ≤ 49*CP*ε := by
      calc
        _ ≤ ∑ _a : PhysicalPotentialGeneratorIndex,∑ _b : PhysicalPotentialGeneratorIndex,CP*ε :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => (hP.2 y hy b a).value))
        _ = _ := by simp only [Fintype.sum_sum_type,Fintype.sum_unique,Fin.sum_univ_three];ring
    exact hWord.trans ((mul_le_mul_of_nonneg_left hMass (sq_nonneg G)).trans_eq (by dsimp only [CN];ring))
  · intro CG CK y hy W u
    exact actual_potential_adjoint_normalized_eq P hd A hy W u
  · intro CG CK W i y hy
    choose DH hDH hDN using fun a : PhysicalPotentialGeneratorIndex => A.jet a y hy i
    let DQ := quadraticWordFirstJetL (fun a b => normalizedPotentialWordCoefficient d y b a)
      (fun a b => coordDeriv i (fun x => normalizedPotentialWordCoefficient d x b a) y)
      (fun a => (normalizedPotentialGeneratorLow P y a).adjoint) (fun a => (DL i a y).adjoint)
      (fun b => A.high b y) DH
    have hLowGraph (a : PhysicalPotentialGeneratorIndex) := half_covariant_adjoint_strong_extension d
      (fun x => normalizedPotentialGeneratorLow P x a) (fun x => normalizedPotentialGeneratorHigh P x a)
      (A.high a) (((normalized_potential_generators_smooth P hd a).1).contDiffAt (hY.mem_nhds hy)) (axis i)
      (normalized_generator_balanced P hy a) (A.balanced a y hy) (DL i a y) (((hDL i a).2 y hy).1)
    refine ⟨DQ,?_,?_⟩
    · have hEq : CA=ᶠ[𝓝 y] (fun x => ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
          normalizedPotentialWordCoefficient d x b a • (normalizedPotentialGeneratorLow P x a).adjoint.comp (A.high b x)) :=
        Eventually.of_forall (normalized_potential_adjoint_weak_transpose P A.high)
      rw [quadratic_covariant_congr_germ hEq]
      apply ContinuousLinearMap.ext
      intro u
      exact quadratic_matrix_covariant_first_jet d
        (fun a b x => normalizedPotentialWordCoefficient d x b a)
        (fun a x => (normalizedPotentialGeneratorLow P x a).adjoint) (fun b x => A.high b x)
        y (axis i) (fun a b => (hP.1 b a).contDiffAt (hY.mem_nhds hy))
        (fun a => (hLS a).contDiffAt (hY.mem_nhds hy)) (fun b => (A.smooth b).contDiffAt (hY.mem_nhds hy))
        (fun a => (DL i a y).adjoint) DH (fun a => A.balanced a y hy) hLowGraph hDH u
        (fun b => normalizedGeneratorReverseFirstWordHigherL P (W y hy) b u)
        (fun b => normalized_generator_reverse_first_word_lift P (W y hy) b (A.high b y) (A.balanced b y hy) u)
    · have hN := norm_quadratic_word_first_jet_le _ _ _ _ _ _ CP G CL CA1 ε (beta d.γ d.radius y)
        hCP hG hCL hCA1 hε (Real.sqrt_nonneg _)
        (fun a b => (hP.2 y hy b a).value) (fun a b => (hP.2 y hy b a).first i)
        (fun a => hLN a y hy) (fun b => hAN b y hy)
        (fun a => by rw [ContinuousLinearMap.adjoint.norm_map];exact ((hDL i a).2 y hy).2.1) hDN
      have hCard : (Fintype.card PhysicalPotentialGeneratorIndex:ℝ)^2=49 := by norm_num [PhysicalPotentialGeneratorIndex]
      simpa only [hCard,CJ,DQ] using hN

end ShrinkingSpheres.ParallelEnergy
