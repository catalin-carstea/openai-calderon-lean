import Proof.ParallelFirstPotentialGreenWeight
import Proof.ParallelNormAssemblyReservedHigherGreenIntegral
import Proof.ParallelNormAssemblyReservedPotentialFirstJet

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

/-- A single genuine normalized first-word pair has its uniform Green
bound in the original frozen energy. The fixed W supplies only pointwise
higher first-word lifts; no regularity of these choices is used. -/
theorem uniform_first_potential_paired_word_integral_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CP : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CP ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT CG CK : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ b : I,∀ a : PhysicalPotentialGeneratorIndex,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
      let H := fun y => normalizedPotentialGeneratorHigh P y a
      let q := firstPotentialGreenWeight d b a
      let F := fun y => quadraticHigherPairDensity d q H P.potentialQuadraticHalfL
          (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (axis b) y+
        quadraticHigherPairDensity d q H P.potentialQuadraticHalfL
          (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (axis b) y
      IntegrableOn F Y ∧ |∫ y in Y,F y| ≤ CP*ε*energySq Y d.γ d.frame d.radius φ := by
  classical
  obtain ⟨ηG,CL,CN,hηG,hηG1,hCL,hCN,hGen⟩ := uniform_normalized_potential_generator_first_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηQ,CD,hηQ,hηQ1,hCD,hQuad⟩ := uniform_physical_quadratic_potential_first_covariant_jet
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨CH,hCH,hBase⟩ := uniform_normalized_potential_generator_bounds
    hY hΩ hSub (by omega) K ρ c₀ M Cj hK CF
  let CW := firstPotentialWordBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  let Qμ := 27*K*|M ⟨1,by omega⟩|
  let CQ := (physicalPotentialGeneratorBudget CF)^2*(49*potentialWordEntryBudget K)
  have hCW : 0 ≤ CW := firstPotentialWordBudget_nonneg _ _ _ _ (zero_le_one.trans hK)
  have hQμ : 0 ≤ Qμ := by dsimp only [Qμ];positivity
  have hCQ : 0 ≤ CQ := by dsimp only [CQ,potentialWordEntryBudget];positivity
  obtain ⟨CP,hCP,hGreen⟩ := uniform_quadratic_higher_pair_integral_bound hY hSub K ρ c₀ M Cj hK
    (2*CW) (2*CW*(Qμ+1)) CH CN CQ CD (by positivity) (by positivity) hCH hCN hCQ hCD
  refine ⟨min ηG ηQ,CP,lt_min hηG hηQ,(min_le_left _ _).trans hηG1,hCP,?_⟩
  intro floor hf ε hε hSmall d hd CT CG CK P W b a φ E D hφ
  have hε1 := hSmall.trans ((min_le_left ηG ηQ).trans hηG1)
  obtain ⟨DL,hDL⟩ := hGen floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CT P
  choose N hN hNN using fun y (hy : y ∈ Y) => ((hDL b a).2 y hy).2.2
  choose DQ hDQ hDQN using hQuad floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CT CG CK P W b
  let NN : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := fun y => if hy : y ∈ Y then N y hy else 0
  let DD : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := fun y => if hy : y ∈ Y then DQ y hy else 0
  let L : X → SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) := fun y =>
    if hy : y ∈ Y then normalizedGeneratorForwardFirstWordHigherL P (W y hy) a else 0
  refine hGreen floor hf ε hε d hd b (firstPotentialGreenWeight d b a)
    (firstPotential_green_weight_smooth hY hd (zero_lt_one.trans_le hK) b a)
    (fun y => normalizedPotentialGeneratorHigh P y a) (normalized_potential_generators_smooth P hd a).2
    P.potentialQuadraticHalfL (P.potentialQuadraticHalfL_smooth hY hSub hd (zero_lt_one.trans_le hK)) NN DD ?_ ?_ ?_ L ?_ φ E D hφ
  · intro y hy
    simpa only [NN,dif_pos hy] using hN y hy
  · intro y hy
    simpa only [DD,dif_pos hy] using hDQ y hy
  · intro y hy
    have hWeight := firstPotential_green_weight_bounds (by omega) hY hΩ hd hK hf hε hε1 hy b b a
    refine ⟨hWeight.1,hWeight.2,(hBase floor ε d hd CT P y hy a).2,?_,
      P.norm_potentialQuadraticHalfL_weighted_small hd hK hf hε hε1 hy,?_⟩
    · simpa only [NN,dif_pos hy] using hNN y hy
    · simpa only [DD,dif_pos hy] using hDQN y hy
  · intro y hy u
    simpa only [L,dif_pos hy] using normalized_generator_forward_first_word_lift P hy (W y hy) a u

end ShrinkingSpheres.ParallelEnergy
