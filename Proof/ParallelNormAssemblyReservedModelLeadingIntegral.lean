import Proof.ParallelNormAssemblyReservedHigherGreenIntegral
import Proof.ParallelNormAssemblyReservedPotentialFirstJet
import Proof.ParallelNormAssemblyReservedModelWeights
import Proof.PhysicalPotentialWordMass
import Proof.PhysicalPotentialQuadraticSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def modelPotentialPairedLeadingComplexDensity {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (k c : I) (y : X) : ℝ :=
  quadraticHigherPairDensity d (modelPotentialLeadingWeight d k c)
    (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inl c))) P.potentialQuadraticHalfL
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (axis k) y+
  quadraticHigherPairDensity d (modelPotentialLeadingWeight d k c)
    (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inl c))) P.potentialQuadraticHalfL
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (axis k) y

/-- The actual model/potential paired leading Green term has the original
uniform C epsilon energy bound. The SAME complete potential and ANY fixed
W precede tests; the first-word lift is genuine and never differentiated. -/
theorem uniform_actual_model_potential_paired_leading_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η C0 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT CG CK : ℝ,
    ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
    ∀ k c : I,∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
    ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
      IntegrableOn (modelPotentialPairedLeadingComplexDensity P E k c) Y ∧
      |∫ y in Y,modelPotentialPairedLeadingComplexDensity P E k c y| ≤
        C0*ε*energySq Y d.γ d.frame d.radius φ := by
  classical
  obtain ⟨ηH,CL,CH,hηH,hηH1,hCL,hCH,hJets⟩ := uniform_normalized_potential_generator_first_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηQ,CD,hηQ,hηQ1,hCD,hQJet⟩ := uniform_physical_quadratic_potential_first_covariant_jet
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨CG0,hCG0,hBase⟩ := uniform_normalized_potential_generator_bounds
    hY hΩ hSub (by omega) K ρ c₀ M Cj hK CF
  obtain ⟨Q0,Q1,hQ0,hQ1,hWeight⟩ := uniform_model_potential_leading_weight_jets
    hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  let CQ := (physicalPotentialGeneratorBudget CF)^2*(49*potentialWordEntryBudget K)
  have hCQ : 0 ≤ CQ := by dsimp only [CQ,potentialWordEntryBudget];positivity
  obtain ⟨C0,hC0,hIntegral⟩ := uniform_quadratic_higher_pair_integral_bound hY hSub K ρ c₀ M Cj hK
    Q0 Q1 CG0 CH CQ CD hQ0 hQ1 hCG0 hCH hCQ hCD
  refine ⟨min ηH ηQ,C0,lt_min hηH hηQ,(min_le_left _ _).trans hηH1,hC0,?_⟩
  intro floor hf ε hε hSmall d hd CT CG CK P W k c φ E D hφ
  have hε1 := ((hSmall.trans (min_le_left _ _)).trans hηH1)
  obtain ⟨DL,hDL⟩ := hJets floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CT P
  let N : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := fun x =>
    if hx : x ∈ Y then Classical.choose (((hDL k (.inr (.inl c))).2 x hx).2.2) else 0
  let DQ : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := fun x =>
    if hx : x ∈ Y then Classical.choose (hQJet floor hf ε hε (hSmall.trans (min_le_right _ _))
      d hd CT CG CK P W k x hx) else 0
  let L : X → SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) := fun x =>
    if hx : x ∈ Y then normalizedGeneratorForwardFirstWordHigherL P (W x hx) (.inr (.inl c)) else 0
  have hNP (x : X) (hx : x ∈ Y) := Classical.choose_spec (((hDL k (.inr (.inl c))).2 x hx).2.2)
  have hDP (x : X) (hx : x ∈ Y) := Classical.choose_spec
    (hQJet floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CT CG CK P W k x hx)
  refine hIntegral floor hf ε hε d hd k (modelPotentialLeadingWeight d k c)
    (hWeight floor ε d hd k c).1
    (fun x => normalizedPotentialGeneratorHigh P x (.inr (.inl c)))
    (normalized_potential_generators_smooth P hd (.inr (.inl c))).2
    P.potentialQuadraticHalfL (P.potentialQuadraticHalfL_smooth hY hSub hd (zero_lt_one.trans_le hK))
    N DQ ?_ ?_ ?_ L ?_ φ E D hφ
  · intro x hx
    simpa only [N,dite_eq_left hx] using (hNP x hx).1
  · intro x hx
    simpa only [DQ,dite_eq_left hx] using (hDP x hx).1
  · intro x hx
    refine ⟨(hWeight floor ε d hd k c).2 x hx k |>.1,
      (hWeight floor ε d hd k c).2 x hx k |>.2,
      (hBase floor ε d hd CT P x hx (.inr (.inl c))).2,?_,?_,?_⟩
    · simpa only [N,dite_eq_left hx] using (hNP x hx).2
    · exact P.norm_potentialQuadraticHalfL_weighted_small hd hK hf hε hε1 hx
    · simpa only [DQ,dite_eq_left hx] using (hDP x hx).2
  · intro x hx u
    simpa only [L,dite_eq_left hx] using normalized_generator_forward_first_word_lift P hx (W x hx) (.inr (.inl c)) u

end ShrinkingSpheres.ParallelEnergy
