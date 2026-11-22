module

public import Proof.Manuscript.MovingTrace.CollarResidualEnvelopes
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN CalderonPatch.BoundaryLayer Set Polynomial Finset
open scoped ContDiff

namespace CalderonPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smoothly parameterized contribution to the scaled collar residual,
with a common jet bound on the geometry set. -/
def SmoothCollarContribution (J : Set (E × ℝ)) (f : ℝ → E × ℝ → ℂ)
    (N : ℕ) (weight : ℝ → ℝ) : Prop :=
  (∀ q ∈ J, ∀ h : ℝ, 0 < h → h ≤ 1 → ContDiffAt ℝ ∞ (f h) q) ∧
  CollarJetEnvelope J f N weight

theorem SmoothCollarContribution.sum {J : Set (E × ℝ)} {ι : Type*} (I : Finset ι)
    {f : ι → ℝ → E × ℝ → ℂ} {N : ℕ} {weight : ℝ → ℝ}
    (hf : ∀ i ∈ I, SmoothCollarContribution J (f i) N weight) :
    SmoothCollarContribution J (fun h q => ∑ i ∈ I, f i h q) N weight := by
  refine ⟨fun q hq h hh hh₁ => ContDiffAt.sum (fun i hi => (hf i hi).1 q hq h hh hh₁), ?_⟩
  exact CollarJetEnvelope.sum I (fun i hi => (hf i hi).1) (fun i hi => (hf i hi).2)

theorem SmoothCollarContribution.add {J : Set (E × ℝ)} {f g : ℝ → E × ℝ → ℂ}
    {N : ℕ} {weight : ℝ → ℝ}
    (hf : SmoothCollarContribution J f N weight) (hg : SmoothCollarContribution J g N weight) :
    SmoothCollarContribution J (fun h q => f h q + g h q) N weight := by
  refine ⟨fun q hq h hh hh₁ => (hf.1 q hq h hh hh₁).add (hg.1 q hq h hh hh₁), ?_⟩
  obtain ⟨A,hA,hF⟩ := hf.2
  obtain ⟨B,hB,hG⟩ := hg.2
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro q hq h hh hh₁ ht j hj
  rw [fun_iteratedFDeriv_add_apply ((hf.1 q hq h hh hh₁).of_le (by simp))
      ((hg.1 q hq h hh hh₁).of_le (by simp)),add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hF q hq h hh hh₁ ht j hj) (hG q hq h hh hh₁ ht j hj))

theorem SmoothCollarContribution.neg {J : Set (E × ℝ)} {f : ℝ → E × ℝ → ℂ}
    {N : ℕ} {weight : ℝ → ℝ} (hf : SmoothCollarContribution J f N weight) :
    SmoothCollarContribution J (fun h q => -f h q) N weight := by
  refine ⟨fun q hq h hh hh₁ => (hf.1 q hq h hh hh₁).neg, ?_⟩
  obtain ⟨C,hC,hF⟩ := hf.2
  refine ⟨C,hC,?_⟩
  intro q hq h hh hh₁ ht j hj
  change ‖iteratedFDeriv ℝ j (-(f h)) q‖ ≤ C * weight h
  rw [iteratedFDeriv_neg_apply,norm_neg]
  exact hF q hq h hh hh₁ ht j hj

theorem SmoothCollarContribution.mul {J : Set (E × ℝ)} {f g : ℝ → E × ℝ → ℂ}
    {N : ℕ} {a b : ℝ → ℝ}
    (ha : ∀ h : ℝ, 0 < h → h ≤ 1 → 0 ≤ a h)
    (hb : ∀ h : ℝ, 0 < h → h ≤ 1 → 0 ≤ b h)
    (hf : SmoothCollarContribution J f N a) (hg : SmoothCollarContribution J g N b) :
    SmoothCollarContribution J (fun h q => f h q * g h q) N (fun h => a h * b h) :=
  ⟨fun q hq h hh hh₁ => (hf.1 q hq h hh hh₁).mul (hg.1 q hq h hh hh₁),
    CollarJetEnvelope.mul hf.1 hg.1 ha hb hf.2 hg.2⟩

/-- The spatial variable is rescaled only in the normal polynomial. The
amplitude is a smooth function of the unscaled collar variables. -/
def scaledProfileContribution (f : E × ℝ → ℂ) (κ : E → ℝ) (P : E → ℂ[X])
    (M : ℕ) (h : ℝ) (q : E × ℝ) : ℂ :=
  (h : ℂ)^M * (f q * polynomialProfileFamily κ P (q.1,q.2/h))

theorem contDiffAt_scaledProfileContribution
    {U : Set E} (hU : IsOpen U) {q : E × ℝ} (hq : q.1 ∈ U)
    {f : E × ℝ → ℂ} (hf : ContDiffAt ℝ ∞ f q)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ) (hD : ∀ p ∈ U, (P p).natDegree < D)
    (M : ℕ) (h : ℝ) : ContDiffAt ℝ ∞ (scaledProfileContribution f κ P M h) q := by
  have hMap : ContDiff ℝ ∞ (fun p : E × ℝ => (p.1,p.2/h)) :=
    contDiff_fst.prodMk (contDiff_snd.div_const h)
  have hA := (hP.profile hκ D hD).contDiffAt ((hU.prod isOpen_univ).mem_nhds
    (show (q.1,q.2/h) ∈ U ×ˢ (univ : Set ℝ) from ⟨hq,mem_univ _⟩))
  change ContDiffAt ℝ ∞ (polynomialProfileFamily κ P) (q.1,q.2/h) at hA
  have hComp := hA.comp q hMap.contDiffAt
  change ContDiffAt ℝ ∞ (fun p : E × ℝ => polynomialProfileFamily κ P (p.1,p.2/h)) q at hComp
  exact contDiffAt_const.mul (hf.mul hComp)

theorem SmoothCollarContribution.profile
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {A J : Set (E × ℝ)} (hA : IsOpen A) (hJ : IsCompact J) (hJA : J ⊆ A)
    (hJK : ∀ q ∈ J, q.1 ∈ K) {f : E × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f A)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U) {c : ℝ} (hc : 0 < c) (hcκ : ∀ p ∈ K, c ≤ κ p)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ) (hD : ∀ p ∈ U, (P p).natDegree < D)
    (M L N : ℕ) (hLM : L ≤ M) :
    SmoothCollarContribution J (scaledProfileContribution f κ P M) N
      (fun h => h^L * h⁻¹ ^ N) := by
  refine ⟨fun q hq h _ _ => contDiffAt_scaledProfileContribution hU (hKU (hJK q hq))
    (hf.contDiffAt (hA.mem_nhds (hJA hq))) hκ hP D hD M h, ?_⟩
  apply (CollarJetEnvelope.profile hU hK hKU hA hJ hJA hJK hf hκ hc hcκ hP D hD M N).mono_weight
  intro h hh hh₁
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hh.le hh₁ hLM) (by positivity)

theorem SmoothCollarContribution.separated_profile
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {A J : Set (E × ℝ)} (hA : IsOpen A) (hJ : IsCompact J) (hJA : J ⊆ A)
    (hJK : ∀ q ∈ J, q.1 ∈ K) {f : E × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f A)
    {d : ℝ} (hd : 0 < d) (hZero : ∀ q ∈ A, q.2 < d → f q = 0)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U) {c : ℝ} (hc : 0 < c) (hcκ : ∀ p ∈ K, c ≤ κ p)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ) (hD : ∀ p ∈ U, (P p).natDegree < D)
    (M L N : ℕ) :
    SmoothCollarContribution J (scaledProfileContribution f κ P M) N
      (fun h => h^L * h⁻¹ ^ N) := by
  refine ⟨fun q hq h _ _ => contDiffAt_scaledProfileContribution hU (hKU (hJK q hq))
    (hf.contDiffAt (hA.mem_nhds (hJA hq))) hκ hP D hD M h, ?_⟩
  apply (CollarJetEnvelope.separated_profile hU hK hKU hA hJ hJA hJK hf hd hZero
    hκ hc hcκ hP D hD M L N).mono_weight
  intro h hh hh₁
  rw [mul_assoc]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hh.le hh₁)

end CalderonPaper
