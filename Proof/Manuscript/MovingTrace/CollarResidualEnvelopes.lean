module

public import Proof.Manuscript.MovingTrace.ScaledProfileAmplitude
public import Proof.Manuscript.MovingTrace.OscillatoryPhaseJets
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN CalderonPatch.BoundaryLayer Set Filter Polynomial Finset
open scoped ContDiff Topology

namespace CalderonPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A family of collar jet bounds at fixed scale. The lower bound on scaled
depth accommodates the residual forcing's exterior cutoff. -/
def CollarJetEnvelope (J : Set (E × ℝ)) (f : ℝ → E × ℝ → ℂ) (N : ℕ) (weight : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ J, ∀ h : ℝ, 0 < h → h ≤ 1 → -1 ≤ q.2 / h →
    ∀ j ≤ N, ‖iteratedFDeriv ℝ j (f h) q‖ ≤ C * weight h

theorem CollarJetEnvelope.mono_weight {J : Set (E × ℝ)}
    {f : ℝ → E × ℝ → ℂ} {N : ℕ} {a b : ℝ → ℝ}
    (hF : CollarJetEnvelope J f N a)
    (hab : ∀ h : ℝ, 0 < h → h ≤ 1 → a h ≤ b h) :
    CollarJetEnvelope J f N b := by
  obtain ⟨C,hC,hJ⟩ := hF
  exact ⟨C,hC, fun q hq h hh hh₁ ht j hj =>
    (hJ q hq h hh hh₁ ht j hj).trans (mul_le_mul_of_nonneg_left (hab h hh hh₁) hC)⟩

theorem CollarJetEnvelope.sum {J : Set (E × ℝ)} {ι : Type*} (I : Finset ι)
    {f : ι → ℝ → E × ℝ → ℂ} {N : ℕ} {weight : ℝ → ℝ}
    (hs : ∀ i ∈ I, ∀ q ∈ J, ∀ h : ℝ, 0 < h → h ≤ 1 → ContDiffAt ℝ ∞ (f i h) q)
    (hf : ∀ i ∈ I, CollarJetEnvelope J (f i) N weight) :
    CollarJetEnvelope J (fun h q => ∑ i ∈ I, f i h q) N weight := by
  classical
  choose C hC hBound using hf
  let D (i : ι) : ℝ := if hi : i ∈ I then C i hi else 0
  refine ⟨∑ i ∈ I, D i, sum_nonneg (fun i hi => by simpa [D,hi] using hC i hi), ?_⟩
  intro q hq h hh hh₁ ht j hj
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => (hs i hi q hq h hh hh₁).of_le (by simp)),sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  simpa [D,hi] using hBound i hi q hq h hh hh₁ ht j hj

theorem CollarJetEnvelope.mul {J : Set (E × ℝ)} {f g : ℝ → E × ℝ → ℂ} {N : ℕ}
    {a b : ℝ → ℝ}
    (hfS : ∀ q ∈ J, ∀ h : ℝ, 0 < h → h ≤ 1 → ContDiffAt ℝ ∞ (f h) q)
    (hgS : ∀ q ∈ J, ∀ h : ℝ, 0 < h → h ≤ 1 → ContDiffAt ℝ ∞ (g h) q)
    (ha : ∀ h : ℝ, 0 < h → h ≤ 1 → 0 ≤ a h)
    (hb : ∀ h : ℝ, 0 < h → h ≤ 1 → 0 ≤ b h)
    (hf : CollarJetEnvelope J f N a) (hg : CollarJetEnvelope J g N b) :
    CollarJetEnvelope J (fun h q => f h q * g h q) N (fun h => a h * b h) := by
  obtain ⟨A,hA,hF⟩ := hf
  obtain ⟨B,hB,hG⟩ := hg
  let L := ContinuousLinearMap.mul ℝ ℂ
  refine ⟨‖L‖ * 2 ^ N * A * B, by positivity, ?_⟩
  intro q hq h hh hh₁ ht j hj
  exact (ShrinkingSpheres.norm_iteratedFDeriv_bilinear_common_bound L (f h) (g h) q
    (hfS q hq h hh hh₁) (hgS q hq h hh hh₁) N (A*a h) (B*b h)
    (mul_nonneg hA (ha h hh hh₁)) (mul_nonneg hB (hb h hh hh₁))
    (hF q hq h hh hh₁ ht) (hG q hq h hh hh₁ ht) j hj).trans_eq (by ring)

theorem CollarJetEnvelope.profile
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {A J : Set (E × ℝ)} (hA : IsOpen A) (hJ : IsCompact J) (hJA : J ⊆ A)
    (hJK : ∀ q ∈ J, q.1 ∈ K) {f : E × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f A)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U) {c : ℝ} (hc : 0 < c) (hcκ : ∀ p ∈ K, c ≤ κ p)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ) (hD : ∀ p ∈ U, (P p).natDegree < D)
    (M N : ℕ) :
    CollarJetEnvelope J
      (fun h p => (h : ℂ)^M * (f p * polynomialProfileFamily κ P (p.1,p.2/h))) N
      (fun h => h^M * h⁻¹ ^ N) := by
  obtain ⟨C,hC,hJ⟩ := exists_scaled_profile_amplitude_jet_bound hU hK hKU hA hJ hJA hJK hf
    hκ hc hcκ hP D hD M N
  refine ⟨C * Real.exp (c/4),by positivity,?_⟩
  intro q hq h hh hh₁ ht j hj
  have hExp : Real.exp (-(c/4)*(q.2/h)) ≤ Real.exp (c/4) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (hJ q hq h hh hh₁ ht j hj).trans ((mul_le_mul_of_nonneg_left hExp (by positivity)).trans_eq (by ring))

/-- Profile contribution supported at a fixed separated depth. Smooth
vanishing on the lower part keeps every derivative of the contribution
zero there. -/
theorem CollarJetEnvelope.separated_profile
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {A J : Set (E × ℝ)} (hA : IsOpen A) (hJ : IsCompact J) (hJA : J ⊆ A)
    (hJK : ∀ q ∈ J, q.1 ∈ K) {f : E × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f A)
    {d : ℝ} (hd : 0 < d) (hZero : ∀ q ∈ A, q.2 < d → f q = 0)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U) {c : ℝ} (hc : 0 < c) (hcκ : ∀ p ∈ K, c ≤ κ p)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ) (hD : ∀ p ∈ U, (P p).natDegree < D)
    (M L N : ℕ) :
    CollarJetEnvelope J
      (fun h p => (h : ℂ)^M * (f p * polynomialProfileFamily κ P (p.1,p.2/h))) N
      (fun h => h^M * h^L * h⁻¹ ^ N) := by
  obtain ⟨C,hC,hJ⟩ := exists_scaled_profile_amplitude_jet_bound hU hK hKU hA hJ hJA hJK hf
    hκ hc hcκ hP D hD M N
  let B := (L.factorial : ℝ) / ((c/4)*d)^L
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨C*B,mul_nonneg hC hB,?_⟩
  intro q hq h hh hh₁ ht j hj
  by_cases hdq : d ≤ q.2
  · have hExp : Real.exp (-(c/4)*(q.2/h)) ≤ B * h^L :=
      scaled_exp_tail (by positivity) hd hh hdq L
    exact (hJ q hq h hh hh₁ ht j hj).trans ((mul_le_mul_of_nonneg_left hExp (by positivity)).trans_eq (by ring))
  · have hf0 : (fun p : E × ℝ => (h : ℂ)^M *
        (f p * polynomialProfileFamily κ P (p.1,p.2/h))) =ᶠ[𝓝 q] 0 := by
      filter_upwards [hA.mem_nhds (hJA hq), (isOpen_lt continuous_snd continuous_const).mem_nhds
        (show q.2 < d from lt_of_not_ge hdq)] with p hp hp'
      simp only [hZero p hp hp',zero_mul,mul_zero,Pi.zero_apply]
    rw [(hf0.iteratedFDeriv ℝ j).eq_of_nhds,iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
    positivity

end CalderonPaper
