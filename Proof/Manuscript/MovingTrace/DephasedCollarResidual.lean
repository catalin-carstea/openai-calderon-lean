module

public import Proof.Manuscript.MovingTrace.FiniteResidualProfileJets
public import Proof.Manuscript.MovingTrace.ParametricCutoffContribution
public import Proof.Manuscript.MovingTrace.OscillatoryPhaseJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 2800000

open CalderonPaper Set Finset
open CalderonN (X I axis)
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer.ParametricLayerCoefficients

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {U : Set (P × X n)} (B : ParametricLayerCoefficients (n := n) U)

def dephasedResidual (a : P × X n → ℂ) (η : ℝ → ℝ) (M : ℕ)
    (A : RemainderMatrix n P) (τ₁ τ₂ : (P × X n) × ℝ → ℂ) (c : RemainderDrift n P)
    (h : ℝ) (q : (P × X n) × ℝ) : ℂ :=
  (η q.2 : ℂ) * (B.finiteResidualProfile a M h (q.1,q.2/h) +
    ∑ j ∈ range (M+1), B.taylorGapContribution a j (M+1) A τ₁ c h q) +
  ∑ j ∈ range (M+1), B.cutoffContribution a η τ₂ j h q

theorem finiteResidualProfile_contDiffOn_scaled (hU : IsOpen U) {K : Set (P × X n)}
    (hK : IsClosed K) (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (ha0 : ∀ q ∉ K, a q = 0) (M : ℕ) (h : ℝ) :
    ContDiffOn ℝ ∞ (fun q : (P × X n) × ℝ => B.finiteResidualProfile a M h (q.1,q.2/h))
      (U ×ˢ (univ : Set ℝ)) := by
  unfold finiteResidualProfile
  apply ContDiffOn.sum
  intro i hi
  have hCoeff := B.finiteResidualPolynomial_coeff_regular hU hK a ha ha0 M i.val
  have hDegree (q : P × X n) (hq : q ∈ U) :
      ((B.finiteResidualPolynomial a M q).coeff i.val).natDegree < 4 * M + 4 :=
    Nat.lt_succ_of_le (B.finiteResidualPolynomial_coeff_degree hU hK a ha ha0 M i.val hq)
  have hMap : ContDiffOn ℝ ∞ (fun q : (P × X n) × ℝ => (q.1,q.2/h)) (U ×ˢ univ) :=
    (contDiff_fst.prodMk (contDiff_snd.div_const h)).contDiffOn
  have hProfile := (hCoeff.profile B.kappa_smooth _ hDegree).comp hMap
    (fun q hq => ⟨hq.1,mem_univ _⟩)
  exact contDiffOn_const.mul hProfile

theorem finiteResidualProfile_scaled_envelope
    (hU : IsOpen U) {K K₀ : Set (P × X n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hK₀ : IsClosed K₀) (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (ha0 : ∀ q ∉ K₀, a q = 0) {J : Set ((P × X n) × ℝ)}
    (hJK : ∀ q ∈ J, q.1 ∈ K) (M N : ℕ) :
    SmoothCollarContribution J
      (fun h (q : (P × X n) × ℝ) => B.finiteResidualProfile a M h (q.1,q.2/h))
      N (fun h => h^(M+1) * h⁻¹^N) := by
  refine ⟨fun q hq h _ _ => (B.finiteResidualProfile_contDiffOn_scaled hU hK₀ a ha ha0 M h).contDiffAt
    ((hU.prod isOpen_univ).mem_nhds ⟨hKU (hJK q hq),mem_univ _⟩), ?_⟩
  obtain ⟨c,C,hc,hC,hBound⟩ := B.finiteResidualProfile_scaled_jet_bound hU hK₀ hK hKU a ha ha0 M N
  refine ⟨C * Real.exp c, by positivity, ?_⟩
  intro q hq h hh hh₁ ht j hj
  have hExp : Real.exp (-c * (q.2/h)) ≤ Real.exp c := Real.exp_le_exp.mpr (by nlinarith)
  refine (hBound h hh hh₁ q (hJK q hq) ht j hj).trans ?_
  calc
    _ ≤ C * h^(M+1) * h⁻¹^N * Real.exp c :=
      mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = _ := by ring

theorem SmoothCollarContribution.compact_unscaled
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O J : Set (E × ℝ)} (hO : IsOpen O) (hJ : IsCompact J) (hJO : J ⊆ O)
    {f : E × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f O) (N : ℕ) :
    SmoothCollarContribution J (fun _ => f) N (fun _ => 1) := by
  have hD (j : Fin (N+1)) :
      ContinuousOn (fun q => ‖iteratedFDeriv ℝ j.val f q‖) O := by
    refine (hf.continuousOn_iteratedFDerivWithin (by simp : (j.val : ℕ∞ω) ≤ ∞)
      hO.uniqueDiffOn).norm.congr ?_
    intro q hq
    exact congrArg norm (iteratedFDerivWithin_of_isOpen j.val hO hq).symm
  have hBound (j : Fin (N+1)) : ∃ C ≥ 0, ∀ q ∈ J, ‖iteratedFDeriv ℝ j.val f q‖ ≤ C := by
    obtain ⟨r,hr⟩ := hJ.bddAbove_image ((hD j).mono hJO)
    exact ⟨max 0 r,le_max_left _ _,fun q hq => (hr ⟨q,hq,rfl⟩).trans (le_max_right _ _)⟩
  choose C hC hB using hBound
  refine ⟨fun q hq _ _ _ => hf.contDiffAt (hO.mem_nhds (hJO hq)),
    ∑ i : Fin (N+1), C i, Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro q hq _ _ _ _ j hj
  let i : Fin (N+1) := ⟨j,Nat.lt_succ_of_le hj⟩
  rw [mul_one]
  exact (hB i q hq).trans (Finset.single_le_sum (fun k _ => hC k) (mem_univ i))

theorem dephasedResidual_envelope
    (hU : IsOpen U) {K K₀ : Set (P × X n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hK₀ : IsClosed K₀) (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U)
    (ha0 : ∀ q ∉ K₀, a q = 0)
    {O J : Set ((P × X n) × ℝ)} (hO : IsOpen O) (hJ : IsCompact J) (hJO : J ⊆ O)
    (hJK : ∀ q ∈ J, q.1 ∈ K) (hOU : O ⊆ U ×ˢ (univ : Set ℝ))
    (A : RemainderMatrix n P) (hA : ∀ i l, ContDiffOn ℝ ∞ (fun p => A p i l) O)
    (τ₁ τ₂ : (P × X n) × ℝ → ℂ) (hτ₁ : ContDiffOn ℝ ∞ τ₁ O) (hτ₂ : ContDiffOn ℝ ∞ τ₂ O)
    (c : RemainderDrift n P) (hc : ∀ i, ContDiffOn ℝ ∞ (fun p => c p i) O)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) {d : ℝ} (hd : 0 < d)
    (hzero : ∀ q ∈ O, q.2 < d → deriv η q.2 = 0 ∧ deriv (deriv η) q.2 = 0)
    (M N : ℕ) :
    SmoothCollarContribution J (B.dephasedResidual a η M A τ₁ τ₂ c) N
      (fun h => h^(M+1) * h⁻¹^N) := by
  have hTaylor := B.finiteResidualProfile_scaled_envelope hU hK hKU hK₀ a ha ha0 hJK M N
  have hGap := CalderonPaper.SmoothCollarContribution.sum (range (M+1)) fun j _ =>
    B.taylorGapContribution_envelope hU hK hKU hK₀ a ha ha0 hO hJ hJO hJK hOU
      A hA τ₁ hτ₁ c hc j (M+1) N
  have hCut := CalderonPaper.SmoothCollarContribution.sum (range (M+1)) fun j _ =>
    B.cutoffContribution_envelope hU hK hKU hK₀ a ha ha0 hO hJ hJO hJK
      η hη τ₂ hτ₂ hd hzero j (M+1) N
  have hηC : ContDiffOn ℝ ∞ (fun q : (P × X n) × ℝ => (η q.2 : ℂ)) O :=
    (Complex.ofRealCLM.contDiff.comp (hη.comp contDiff_snd)).contDiffOn
  have hEta := SmoothCollarContribution.compact_unscaled hO hJ hJO hηC N
  have hS := CalderonPaper.SmoothCollarContribution.mul (fun _ _ _ => zero_le_one)
    (fun h hh hh₁ => by positivity) hEta (hTaylor.add hGap)
  have hS' : SmoothCollarContribution J
      (fun h q => (η q.2 : ℂ) * (B.finiteResidualProfile a M h (q.1,q.2/h) +
        ∑ j ∈ range (M+1), B.taylorGapContribution a j (M+1) A τ₁ c h q))
      N (fun h => h^(M+1) * h⁻¹^N) := by simpa only [one_mul] using hS
  exact hS'.add hCut

end CalderonPatch.BoundaryLayer.ParametricLayerCoefficients
