module

public import Proof.Manuscript.MovingTrace.ActualCollarWaveResidual
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2400000

open CalderonPatch.BoundaryLayer Set Finset
open scoped ContDiff

namespace CalderonPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem SmoothCollarContribution.mono_weight {J : Set (E × ℝ)}
    {f : ℝ → E × ℝ → ℂ} {N : ℕ} {a b : ℝ → ℝ}
    (hf : SmoothCollarContribution J f N a)
    (hab : ∀ h : ℝ, 0 < h → h ≤ 1 → a h ≤ b h) :
    SmoothCollarContribution J f N b := ⟨hf.1,hf.2.mono_weight hab⟩

theorem SmoothCollarContribution.congr_on_open
    {O J : Set (E × ℝ)} (hO : IsOpen O) (hJO : J ⊆ O)
    {f g : ℝ → E × ℝ → ℂ} {N : ℕ} {a : ℝ → ℝ}
    (hf : SmoothCollarContribution J f N a)
    (hEq : ∀ h : ℝ, 0 < h → h ≤ 1 → EqOn (g h) (f h) O) :
    SmoothCollarContribution J g N a := by
  have hE (q) (hq : q ∈ J) (h) (hh : 0 < h) (hh₁ : h ≤ 1) :
      (g h) =ᶠ[nhds q] f h :=
    Filter.mem_of_superset (hO.mem_nhds (hJO hq)) (hEq h hh hh₁)
  refine ⟨fun q hq h hh hh₁ => (hf.1 q hq h hh hh₁).congr_of_eventuallyEq (hE q hq h hh hh₁), ?_⟩
  obtain ⟨C,hC,hB⟩ := hf.2
  refine ⟨C,hC,fun q hq h hh hh₁ ht j hj => ?_⟩
  rw [← iteratedFDerivWithin_of_isOpen j hO (hJO hq),
    iteratedFDerivWithin_congr (hEq h hh hh₁) (hJO hq) j,
    iteratedFDerivWithin_of_isOpen j hO (hJO hq)]
  exact hB q hq h hh hh₁ ht j hj

theorem SmoothCollarContribution.oscillatory
    {O J : Set (E × ℝ)} (hO : IsOpen O) (hJ : IsCompact J) (hJO : J ⊆ O)
    {phase : E × ℝ → ℝ} (hp : ContDiffOn ℝ ∞ phase O) (N : ℕ) :
    SmoothCollarContribution J (fun h q => Complex.exp (Complex.I * (phase q / h : ℝ))) N
      (fun h => h⁻¹^N) := by
  have hD (j : Fin (N+1)) : ContinuousOn (fun q => ‖iteratedFDeriv ℝ j.val phase q‖) O :=
    fun q hq => ((hp.contDiffAt (hO.mem_nhds hq)).continuousAt_iteratedFDeriv
      (by simp)).norm.continuousWithinAt
  have hBound (j : Fin (N+1)) : ∃ C ≥ 0, ∀ q ∈ J, ‖iteratedFDeriv ℝ j.val phase q‖ ≤ C := by
    obtain ⟨r,hr⟩ := hJ.bddAbove_image ((hD j).mono hJO)
    exact ⟨max 0 r,le_max_left _ _,fun q hq => (hr ⟨q,hq,rfl⟩).trans (le_max_right _ _)⟩
  choose C hC hB using hBound
  let A := 1 + ∑ i : Fin (N+1), C i
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hC i)
  have hps (q) (hq : q ∈ J) : ContDiffAt ℝ ∞ phase q := hp.contDiffAt (hO.mem_nhds (hJO hq))
  refine ⟨fun q hq h _ _ => (contDiffAt_const.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp q ((hps q hq).div_const h))).cexp, ?_⟩
  refine ⟨(N.factorial : ℝ) * oscillatoryPhaseJetBound * A^N,
    mul_nonneg (mul_nonneg (by positivity) oscillatoryPhaseJetBound_nonneg)
      (pow_nonneg (zero_le_one.trans hA) _), ?_⟩
  intro q hq h hh hh₁ _ j hj
  refine norm_iteratedFDeriv_oscillatoryPhase_le (hps q hq) hA N ?_ hh hh₁ j hj
  intro i _ hi
  let j : Fin (N+1) := ⟨i,Nat.lt_succ_of_le hi⟩
  exact (hB j q hq).trans ((Finset.single_le_sum (fun k _ => hC k) (mem_univ j)).trans
    (le_add_of_nonneg_left zero_le_one))

theorem SmoothCollarContribution.invPower {J : Set (E × ℝ)} (n N : ℕ) :
    SmoothCollarContribution J (fun h _ => ((h : ℂ)⁻¹)^n) N (fun h => h⁻¹^n) := by
  refine ⟨fun _ _ _ _ _ => contDiffAt_const, 1, zero_le_one, ?_⟩
  intro q hq h hh hh₁ ht j hj
  cases j with
  | zero =>
    simp [norm_iteratedFDeriv_zero, norm_pow, norm_inv, Real.norm_of_nonneg hh.le]
  | succ j =>
    rw [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
    positivity

/-- Remove the normalization h² and restore the carrier while retaining
arbitrary decay from the number of layers. -/
theorem oscillatoryResidual_envelope
    {O J : Set (E × ℝ)} (hO : IsOpen O) (hJ : IsCompact J) (hJO : J ⊆ O)
    {phase : E × ℝ → ℝ} (hp : ContDiffOn ℝ ∞ phase O)
    {f g : ℝ → E × ℝ → ℂ} {M N : ℕ}
    (hf : SmoothCollarContribution J f N (fun h => h^(M+1) * h⁻¹^N))
    (hG : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ q ∈ O,
      (h : ℂ)^2 * g h q = Complex.exp (Complex.I * (phase q / h : ℝ)) * f h q) :
    SmoothCollarContribution J g N (fun h => h^(M+1) * h⁻¹^(2*N+2)) := by
  have hi := SmoothCollarContribution.invPower (J := J) 2 N
  have he := SmoothCollarContribution.oscillatory hO hJ hJO hp N
  have hEF := he.mul (fun h hh _ => by positivity) (fun h hh _ => by positivity) hf
  have hF := hi.mul (fun h hh _ => by positivity) (fun h hh _ => by positivity) hEF
  have hF' := hF.mono_weight (b := fun h => h^(M+1) * h⁻¹^(2*N+2)) (by
    intro h hh hh₁
    rw [two_mul,pow_add,pow_add]
    ring_nf
    exact le_rfl)
  apply hF'.congr_on_open hO hJO
  intro h hh hh₁ q hq
  change g h q = ((h : ℂ)⁻¹)^2 * (Complex.exp (Complex.I * (phase q / h : ℝ)) * f h q)
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  rw [← hG h hh hh₁ q hq, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hh', one_pow, one_mul]

end CalderonPaper
