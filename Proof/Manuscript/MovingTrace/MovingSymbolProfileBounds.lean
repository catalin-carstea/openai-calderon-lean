module

public import Proof.Manuscript.MovingTraceSymbols
public import Proof.CalderonN.ActualTraceProfileScalarJets
public import Proof.CalderonN.MixedSliceJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Proof.CalderonN.WeakEnergyConormalJets

@[expose] public section

noncomputable section
set_option maxHeartbeats 3200000

open CalderonN Set
open scoped ContDiff

namespace CalderonPaper

variable {d : ℕ} [NeZero d]

private theorem uniform_compact_metric_entry_jets
    {F : ℝ × X d → Mat d} (hF : ∀ i j, ContDiff ℝ ∞ (fun q => F q i j))
    {Z : Set (X d)} (hZ : IsCompact Z) (k : ℕ) :
    ∃ M : Fin (k+1) → ℝ, ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y ∈ Z, ∀ j i l,
      ‖iteratedFDeriv ℝ j.val (fun x => F (lam,x) i l) y‖ ≤ M j := by
  let J := Icc (0:ℝ) 1 ×ˢ Z
  have hJ : IsCompact J := isCompact_Icc.prod hZ
  have hB (i l : I d) (j : Fin (k+1)) :
      ∃ M ≥ 0, ∀ q ∈ J, ‖iteratedFDeriv ℝ j.val (fun x => F (q.1,x) i l) q.2‖ ≤ M := by
    have hC := (contDiff_iteratedFDeriv_slice_right (hF i l) j.val).continuous.norm
    obtain ⟨B,hB⟩ := hJ.bddAbove_image hC.continuousOn
    exact ⟨max B 0,le_max_right _ _,fun q hq => (hB ⟨q,hq,rfl⟩).trans (le_max_left _ _)⟩
  choose B hB hBound using hB
  let M (j : Fin (k+1)) := ∑ i : I d, ∑ l : I d, B i l j
  refine ⟨M,fun lam hlam y hy j i l => ?_⟩
  exact (hBound i l j (lam,y) ⟨hlam,hy⟩).trans
    ((Finset.single_le_sum (fun z _ => hB i z j) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun w _ => hB z w j)) (Finset.mem_univ i)))

theorem uniform_admittedRadius_profile_jets
    {Y Ω : Set (X d)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hComp : IsCompact (closure Y)) (hSub : closure Y ⊆ Ω)
    {γ g₁ g₂ : ℝ → MetricField d}
    (hΓ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X d => γ q.1 q.2 i j))
    (hG₁ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X d => g₁ q.1 q.2 i j))
    {e : ℝ → Frame d} {K : ℝ} (hK : 0 < K)
    {m : ℕ} {M : Fin (m+1) → ℝ}
    (hbg : ∀ lam ∈ Icc (0 : ℝ) 1, Background Ω K M (γ lam) (g₁ lam) (g₂ lam) (e lam))
    {ρ floor c₀ ε : ℝ} (hρ : 0 < ρ) (hfloor : 1 ≤ floor) (hε : 0 ≤ ε)
    (Cj : Fin 9 → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ lam ∈ Icc (0 : ℝ) 1, ∀ r : X d → ℝ,
      AdmittedTraceRadius Y (γ lam) (g₂ lam) (e lam) ρ floor c₀ ε Cj r →
      ∀ y ∈ Y,
        let β := beta (γ lam) r y
        (∀ k ≤ 6, ‖iteratedFDeriv ℝ k r y‖ ≤ C*β^k) ∧
        ∀ i k, k ≤ 6 → ‖iteratedFDeriv ℝ k (coordDeriv i r) y‖ ≤ C*β^k := by
  obtain ⟨Ω',hΩ',hYΩ',hΩ'Ω,hΩ'Comp⟩ := exists_open_between_and_isCompact_closure hComp hΩ hSub
  have h₂ : Ω' ⊆ Ω := subset_closure.trans hΩ'Ω
  obtain ⟨Bγ,hBγ⟩ := uniform_compact_metric_entry_jets hΓ hΩ'Comp 8
  obtain ⟨B₁,hB₁⟩ := uniform_compact_metric_entry_jets hG₁ hΩ'Comp 8
  let B (j : Fin (8+1)) := max (Bγ j) (B₁ j)
  have hBg (lam : ℝ) (hlam : lam ∈ Icc 0 1) :
      Background Ω' K B (γ lam) (g₁ lam) (g₂ lam) (e lam) := by
    have h := hbg lam hlam
    have hmono {g : MetricField d} (hE : Elliptic Ω K g) : Elliptic Ω' K g :=
      ⟨fun i j => (hE.1 i j).mono h₂,fun _ hx => hE.2 _ (h₂ hx)⟩
    refine ⟨hmono h.1,hmono h.2.1,hmono h.2.2.1,fun y hy => h.2.2.2.1 y (h₂ hy),?_,
      fun y hy => h.2.2.2.2.2.1 y (h₂ hy),fun i => (h.2.2.2.2.2.2.1 i).mono h₂,
      fun y hy => h.2.2.2.2.2.2.2 y (h₂ hy)⟩
    intro g hg j i l y hy
    rcases (show g = γ lam ∨ g = g₁ lam from by simpa using hg) with rfl | rfl
    · exact (hBγ lam hlam y (subset_closure hy) j i l).trans (le_max_left _ _)
    · exact (hB₁ lam hlam y (subset_closure hy) j i l).trans (le_max_right _ _)
  obtain ⟨A,hA,hLog⟩ := uniform_background_logRadius_chart_jets hY hΩ'
    (subset_closure.trans hYΩ') 7 (by omega) (by omega : 7+1 ≤ 8) K B Cj hK
  obtain ⟨D,hD,hRad⟩ := uniform_radius_scaled_chart_jets hY 7 (1+A) (le_add_of_nonneg_right hA)
  let C := 1 + D*(ρ+ε)
  have hC : 1 ≤ C := le_add_of_nonneg_right (mul_nonneg hD (add_nonneg hρ.le hε))
  refine ⟨C,hC,?_⟩
  intro lam hlam r hr y hy
  dsimp only
  let β := beta (γ lam) r y
  have hβ := hfloor.trans (hr.2.1.2 y hy).2.1
  have hβp := zero_lt_one.trans_le hβ
  have hrp (z : X d) (hz : z ∈ Y) := (hr.2.1.2 z hz).1
  have hlog := hLog _ _ _ _ (hBg lam hlam) r floor c₀ hfloor hr.2.1 y hy
  have hR := (hRad r hr.1.contDiffOn y hy hrp β hβ (fun k hk hk₀ =>
    (hlog k hk hk₀).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
      (pow_nonneg hβp.le k)))).1
  have hR' := hR.const_smul (r y) (hrp y hy).le
  have hEq : (fun x : X d => r y • (r (y+β⁻¹ • x)/r y)) =
      fun x => r (y+β⁻¹ • x) := by
    funext x
    rw [smul_eq_mul]
    field_simp [(hrp y hy).ne']
  rw [hEq] at hR'
  have hbD (k : ℕ) (hk : k ≤ 7) : ‖iteratedFDeriv ℝ k r y‖ ≤ (r y*D)*β^k :=
    localSmoothJetBudget_scaled_chart_bound hβ hR' k hk
  have hρD : r y * D ≤ C := by
    dsimp only [C]
    nlinarith only [hr.2.2.2 y hy,hD,hε]
  have hSmall : r y * β ≤ ε :=
    (mul_le_mul_of_nonneg_left (by simpa only [pow_one] using pow_le_pow_right₀ hβ (by omega : 1 ≤ 2))
      (hrp y hy).le).trans ((hr.2.2.1 y hy).2)
  have hεD : (r y*D)*β ≤ C := by
    rw [mul_right_comm]
    dsimp only [C]
    nlinarith only [hSmall,hD,hρ.le]
  refine ⟨fun k hk => (hbD k (by omega)).trans (mul_le_mul_of_nonneg_right hρD (by positivity)),?_⟩
  intro i k hk
  refine (norm_iteratedFDeriv_coordDeriv_le hr.1.contDiffAt i k).trans ((hbD (k+1) (by omega)).trans ?_)
  calc
    _ = ((r y*D)*β)*β^k := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hεD (pow_nonneg hβp.le _)

end CalderonPaper
