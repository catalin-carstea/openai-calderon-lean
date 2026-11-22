module

public import Proof.CalderonN.CenterJetCalculus

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

/-! Finite pointwise jet budgets for maps composed in the normal-coordinate
coefficients. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace CalderonN

variable {P E F G : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure LocalSmoothJetBudget (f : P → E) (x : P) (N : ℕ) (C : ℝ) : Prop where
  smooth : ContDiffAt ℝ ∞ f x
  bound : ∀ n ≤ N, ‖iteratedFDeriv ℝ n f x‖ ≤ C

namespace LocalSmoothJetBudget

variable {f : P → E} {g : P → F} {x : P} {N : ℕ} {A B : ℝ}

theorem nonneg (h : LocalSmoothJetBudget f x N A) : 0 ≤ A :=
  (norm_nonneg _).trans (h.bound 0 (Nat.zero_le _))

theorem enlarge (h : LocalSmoothJetBudget f x N A) (hAB : A ≤ B) : LocalSmoothJetBudget f x N B :=
  ⟨h.smooth, fun n hn => (h.bound n hn).trans hAB⟩

theorem value_norm_le (h : LocalSmoothJetBudget f x N A) : ‖f x‖ ≤ A := by
  simpa only [norm_iteratedFDeriv_zero] using h.bound 0 (Nat.zero_le _)

theorem const (c : E) : LocalSmoothJetBudget (fun _ : P => c) x N ‖c‖ := by
  refine ⟨contDiffAt_const,?_⟩
  intro n _
  cases n with
  | zero => rw [norm_iteratedFDeriv_zero]
  | succ n => simp [iteratedFDeriv_succ_const]

theorem prod (hf : LocalSmoothJetBudget f x N A) (hg : LocalSmoothJetBudget g x N B) :
    LocalSmoothJetBudget (fun y => (f y,g y)) x N (max A B) :=
  ⟨hf.smooth.prodMk hg.smooth,
    fun n hn => norm_iteratedFDeriv_prod_envelope_at f g x n hf.smooth hg.smooth (hf.bound n hn) (hg.bound n hn)⟩

theorem linear_postcomp (hf : LocalSmoothJetBudget f x N A) (L : E →L[ℝ] F) :
    LocalSmoothJetBudget (L ∘ f) x N (‖L‖*A) := by
  refine ⟨L.contDiff.contDiffAt.comp x hf.smooth,?_⟩
  intro n hn
  exact (L.norm_iteratedFDeriv_comp_left (hf.smooth.of_le (by simp : (n:ℕ∞ω) ≤ ∞)) (n:=n) le_rfl).trans
    (mul_le_mul_of_nonneg_left (hf.bound n hn) (norm_nonneg _))

theorem bilinear (hf : LocalSmoothJetBudget f x N A) (hg : LocalSmoothJetBudget g x N B)
    (L : E →L[ℝ] F →L[ℝ] G) :
    LocalSmoothJetBudget (fun y => L (f y) (g y)) x N ((2:ℝ)^N*‖L‖*A*B) := by
  refine ⟨(L.contDiff.contDiffAt.comp x hf.smooth).clm_apply hg.smooth,?_⟩
  intro n hn
  exact (norm_iteratedFDeriv_bilinear_envelope_at L f g x n hf.smooth hg.smooth A B hf.nonneg hg.nonneg
    (fun j hj => hf.bound j (hj.trans hn)) (fun j hj => hg.bound j (hj.trans hn))).trans (by
      have hA := hf.nonneg
      have hB := hg.nonneg
      gcongr
      norm_num)

theorem fderiv (hf : LocalSmoothJetBudget f x (N+1) A) :
    LocalSmoothJetBudget (fderiv ℝ f) x N A := by
  refine ⟨hf.smooth.fderiv_right (m:=∞) (by simp),?_⟩
  intro n hn
  rw [norm_iteratedFDeriv_fderiv]
  exact hf.bound _ (by omega)

theorem comp_of_positive_inner {g : E → F} (hf : ContDiffAt ℝ ∞ f x)
    (hg : LocalSmoothJetBudget g (f x) N B) (hA : 1 ≤ A)
    (hJets : ∀ j, 1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j f x‖ ≤ A) :
    LocalSmoothJetBudget (g ∘ f) x N (N.factorial*B*A^N) := by
  refine ⟨hg.smooth.comp x hf,?_⟩
  intro n hn
  have h := norm_iteratedFDeriv_comp_at_le f g x n hf hg.smooth B A
    (fun k hk => hg.bound k (hk.trans hn))
    (fun k hk hkn => (hJets k hk (hkn.trans hn)).trans (le_self_pow₀ hA (by omega)))
  have hFac : (n.factorial:ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hn
  have hB := hg.nonneg
  exact h.trans (by gcongr)

theorem comp {g : E → F} (hf : LocalSmoothJetBudget f x N A)
    (hg : LocalSmoothJetBudget g (f x) N B) (hA : 1 ≤ A) :
    LocalSmoothJetBudget (g ∘ f) x N (N.factorial*B*A^N) :=
  comp_of_positive_inner hf.smooth hg hA (fun k _ hk => hf.bound k hk)

theorem linear_precomp (L : F →L[ℝ] P) (y : F) (h : LocalSmoothJetBudget f (L y) N A) :
    LocalSmoothJetBudget (f ∘ L) y N (N.factorial*A*(max 1 ‖L‖)^N) := by
  apply comp_of_positive_inner L.contDiff.contDiffAt h (le_max_left _ _)
  intro n hn _
  cases n with
  | zero => omega
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hD : _root_.fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
    rw [hD]
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero] using le_max_right (1:ℝ) ‖L‖
    | succ n => simpa only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero] using
        (zero_le_one.trans (le_max_left (1:ℝ) ‖L‖))

theorem mono_order {n : ℕ} (h : LocalSmoothJetBudget f x N A) (hn : n ≤ N) :
    LocalSmoothJetBudget f x n A :=
  ⟨h.smooth,fun i hi => h.bound i (hi.trans hn)⟩

theorem finite_sum {ι : Type*} (S : Finset ι) (H : ι → P → E) (C : ι → ℝ)
    (h : ∀ i ∈ S, LocalSmoothJetBudget (H i) x N (C i)) :
    LocalSmoothJetBudget (fun y => ∑ i ∈ S,H i y) x N (∑ i ∈ S,C i) := by
  refine ⟨ContDiffAt.sum (fun i hi => (h i hi).smooth),?_⟩
  intro n hn
  obtain ⟨U,hU,hx,hG⟩ : ∃ U : Set P, IsOpen U ∧ x ∈ U ∧
      ∀ i ∈ S, ContDiffOn ℝ (n:ℕ∞ω) (H i) U := by
    classical
    have hh (i : ι) (hi : i ∈ S) : ∃ U : Set P, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ (n:ℕ∞ω) (H i) U := by
      obtain ⟨V,hV,hf⟩ := (h i hi).smooth.contDiffOn (m:=(n:ℕ∞ω)) (by simp) (by simp)
      obtain ⟨U,hUV,hU,hx⟩ := mem_nhds_iff.mp hV
      exact ⟨U,hU,hx,hf.mono hUV⟩
    choose U hU hx hG using hh
    let V := ⋂ i : S, U i i.2
    exact ⟨V,isOpen_iInter_of_finite (fun i : S => hU i i.2),
      Set.mem_iInter.mpr (fun i => hx i i.2),
      fun i hi => (hG i hi).mono (Set.iInter_subset (fun j : S => U j j.2) ⟨i,hi⟩)⟩
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun i hi => (h i hi).nonneg)
  intro v
  rw [← iteratedFDerivWithin_of_isOpen n hU hx,
    iteratedFDerivWithin_fun_sum_apply hU.uniqueDiffOn hx (fun i hi => hG i hi x hx)]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine (norm_sum_le S (fun i => iteratedFDerivWithin ℝ n (H i) U x v)).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [iteratedFDerivWithin_of_isOpen n hU hx]
  exact ((iteratedFDeriv ℝ n (H i) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((h i hi).bound n hn) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

end LocalSmoothJetBudget

end CalderonN
