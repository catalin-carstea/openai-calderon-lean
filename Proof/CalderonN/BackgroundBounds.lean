module

public import Proof.CalderonN.SmoothMetricFrame
public import Proof.CalderonN.Coercivity

import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.PrincipalMetric
import Proof.CalderonN.MetricPair
import Proof.CalderonN.DilationConnection
import Mathlib.Tactic

public section

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem norm_iteratedFDeriv_slice_le (F : ℝ × (X dim) → ℝ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (lam : ℝ) (y : (X dim)) :
    ‖iteratedFDeriv ℝ n (fun z => F (lam,z)) y‖ ≤ ‖iteratedFDeriv ℝ n F (lam,y)‖ := by
  let L := ContinuousLinearMap.inr ℝ ℝ (X dim)
  let F' := fun p : ℝ × (X dim) => F ((lam,0) + p)
  have hF' : ContDiff ℝ ∞ F' := hF.comp (contDiff_const.add contDiff_id)
  have he : (fun z => F (lam,z)) = F' ∘ L := by
    funext z
    change F (lam,z) = F (lam + 0, 0 + z)
    rw [add_zero, zero_add]
  rw [he, L.iteratedFDeriv_comp_right hF' y (by simp)]
  have hF'' : iteratedFDeriv ℝ n F' (L y) = iteratedFDeriv ℝ n F (lam,y) := by
    change iteratedFDeriv ℝ n (fun p => F ((lam,0) + p)) (L y) = _
    rw [iteratedFDeriv_comp_add_left]
    change iteratedFDeriv ℝ n F (lam + 0, 0 + y) = _
    rw [add_zero, zero_add]
  rw [hF'']
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg L)
    (ContinuousLinearMap.norm_inr_le_one ℝ ℝ (X dim) : ‖L‖ ≤ 1)) (norm_nonneg _)).trans_eq (mul_one _)

theorem contDiff_family_drift
    {γ g : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hg : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g q.1 q.2 i j))
    (hγp : ∀ lam y, (γ lam y).PosDef) (hgp : ∀ lam y, (g lam y).PosDef) (k : (I dim)) :
    ContDiff ℝ ∞ (fun q : ℝ × (X dim) => drift (γ q.1) (g q.1) q.2 k) := by
  have hP (i j : (I dim)) := contDiffOn_normalized_inv_entry_of_entries (Ω := univ)
    (fun a b => (hγ a b).contDiffOn) (fun a b => (hg a b).contDiffOn)
    (fun (q : ℝ × (X dim)) _ => hγp q.1 q.2) (fun q _ => hgp q.1 q.2) i j
  have hΓ (i j : (I dim)) := contDiffOn_christoffel_slice (U := univ) isOpen_univ
    (fun a b => (hγ a b).contDiffOn) (fun (q : ℝ × (X dim)) _ => hγp q.1 q.2) k i j
  have hG (i j : (I dim)) := contDiffOn_christoffel_slice (U := univ) isOpen_univ
    (fun a b => (hg a b).contDiffOn) (fun (q : ℝ × (X dim)) _ => hgp q.1 q.2) k i j
  apply contDiffOn_univ.mp
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hP i j).mul ((hΓ i j).sub (hG i j))

private theorem exists_uniform_elliptic {S : Set ℝ} {D Ω : Set (X dim)}
    (hS : IsCompact S) (hD : IsCompact D) (hΩD : Ω ⊆ D)
    {g : ℝ → (MetricField dim)}
    (hg : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g q.1 q.2 i j))
    (hpos : ∀ lam y, (g lam y).PosDef) :
    ∃ K ≥ (1 : ℝ), ∀ A ≥ K, ∀ lam ∈ S, Elliptic Ω A (g lam) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := exists_uniform_metric_comparison (hS.prod hD)
    (g := fun q : ℝ × (X dim) => g q.1 q.2) (fun i j => (hg i j).continuous.continuousOn)
    (fun q _ => hpos q.1 q.2)
  let K := max 1 (max c⁻¹ C)
  refine ⟨K, le_max_left _ _, fun A hA lam hlam => ?_⟩
  have hApos : 0 < A := zero_lt_one.trans_le ((le_max_left _ _).trans hA)
  have hcA : c⁻¹ ≤ A := (le_max_left _ _).trans ((le_max_right _ _).trans hA)
  have hCA : C ≤ A := (le_max_right _ _).trans ((le_max_right _ _).trans hA)
  have hc' : A⁻¹ ≤ c := by
    have h := inv_le_inv₀ hApos (inv_pos.mpr hc) |>.mpr hcA
    simpa only [inv_inv] using h
  refine ⟨fun i j => ((hg i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn, ?_⟩
  intro y hy
  refine ⟨(hpos lam y).isHermitian.isSymm.eq, fun v => ?_⟩
  obtain ⟨hlo, hhi⟩ := hbound (lam,y) ⟨hlam,hΩD hy⟩ v
  exact ⟨(mul_le_mul_of_nonneg_right hc' (sq_nonneg _)).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right hCA (sq_nonneg _))⟩

/-- Uniform background data in the exact protected form, on an open
region contained in a compact coordinate set. -/
theorem exists_uniform_background
    {S : Set ℝ} {D Ω : Set (X dim)} (hS : IsCompact S) (hD : IsCompact D) (hΩD : Ω ⊆ D)
    {γ g₁ g₂ : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (h₁ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g₁ q.1 q.2 i j))
    (h₂ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g₂ q.1 q.2 i j))
    (hpγ : ∀ lam y, (γ lam y).PosDef) (hp₁ : ∀ lam y, (g₁ lam y).PosDef)
    (hp₂ : ∀ lam y, (g₂ lam y).PosDef)
    (hconformal : ∀ lam ∈ S, ∀ y ∈ Ω, ∃ a : ℝ, 0 < a ∧ γ lam y = a • g₁ lam y)
    (m : ℕ) :
    ∃ K ≥ (1 : ℝ), ∃ M : Fin (m+1) → ℝ, ∀ lam ∈ S,
      Background Ω K M (γ lam) (g₁ lam) (g₂ lam) (fun y => smoothMetricFrame (γ lam y)) := by
  obtain ⟨A, hA, heγ⟩ := exists_uniform_elliptic hS hD hΩD hγ hpγ
  obtain ⟨B, hB, he₁⟩ := exists_uniform_elliptic hS hD hΩD h₁ hp₁
  obtain ⟨C, hC, he₂⟩ := exists_uniform_elliptic hS hD hΩD h₂ hp₂
  let T := S ×ˢ D
  have hT : IsCompact T := hS.prod hD
  have hbd (n : ℕ) (f : ℝ × (X dim) → ℝ) (hf : ContDiff ℝ ∞ f) :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ lam ∈ S, ∀ y ∈ Ω,
        ‖iteratedFDeriv ℝ n (fun z => f (lam,z)) y‖ ≤ R := by
    obtain ⟨R, hR⟩ := hT.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by simp : (n : ℕ∞ω) ≤ ∞)).continuousOn
    exact ⟨max 0 R, le_max_left _ _, fun lam hlam y hy =>
      (norm_iteratedFDeriv_slice_le f hf n lam y).trans ((hR (lam,y) ⟨hlam,hΩD hy⟩).trans
        (le_max_right _ _))⟩
  choose G hG₀ hG using fun (j : Fin (m+1)) (i l : (I dim)) => hbd j (fun q => γ q.1 q.2 i l) (hγ i l)
  choose H hH₀ hH using fun (j : Fin (m+1)) (i l : (I dim)) => hbd j (fun q => g₁ q.1 q.2 i l) (h₁ i l)
  let M (j : Fin (m+1)) := ∑ i : (I dim), ∑ l : (I dim), (G j i l + H j i l)
  have hM (j : Fin (m+1)) (i l : (I dim)) : G j i l + H j i l ≤ M j := by
    apply (Finset.single_le_sum (f := fun t => G j i t + H j i t)
      (fun t _ => add_nonneg (hG₀ j i t) (hH₀ j i t)) (Finset.mem_univ l)).trans
    exact Finset.single_le_sum (f := fun t : (I dim) => ∑ u : (I dim), (G j t u + H j t u))
      (fun t _ => Finset.sum_nonneg fun u _ => add_nonneg (hG₀ j t u) (hH₀ j t u)) (Finset.mem_univ i)
  have hDrift (i : (I dim)) := hT.exists_bound_of_continuousOn
    (contDiff_family_drift hγ h₂ hpγ hp₂ i).continuous.continuousOn
  choose R hR using hDrift
  let Q := ∑ i : (I dim), max 0 (R i)
  have hRQ (i : (I dim)) : R i ≤ Q := (le_max_right _ _).trans
    (Finset.single_le_sum (fun j _ => le_max_left 0 (R j)) (Finset.mem_univ i))
  let K := max (max A B) (max C Q)
  refine ⟨K, hA.trans ((le_max_left _ _).trans (le_max_left _ _)), M, fun lam hlam => ?_⟩
  refine ⟨heγ K ((le_max_left _ _).trans (le_max_left _ _)) lam hlam,
    he₁ K ((le_max_right _ _).trans (le_max_left _ _)) lam hlam,
    he₂ K ((le_max_left _ _).trans (le_max_right _ _)) lam hlam, hconformal lam hlam, ?_, ?_, ?_, ?_⟩
  · intro g hg j i l y hy
    rcases mem_insert_iff.mp hg with (rfl | hg)
    · exact (hG j i l lam hlam y hy).trans ((le_add_of_nonneg_right (hH₀ j i l)).trans (hM j i l))
    · have he : g = g₁ lam := mem_singleton_iff.mp hg
      rw [he]
      exact (hH j i l lam hlam y hy).trans ((le_add_of_nonneg_left (hG₀ j i l)).trans (hM j i l))
  · intro y hy i
    exact (hR i (lam,y) ⟨hlam,hΩD hy⟩).trans ((hRQ i).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  · intro i
    exact contDiffOn_smoothMetricFrame
      (fun a b => ((hγ a b).comp (contDiff_const.prodMk contDiff_id)).contDiffOn)
      (fun y _ => hpγ lam y) i
  · intro y _ i j
    exact smoothMetricFrame_orthonormal (hpγ lam y) i j

end CalderonN
