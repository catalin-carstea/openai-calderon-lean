module

public import Proof.CalderonN.LocalBoundedProductCross
public import Proof.CalderonN.ProductPhaseSweep

import Mathlib.Tactic

@[expose] public section

set_option maxHeartbeats 2000000

open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private def locallyUniformValueRegion (F : ℝ → (X dim) × (X dim) → ℝ) : Set ((X dim) × (X dim)) :=
  {q | ∃ U : Set ((X dim) × (X dim)), IsOpen U ∧ q ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ z ∈ U, |F lam z| ≤ C}

private theorem isOpen_locallyUniformValueRegion (F : ℝ → (X dim) × (X dim) → ℝ) :
    IsOpen (locallyUniformValueRegion F) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro q ⟨U,hU,hq,C,hC,h⟩
  exact mem_of_superset (hU.mem_nhds hq) (fun _ hz => ⟨U,hU,hz,C,hC,h⟩)

private theorem exists_compact_bound_of_locallyUniformValueRegion {F : ℝ → (X dim) × (X dim) → ℝ}
    {K : Set ((X dim) × (X dim))} (hK : IsCompact K) (hKR : K ⊆ locallyUniformValueRegion F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ q ∈ K, |F lam q| ≤ C := by
  classical
  choose U hU hqU C hC h using fun q : K => hKR q.property
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU
    (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hqU ⟨q,hq⟩⟩)
  let B := ∑ q ∈ s, C q
  refine ⟨B,Finset.sum_nonneg (fun q _ => hC q),?_⟩
  have h' := (eventually_all_finset s).mpr (fun q _ => h q)
  filter_upwards [h'] with lam h' hp q hq
  obtain ⟨z, hqz⟩ := mem_iUnion.mp (hs hq)
  obtain ⟨hz,hqz⟩ := mem_iUnion.mp hqz
  exact (h' z hz hp q hqz).trans
    (Finset.single_le_sum (fun x _ => hC x) hz)

/-- An open region that contains the top and can cross every compact
level from above contains the entire open swept interval. -/
private theorem image_above_subset_of_local_step
    {Z : Type*} [TopologicalSpace Z] (e : OpenPartialHomeomorph ((X dim) × (X dim)) (Z × ℝ))
    {K : Set Z} (hK : IsCompact K) {W : Set ((X dim) × (X dim))} (hW : IsOpen W)
    {amin amax upper : ℝ} (hab : amin ≤ amax) (hhi : amax < upper)
    (htarget : K ×ˢ Ico amin upper ⊆ e.target)
    (htop : e.symm '' (K ×ˢ Ioo amax upper) ⊆ W)
    (hstep : ∀ a ∈ Ioc amin amax, e.symm '' (K ×ˢ Ioo a upper) ⊆ W →
      ∀ z ∈ K, e.symm (z,a) ∈ W) :
    e.symm '' (K ×ˢ Ioo amin upper) ⊆ W := by
  let A (a : ℝ) := e.symm '' (K ×ˢ Ioo a upper)
  let R : Set ℝ := {a ∈ Icc amin amax | A a ⊆ W}
  have hTopR : amax ∈ R := ⟨⟨hab,le_rfl⟩,htop⟩
  have hne : R.Nonempty := ⟨amax,hTopR⟩
  have hbd : BddBelow R := ⟨amin,fun a ha => ha.1.1⟩
  let a := sInf R
  have ha : a ∈ Icc amin amax :=
    ⟨le_csInf hne (fun _ h => h.1.1),csInf_le hbd hTopR⟩
  have hAbove : A a ⊆ W := by
    rintro q ⟨⟨z,t⟩,⟨hz,hat,htu⟩,rfl⟩
    obtain ⟨b,hb,hbt⟩ := exists_lt_of_csInf_lt hne hat
    exact hb.2 ⟨(z,t),⟨hz,hbt,htu⟩,rfl⟩
  have hae : a = amin := by
    by_contra hneq
    have ham : amin < a := lt_of_le_of_ne ha.1 (Ne.symm hneq)
    let T := e.target ∩ e.symm ⁻¹' W
    have hT : IsOpen T := e.continuousOn_symm.isOpen_inter_preimage e.open_target hW
    have hKT : K ×ˢ ({a} : Set ℝ) ⊆ T := by
      rintro ⟨z,t⟩ ⟨hz,ht⟩
      change t ∈ ({a} : Set ℝ) at ht
      rw [mem_singleton_iff] at ht
      subst t
      exact ⟨htarget ⟨hz,ha.1,ha.2.trans_lt hhi⟩,hstep a ⟨ham,ha.2⟩ hAbove z hz⟩
    obtain ⟨U,V,_,hV,hKU,haV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton hT hKT
    obtain ⟨d,hd,hDV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (haV (mem_singleton a)))
    let b := max amin (a-d/2)
    have hba : b < a := max_lt ham (by linarith)
    have hb : b ∈ R := by
      refine ⟨⟨le_max_left _ _,hba.le.trans ha.2⟩,?_⟩
      rintro q ⟨⟨z,t⟩,⟨hz,hbt,htu⟩,rfl⟩
      by_cases hat : a < t
      · exact hAbove ⟨(z,t),⟨hz,hat,htu⟩,rfl⟩
      · have ht : t ∈ ball a d := by
          rw [mem_ball,Real.dist_eq,abs_lt]
          have hlow := (le_max_right amin (a-d/2)).trans_lt hbt
          exact ⟨by linarith,by linarith [le_of_not_gt hat]⟩
        exact (hUV ⟨hKU hz,hDV ht⟩).2
    exact (not_lt_of_ge (csInf_le hbd hb)) hba
  rw [← hae]
  exact hAbove

/-- Uniform compact-subset bounds propagate across the compact cylinder
for a family of already continued product solutions. -/
theorem exists_uniform_bound_across_phase_cylinder
    {Z : Type*} [TopologicalSpace Z] (e : OpenPartialHomeomorph ((X dim) × (X dim)) (Z × ℝ))
    {K : Set Z} (hK : IsCompact K) {S : Set ((X dim) × (X dim))} (hS : IsOpen S)
    {amin amax upper : ℝ} (hab : amin ≤ amax) (hhi : amax < upper)
    (htarget : K ×ˢ Ico amin upper ⊆ e.target)
    (htop : e.symm '' (K ×ˢ Ioo amax upper) ⊆ S)
    (hside : e.symm '' ((K \ interior K) ×ˢ Ioc amin amax) ⊆ S)
    {g₁ g₂ : ℝ → (MetricField dim)}
    (hg₁ : ∀ lam, SmoothMetric univ (g₁ lam)) (hg₂ : ∀ lam, SmoothMetric univ (g₂ lam))
    (hgm₁ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g₁ q.1 q.2 i j))
    (hgm₂ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g₂ q.1 q.2 i j))
    (ha₁ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => divergenceCoeff (g₁ q.1) q.2 i j))
    (ha₂ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => divergenceCoeff (g₂ q.1) q.2 i j))
    (F : ℝ → (X dim) × (X dim) → ℝ)
    (hF : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ProductSolutionOn (g₁ lam) (g₂ lam) (e.symm '' (interior K ×ˢ Ioo amin upper)) (F lam))
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hSeed : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ q ∈ S, |F lam q| ≤ C₀)
    (ρ : ℝ → (X dim) × (X dim) → ℝ)
    (hsmooth : ∀ a ∈ Ioc amin amax, ContDiffOn ℝ ∞ (ρ a) (e.symm '' (interior K ×ˢ Ioo amin upper)))
    (hzero : ∀ a ∈ Ioc amin amax, ∀ z ∈ interior K, ρ a (e.symm (z,a)) = 0)
    (hsign : ∀ a ∈ Ioc amin amax, ∀ z ∈ interior K, ∀ t ∈ Ioo amin upper,
      0 < ρ a (e.symm (z,t)) → a < t)
    (hstrict : ∀ a ∈ Ioc amin amax, ∀ z ∈ interior K, e.symm (z,a) ∉ S →
      ProductStrictHessianAt (g₁ 0) (g₂ 0) (ρ a) (e.symm (z,a)))
    {T : Set ((X dim) × (X dim))} (hT : IsCompact T)
    (hCover : T ⊆ S ∪ e.symm '' (K ×ˢ Ioo amin upper)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ q ∈ T, |F lam q| ≤ B := by
  let W := locallyUniformValueRegion F
  let U := e.symm '' (interior K ×ˢ Ioo amin upper)
  have hU : IsOpen U := e.isOpen_image_symm_of_subset_target (isOpen_interior.prod isOpen_Ioo)
    (fun q hq => htarget ⟨interior_subset hq.1,hq.2.1.le,hq.2.2⟩)
  have hSW : S ⊆ W := fun x hx => ⟨S,hS,hx,C₀,hC₀,hSeed⟩
  have hStep (a : ℝ) (ha : a ∈ Ioc amin amax)
      (hAbove : e.symm '' (K ×ˢ Ioo a upper) ⊆ W) (z : Z) (hz : z ∈ K) :
      e.symm (z,a) ∈ W := by
    by_cases hn : e.symm (z,a) ∈ S
    · exact hSW hn
    have hz' : z ∈ interior K := by
      by_contra hh
      exact hn (hside ⟨(z,a),⟨⟨hz,hh⟩,ha⟩,rfl⟩)
    have hzU : e.symm (z,a) ∈ U :=
      ⟨(z,a),⟨hz',ha.1,ha.2.trans_lt hhi⟩,rfl⟩
    obtain ⟨V,hV,hzV,_,L,hL,hLpos,C,hC,hLocal⟩ := exists_local_bound_of_productPhase
      hg₁ hg₂ hgm₁ hgm₂ ha₁ ha₂ hU _ hzU (hsmooth a ha) (hzero a ha z hz') (hstrict a ha z hz' hn)
    have hLW : L ⊆ W := by
      intro q hq
      obtain ⟨⟨⟨w,t⟩,⟨hw,ht⟩,rfl⟩,hp⟩ := hLpos hq
      exact hAbove ⟨(w,t),⟨interior_subset hw,hsign a ha w hw t ht hp,ht.2⟩,rfl⟩
    obtain ⟨B,hB,hBnd⟩ := exists_compact_bound_of_locallyUniformValueRegion hL hLW
    refine ⟨V,hV,hzV,C*B,mul_nonneg hC hB,?_⟩
    filter_upwards [hF,hBnd,hLocal] with lam hF hBnd hLocal hpos
    exact hLocal (F lam) B hB (hF hpos) (hBnd hpos)
  have hIW := image_above_subset_of_local_step e hK (isOpen_locallyUniformValueRegion F) hab hhi
    htarget (htop.trans hSW) hStep
  exact exists_compact_bound_of_locallyUniformValueRegion hT (hCover.trans (union_subset hSW hIW))

end CalderonN
