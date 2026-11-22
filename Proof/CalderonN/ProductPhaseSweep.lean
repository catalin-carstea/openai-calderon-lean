module

public import Proof.CalderonN.ProductPropagation
public import Proof.CalderonN.CompactProductCross

import Mathlib.Tactic

@[expose] public section

open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- A smooth defining phase with the source strict test gives qualitative
continuation along a compact parameter cylinder. -/
theorem exists_productSolution_across_compact_phase_cylinder
    {Z : Type*} [TopologicalSpace Z] (e : OpenPartialHomeomorph ((X dim) × (X dim)) (Z × ℝ))
    {K : Set Z} (hK : IsCompact K) {S : Set ((X dim) × (X dim))} (hS : IsOpen S)
    {lo amin amax upper : ℝ} (hlo : lo < amin) (hab : amin ≤ amax) (hhi : amax < upper)
    (htarget : K ×ˢ Ioo lo upper ⊆ e.target)
    (habove : e.symm '' (K ×ˢ Ioo amax upper) ⊆ S)
    (hside : e.symm '' ((K \ interior K) ×ˢ Icc amin amax) ⊆ S)
    (hup : ∀ z ∈ K, ∀ s t : ℝ, s ∈ Ioo lo upper → t ∈ Ioo lo upper →
      s ≤ t → e.symm (z,s) ∈ S → e.symm (z,t) ∈ S)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (Fseed : (X dim) × (X dim) → ℝ) (hseed : ProductSolutionOn g₁ g₂ S Fseed)
    (ρ : ℝ → (X dim) × (X dim) → ℝ)
    (hsmooth : ∀ a ∈ Icc amin amax, ContDiffOn ℝ ∞ (ρ a) (e.symm '' (interior K ×ˢ Ioo lo upper)))
    (hzero : ∀ a ∈ Icc amin amax, ∀ z ∈ interior K, ρ a (e.symm (z,a)) = 0)
    (hsign : ∀ a ∈ Icc amin amax, ∀ z ∈ interior K, ∀ t ∈ Ioo lo upper,
      0 < ρ a (e.symm (z,t)) ↔ a < t)
    (hstrict : ∀ a ∈ Icc amin amax, ∀ z ∈ interior K, e.symm (z,a) ∉ S →
      ProductStrictHessianAt g₁ g₂ (ρ a) (e.symm (z,a))) :
    ∃ O : Set ((X dim) × (X dim)), IsOpen O ∧ S ∪ e.symm '' (K ×ˢ Icc amin amax) ⊆ O ∧
      ∃ G, ProductSolutionOn g₁ g₂ O G ∧ EqOn G Fseed S := by
  apply exists_productSolution_across_compact_cylinder e hK hS hlo hab hhi htarget habove
    hside hup hg₁ hg₂ Fseed hseed
  intro a ha F hF _ z hz hn
  let T := interior K ×ˢ Ioo lo upper
  let U := e.symm '' T
  have hT : IsOpen T := isOpen_interior.prod isOpen_Ioo
  have hTe : T ⊆ e.target := (Set.prod_mono interior_subset Subset.rfl).trans htarget
  have hU : IsOpen U := e.isOpen_image_symm_of_subset_target hT hTe
  have hza : (z,a) ∈ T := ⟨hz,hlo.trans_le ha.1,ha.2.trans_lt hhi⟩
  have hsa : {q ∈ U | 0 < ρ a q} ⊆ productAbove e K S a upper := by
    rintro _ ⟨⟨q,hq,rfl⟩,hpos⟩
    exact Or.inr ⟨q,⟨hq.1,(hsign a ha q.1 hq.1 q.2 hq.2).mp hpos,hq.2.2⟩,rfl⟩
  obtain ⟨D₁,D₂,S₁,S₂,O₁,O₂,hO₁,hO₂,hOb,_,_,_,_,_,G,hG,hagree⟩ :=
    exists_compact_productCross_extension hg₁ hg₂ hU (e.symm (z,a)) ⟨(z,a),hza,rfl⟩
      (hsmooth a ha) (hzero a ha z hz) (hstrict a ha z hz hn) (hF.mono hsa)
  have hca := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (hTe hza))
  have hO := (hO₁.prod hO₂).mem_nhds hOb
  have hN : T ∩ e.symm ⁻¹' (O₁ ×ˢ O₂) ∈ 𝓝 (z,a) :=
    inter_mem (hT.mem_nhds hza) (hca.preimage_mem_nhds hO)
  obtain ⟨B,d,hB,hzB,hd,hBN⟩ := exists_open_vertical_box_of_mem_nhds hN
  have hBN' : B ×ˢ Ioo (a-d) (a+d) ⊆ T := hBN.trans inter_subset_left
  have hmid : a ∈ Ioo (a-d) (a+d) := ⟨sub_lt_self _ hd,lt_add_of_pos_right _ hd⟩
  refine ⟨B,d,G,hB,hzB,fun w hw => (hBN' (a := (w,a)) ⟨hw,hmid⟩).1,hd,
    fun t ht => (hBN' (a := (z,t)) ⟨hzB,ht⟩).2,hG.mono ?_,?_⟩
  · rintro _ ⟨q,hq,rfl⟩
    exact (hBN hq).2
  · rintro _ ⟨q,hq,rfl⟩
    have hqb : q ∈ B ×ˢ Ioo (a-d) (a+d) := ⟨hq.1,hmid.1.trans hq.2.1,hq.2.2⟩
    obtain ⟨hqt,hqO⟩ := hBN hqb
    exact hagree ⟨hqO,⟨⟨q,hqt,rfl⟩,(hsign a ha q.1 hqt.1 q.2 hqt.2).mpr hq.2.1⟩⟩

end CalderonN
