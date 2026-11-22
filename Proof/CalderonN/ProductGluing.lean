module

public import Proof.CalderonN.GreenCross

import Proof.CalderonN.ChartUniqueContinuation
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! The local overlap arguments adapt
`Calderon/MixedKernelConstruction/MixedKernelCompatibleGluing.lean`
at d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

open Set

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Agreement at the initial point follows from one interval path
inside the overlap to an open region of agreement. -/
theorem product_eq_at_of_interval_to_seed
    {U V : Set ((X dim) × (X dim))}
    {A₁ A₂ : Set (X dim)} (hU : IsOpen U) (hV : IsOpen V)
    (hsub : U ⊆ A₁ ×ˢ A₂)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric A₁ g₁) (hg₂ : SmoothMetric A₂ g₂)
    {F G : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ U F) (hG : ProductSolutionOn g₁ g₂ U G)
    (heq : EqOn F G V)
    {z : (X dim) × (X dim)} (hz : z ∈ U)
    (hpath : ∃ (a b : ℝ) (f : ℝ → (X dim) × (X dim)),
      ContinuousOn f (uIcc a b) ∧ f a = z ∧ MapsTo f (uIcc a b) U ∧ f b ∈ V) :
    F z = G z := by
  let C := connectedComponentIn U z
  have hC : IsOpen C := hU.connectedComponentIn
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hz
  have hCU : C ⊆ U := connectedComponentIn_subset U z
  obtain ⟨a, b, f, hf, hstart, hinside, hend⟩ := hpath
  have himg : f '' uIcc a b ⊆ C :=
    (isPreconnected_uIcc.image f hf).subset_connectedComponentIn
      ⟨a, left_mem_uIcc, hstart⟩ (by rintro _ ⟨t, ht, rfl⟩; exact hinside ht)
  have hseed : (C ∩ V).Nonempty := ⟨f b, himg ⟨b, right_mem_uIcc, rfl⟩, hend⟩
  exact product_eqOn_of_eqOn_open hC hCconn.isPreconnected (hCU.trans hsub) (hC.inter hV) hseed
    inter_subset_left hg₁ hg₂ (hF.mono hCU) (hG.mono hCU) (fun q hq => heq hq.2)
    (mem_connectedComponentIn hz)

/-- Agreement on a common open seed propagates along actual interval
paths lying in the overlap. -/
theorem product_eqOn_of_interval_to_seed
    {U V : Set ((X dim) × (X dim))}
    {A₁ A₂ : Set (X dim)} (hU : IsOpen U) (hV : IsOpen V)
    (hsub : U ⊆ A₁ ×ˢ A₂)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric A₁ g₁) (hg₂ : SmoothMetric A₂ g₂)
    {F G : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ U F) (hG : ProductSolutionOn g₁ g₂ U G)
    (heq : EqOn F G V)
    (hpath : ∀ z ∈ U, ∃ (a b : ℝ) (f : ℝ → (X dim) × (X dim)),
      ContinuousOn f (uIcc a b) ∧ f a = z ∧ MapsTo f (uIcc a b) U ∧ f b ∈ V) :
    EqOn F G U := by
  intro z hz
  exact product_eq_at_of_interval_to_seed hU hV hsub hg₁ hg₂ hF hG heq hz (hpath z hz)

/-- Compatible local solutions glue to a single product solution on the
actual union of their open domains. -/
theorem exists_productSolution_iUnion {ι : Type*} {g₁ g₂ : (MetricField dim)}
    (U : ι → Set ((X dim) × (X dim))) (hU : ∀ i, IsOpen (U i))
    (F : ι → (X dim) × (X dim) → ℝ) (hF : ∀ i, ProductSolutionOn g₁ g₂ (U i) (F i))
    (hcompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j)) :
    ∃ G : (X dim) × (X dim) → ℝ, ProductSolutionOn g₁ g₂ (⋃ i, U i) G ∧ ∀ i, EqOn G (F i) (U i) := by
  classical
  let G (z : (X dim) × (X dim)) := if h : ∃ i, z ∈ U i then F (Classical.choose h) z else 0
  have heq (i : ι) : EqOn G (F i) (U i) := by
    intro z hz
    have h : ∃ j, z ∈ U j := ⟨i,hz⟩
    dsimp only [G]
    rw [dite_eq_left h]
    exact hcompat (Classical.choose h) i ⟨Classical.choose_spec h,hz⟩
  have hsol (i : ι) : ProductSolutionOn g₁ g₂ (U i) G :=
    (hF i).congr (hU i) (heq i)
  refine ⟨G, ⟨?_, ?_, ?_⟩, heq⟩
  · refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact ⟨U i, hU i, hi, (hsol i).1.mono inter_subset_right⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (hsol i).2.1 z hi
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (hsol i).2.2 z hi

/-- A common top height is reachable inside two boxes centered at the
same level, even when their base intersection has several components. -/
theorem exists_vertical_overlap_segment {Z : Type*} (B₁ B₂ : Set Z)
    (a d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (z : Z × ℝ)
    (hz : z ∈ (B₁ ×ˢ Ioo (a-d₁) (a+d₁)) ∩ (B₂ ×ˢ Ioo (a-d₂) (a+d₂))) :
    ∃ b : ℝ, a < b ∧ ∀ t ∈ uIcc z.2 b,
      (z.1,t) ∈ (B₁ ×ˢ Ioo (a-d₁) (a+d₁)) ∩ (B₂ ×ˢ Ioo (a-d₂) (a+d₂)) := by
  let b := a + min d₁ d₂ / 2
  have hm : 0 < min d₁ d₂ := lt_min hd₁ hd₂
  have h₁ : a-d₁ < b ∧ b < a+d₁ := by
    dsimp [b]
    constructor <;> linarith [min_le_left d₁ d₂]
  have h₂ : a-d₂ < b ∧ b < a+d₂ := by
    dsimp [b]
    constructor <;> linarith [min_le_right d₁ d₂]
  refine ⟨b, by dsimp [b]; linarith, ?_⟩
  intro t ht
  have hbounds : a-d₁ < t ∧ t < a+d₁ ∧ a-d₂ < t ∧ t < a+d₂ := by
    rcases Set.mem_uIcc.mp ht with ⟨hl,hu⟩ | ⟨hl,hu⟩
    · exact ⟨hz.1.2.1.trans_le hl, hu.trans_lt h₁.2, hz.2.2.1.trans_le hl, hu.trans_lt h₂.2⟩
    · exact ⟨h₁.1.trans_le hl, hu.trans_lt hz.1.2.2, h₂.1.trans_le hl, hu.trans_lt hz.2.2.2⟩
  exact ⟨⟨hz.1.1,hbounds.1,hbounds.2.1⟩,⟨hz.2.1,hbounds.2.2.1,hbounds.2.2.2⟩⟩

end CalderonN
