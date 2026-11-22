module

public import Proof.CalderonPatch.FrontierGram
public import Proof.CalderonPatch.SourceCoordinateChart

@[expose] public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

/-- The same source coordinates on a common target near a frontier
point and its partner, compatible with the old match where defined. -/
structure PairedSourceCharts (Φ : OpenPartialHomeomorph M₂ M₁)
    (f₁ : M₁ → X n) (f₂ : M₂ → X n) (U₁ : Set M₁) (U₂ : Set M₂) (q : M₁) (p : M₂) where
  first : OpenPartialHomeomorph M₁ (X n)
  second : OpenPartialHomeomorph M₂ (X n)
  target_eq : first.target = second.target
  first_center : q ∈ first.source
  second_center : p ∈ second.source
  first_interior : first.source ⊆ (𝓡∂ n).interior M₁
  second_interior : second.source ⊆ (𝓡∂ n).interior M₂
  first_domain : first.source ⊆ U₁
  second_domain : second.source ⊆ U₂
  first_smooth : ContMDiffOn J K ∞ first first.source
  second_smooth : ContMDiffOn J K ∞ second second.source
  first_inverse_smooth : ContMDiffOn K J ∞ first.symm first.target
  second_inverse_smooth : ContMDiffOn K J ∞ second.symm second.target
  first_coordinates : EqOn first f₁ first.source
  second_coordinates : EqOn second f₂ second.source
  inverse_matches : ∀ x ∈ second.target, second.symm x ∈ Φ.source → first.symm x = Φ (second.symm x)

/-- Restrict a smooth coordinate chart to a smaller open target. -/
theorem restrict_smooth_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    (e : OpenPartialHomeomorph M (X n))
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {V : Set (X n)} (hV : IsOpen V) (hVsub : V ⊆ e.target) :
    let a := e.trans (OpenPartialHomeomorph.ofSet V hV)
    a.target = V ∧ a.source ⊆ e.source ∧ ContMDiffOn J K ∞ a a.source ∧
      ContMDiffOn K J ∞ a.symm a.target := by
  let a := e.trans (OpenPartialHomeomorph.ofSet V hV)
  have ht : a.target = V := inter_eq_left.mpr hVsub
  exact ⟨ht, fun _ hx => hx.1, he.mono (fun _ hx => hx.1),
    hes.mono (fun _ hx => hx.2)⟩

/-- Invertibility at the two centers gives charts on the same coordinate
ball. The limiting partner property keeps all nearby matched points in
the first chart, where their source coordinates force the match. -/
theorem exists_paired_sourceCharts
    {Φ : OpenPartialHomeomorph M₂ M₁} {f₁ : M₁ → X n} {f₂ : M₂ → X n}
    {U₁ : Set M₁} {U₂ : Set M₂} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    {q : M₁} {p : M₂}
    (hq : q ∈ (𝓡∂ n).interior M₁) (hp : p ∈ (𝓡∂ n).interior M₂) (hqU : q ∈ U₁) (hpU : p ∈ U₂)
    (hf₁ : ContMDiff J K ∞ f₁) (hf₂ : ContMDiff J K ∞ f₂)
    (hD₁ : (mfderiv J K f₁ q).IsInvertible) (hD₂ : (mfderiv J K f₂ p).IsInvertible)
    (hvalues : f₂ p = f₁ q) (hEq : EqOn f₂ (f₁ ∘ Φ) Φ.source)
    (hlim : Tendsto Φ (𝓝[Φ.source] p) (𝓝 q)) :
    Nonempty (PairedSourceCharts Φ f₁ f₂ U₁ U₂ q p) := by
  obtain ⟨a, hqa, haU, haI, haF, ha, has⟩ :=
    exists_chart_of_invertible_mfderiv hq hU₁ hqU hf₁.contMDiffOn hD₁
  obtain ⟨b, hpb, hbU, hbI, hbF, hb, hbs⟩ :=
    exists_chart_of_invertible_mfderiv hp hU₂ hpU hf₂.contMDiffOn hD₂
  have hz : b p = a q := (hbF hpb).trans (hvalues.trans (haF hqa).symm)
  have hlim' : ∀ᶠ x in 𝓝 p, x ∈ Φ.source → Φ x ∈ a.source :=
    eventually_nhdsWithin_iff.mp (hlim.eventually (a.open_source.eventually_mem hqa))
  obtain ⟨S, hSsub, hS, hpS⟩ := mem_nhds_iff.mp hlim'
  let V := (a.target ∩ b.target) ∩ b.symm ⁻¹' S
  have hV : IsOpen V :=
    (b.continuousOn_symm.mono inter_subset_right).isOpen_inter_preimage
      (a.open_target.inter b.open_target) hS
  have hzV : b p ∈ V := by
    refine ⟨⟨hz.symm ▸ a.map_source hqa, b.map_source hpb⟩, ?_⟩
    change b.symm (b p) ∈ S
    rwa [b.left_inv hpb]
  obtain ⟨r, hr, hBV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzV)
  let B := ball (b p) r
  let A := a.trans (OpenPartialHomeomorph.ofSet B isOpen_ball)
  let C := b.trans (OpenPartialHomeomorph.ofSet B isOpen_ball)
  obtain ⟨hAt, hAs, hA, hAi⟩ := restrict_smooth_chart a ha has isOpen_ball
    (show B ⊆ a.target from fun _ hx => (hBV hx).1.1)
  obtain ⟨hCt, hCs, hC, hCi⟩ := restrict_smooth_chart b hb hbs isOpen_ball
    (show B ⊆ b.target from fun _ hx => (hBV hx).1.2)
  refine ⟨⟨A, C, hAt.trans hCt.symm, ⟨hqa, ?_⟩, ⟨hpb, mem_ball_self hr⟩,
    hAs.trans haI, hCs.trans hbI, hAs.trans haU, hCs.trans hbU, hA, hC, hAi, hCi,
    haF.mono hAs, hbF.mono hCs, ?_⟩⟩
  · change a q ∈ B
    rw [← hz]
    exact mem_ball_self hr
  · intro x hx hxW
    change C.target = B at hCt
    have hxB : x ∈ B := by
      rw [← hCt]
      exact hx
    have hxV := hBV hxB
    have hbPhi : Φ (b.symm x) ∈ a.source := hSsub (show b.symm x ∈ S from hxV.2) hxW
    have hE := hEq hxW
    have hbEq : f₂ (b.symm x) = x := (hbF (b.map_target hxV.1.2)).symm.trans (b.right_inv hxV.1.2)
    have hcoord : a (Φ (b.symm x)) = x := (haF hbPhi).trans (hE.symm.trans hbEq)
    change a.symm x = Φ (b.symm x)
    exact (congrArg a.symm hcoord.symm).trans (a.left_inv hbPhi)

end CalderonPatch
