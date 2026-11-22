module

public import Proof.CalderonPatch.CapMetricExtension
public import Proof.CalderonPatch.SmoothPasting

@[expose] public section

noncomputable section
open Matrix Metric Set
open scoped ContDiff

namespace CalderonPatch

open CalderonN (I Mat lowerHalfSpace uniqueDiffOn_lowerHalfSpace)

variable {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Two one-sided metrics with matched jets on the seam admit smooth
local extensions with a common metric on the added side. The outward
coordinate is positive on the added side in this chart. -/
theorem exists_local_common_cap_metrics
    {g₁ g₂ : Z × ℝ → Mat n} {U : Set (Z × ℝ)} (hU : IsOpen U)
    (hg₁ : ∀ i j, ContDiffOn ℝ ∞ (fun p => g₁ p i j) (lowerHalfSpace Z))
    (hg₂ : ∀ i j, ContDiffOn ℝ ∞ (fun p => g₂ p i j) (lowerHalfSpace Z))
    (hSym₁ : ∀ p ∈ lowerHalfSpace Z, (g₁ p).transpose = g₁ p)
    (hSym₂ : ∀ p ∈ lowerHalfSpace Z, (g₂ p).transpose = g₂ p)
    (hSupp₁ : ∀ (i j : I n) (k : ℕ), HasCompactSupport (fun z : Z =>
      iteratedFDerivWithin ℝ k (fun p => g₁ p i j) (lowerHalfSpace Z) (z, 0) (fun _ => (0, 1))))
    (hSupp₂ : ∀ (i j : I n) (k : ℕ), HasCompactSupport (fun z : Z =>
      iteratedFDerivWithin ℝ k (fun p => g₂ p i j) (lowerHalfSpace Z) (z, 0) (fun _ => (0, 1))))
    (hJets : ∀ i j k, EqOn
      (iteratedFDerivWithin ℝ k (fun p => g₁ p i j) (lowerHalfSpace Z))
      (iteratedFDerivWithin ℝ k (fun p => g₂ p i j) (lowerHalfSpace Z))
      (U ∩ frontier (lowerHalfSpace Z)))
    {A : Set Z} (hA : IsCompact A)
    (hPos₁ : ∀ z ∈ A, Matrix.PosDef (g₁ (z, 0))) (hPos₂ : ∀ z ∈ A, Matrix.PosDef (g₂ (z, 0))) :
    ∃ G₁ G₂ : Z × ℝ → Mat n,
      (∀ i j, ContDiffOn ℝ ∞ (fun p => G₁ p i j) U) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun p => G₂ p i j) U) ∧
      EqOn G₁ g₁ (lowerHalfSpace Z) ∧ EqOn G₂ g₂ (lowerHalfSpace Z) ∧
      EqOn G₁ G₂ (lowerHalfSpace Z)ᶜ ∧
      ∃ δ > 0, ∀ z ∈ A, ∀ t ∈ ball (0 : ℝ) δ,
        Matrix.PosDef (G₁ (z, t)) ∧ Matrix.PosDef (G₂ (z, t)) := by
  classical
  let S := lowerHalfSpace Z
  obtain ⟨F₁, hF₁, hFS₁, hE₁⟩ := exists_symmetric_extension_lowerHalfSpace hg₁ hSym₁ hSupp₁
  obtain ⟨F₂, hF₂, hFS₂, hE₂⟩ := exists_symmetric_extension_lowerHalfSpace hg₂ hSym₂ hSupp₂
  let G₂ := S.piecewise F₂ F₁
  have hClosed : IsClosed S := isClosed_univ.prod isClosed_Iic
  have hS (p : Z) : (p, (0 : ℝ)) ∈ S := ⟨mem_univ _, le_rfl⟩
  have hFJets (i j : I n) (k : ℕ) :
      EqOn (iteratedFDeriv ℝ k (fun p => F₂ p i j))
        (iteratedFDeriv ℝ k (fun p => F₁ p i j)) (U ∩ frontier S) := by
    intro p hp
    have hpS : p ∈ S := by
      rw [← hClosed.closure_eq]
      exact frontier_subset_closure hp.2
    have h₁ : EqOn (fun p => F₁ p i j) (fun p => g₁ p i j) S :=
      fun x hx => congrArg (fun A : Mat n => A i j) (hE₁ hx)
    have h₂ : EqOn (fun p => F₂ p i j) (fun p => g₂ p i j) S :=
      fun x hx => congrArg (fun A : Mat n => A i j) (hE₂ hx)
    have h₁' := h₁.iteratedFDerivWithin (𝕜 := ℝ) k hpS
    have h₂' := h₂.iteratedFDerivWithin (𝕜 := ℝ) k hpS
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (n := k) (𝕜 := ℝ)
      uniqueDiffOn_lowerHalfSpace ((hF₁ i j).contDiffAt.of_le (by simp)) hpS] at h₁'
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (n := k) (𝕜 := ℝ)
      uniqueDiffOn_lowerHalfSpace ((hF₂ i j).contDiffAt.of_le (by simp)) hpS] at h₂'
    exact h₂'.trans ((hJets i j k hp).symm.trans h₁'.symm)
  have hG₂ : ∀ i j, ContDiffOn ℝ ∞ (fun p => G₂ p i j) U := by
    intro i j
    have h := contDiffOn_piecewise_of_matched_jets (S := S)
      (f := fun p => F₂ p i j) (g := fun p => F₁ p i j)
      hU (hF₂ i j).contDiffOn (hF₁ i j).contDiffOn (hFJets i j)
    exact h.congr (fun x _ => by by_cases hx : x ∈ S <;> simp [G₂, hx])
  refine ⟨F₁, G₂, fun i j => (hF₁ i j).contDiffOn, hG₂, hE₁,
    fun p hp => (piecewise_eq_of_mem S F₂ F₁ hp).trans (hE₂ hp),
    fun p hp => (piecewise_eq_of_notMem S F₂ F₁ hp).symm, ?_⟩
  obtain ⟨r₁, hr₁, hV₁⟩ := posDef_near_compact_slice hA hFS₁
    (fun i j => (hF₁ i j).continuous) (fun z hz => (hE₁ (hS z)).symm ▸ hPos₁ z hz)
  obtain ⟨r₂, hr₂, hV₂⟩ := posDef_near_compact_slice hA hFS₂
    (fun i j => (hF₂ i j).continuous) (fun z hz => (hE₂ (hS z)).symm ▸ hPos₂ z hz)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz t ht => ?_⟩
  have h₁ := hV₁ z hz t (ball_subset_ball (min_le_left _ _) ht)
  have h₂ := hV₂ z hz t (ball_subset_ball (min_le_right _ _) ht)
  exact ⟨h₁, by
    change Matrix.PosDef (S.piecewise F₂ F₁ (z, t))
    by_cases hp : (z, t) ∈ S
    · rwa [piecewise_eq_of_mem _ _ _ hp]
    · rwa [piecewise_eq_of_notMem _ _ _ hp]⟩

end CalderonPatch
