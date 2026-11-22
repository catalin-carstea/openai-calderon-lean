module

public import Proof.CalderonN.Chart

import Proof.CalderonN.GreenWeak

@[expose] public section

/-! Product continuation seed, ported from GreenCross in the checked 3D Theorem 3.1 release. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {n : ℕ}

/-- A smooth kernel satisfying the first equation in the first variable
and the second equation in the second variable. -/
def ProductSolutionOn (g₁ g₂ : (MetricField n)) (U : Set ((X n) × (X n))) (F : (X n) × (X n) → ℝ) : Prop :=
  ContDiffOn ℝ ∞ F U ∧
    (∀ q ∈ U, laplace g₁ (fun x => F (x, q.2)) q.1 = 0) ∧
    ∀ q ∈ U, laplace g₂ (fun y => F (q.1, y)) q.2 = 0

theorem ProductSolutionOn.mono {g₁ g₂ : (MetricField n)} {U V : Set ((X n) × (X n))} {F : (X n) × (X n) → ℝ}
    (h : ProductSolutionOn g₁ g₂ U F) (hsub : V ⊆ U) : ProductSolutionOn g₁ g₂ V F :=
  ⟨h.1.mono hsub, fun q hq => h.2.1 q (hsub hq), fun q hq => h.2.2 q (hsub hq)⟩

theorem ProductSolutionOn.congr {g₁ g₂ : (MetricField n)} {U : Set ((X n) × (X n))} {F H : (X n) × (X n) → ℝ}
    (h : ProductSolutionOn g₁ g₂ U F) (hU : IsOpen U) (heq : EqOn H F U) :
    ProductSolutionOn g₁ g₂ U H := by
  refine ⟨h.1.congr heq, ?_, ?_⟩
  · intro q hq
    let Uq := {x | (x, q.2) ∈ U}
    have hUq : IsOpen Uq := hU.preimage (continuous_id.prodMk continuous_const)
    exact (laplace_congrOn hUq (fun _ _ => rfl) (fun x hx => heq hx) hq).trans (h.2.1 q hq)
  · intro q hq
    let Uq := {y | (q.1, y) ∈ U}
    have hUq : IsOpen Uq := hU.preimage (continuous_const.prodMk continuous_id)
    exact (laplace_congrOn hUq (fun _ _ => rfl) (fun y hy => heq hy) hq).trans (h.2.2 q hq)

theorem ProductSolutionOn.swap {g₁ g₂ : (MetricField n)} {U : Set ((X n) × (X n))} {F : (X n) × (X n) → ℝ}
    (h : ProductSolutionOn g₁ g₂ U F) :
    ProductSolutionOn g₂ g₁ (Prod.swap ⁻¹' U) (F ∘ Prod.swap) := by
  refine ⟨h.1.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hz => hz),?_,?_⟩
  · exact fun q hq => h.2.2 (Prod.swap q) hq
  · exact fun q hq => h.2.1 (Prod.swap q) hq

/-- The initial cross is off the diagonal and has at least one point in
the known side. Both factors lie in the original chart. -/
def knownCross (Ω W : Set (X n)) : Set ((X n) × (X n)) :=
  OffDiagonal Ω ∩ {q | q.2 ∈ W ∨ q.1 ∈ W}

def initialGreenKernel (W : Set (X n)) (G₁ G₂ : (X n) × (X n) → ℝ) (q : (X n) × (X n)) : ℝ := by
  classical
  exact if q.2 ∈ W then G₁ q else G₂ q

theorem isOpen_knownCross {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) :
    IsOpen (knownCross Ω W) :=
  (isOpen_offDiagonal hΩ).inter
    ((hW.preimage continuous_snd).union (hW.preimage continuous_fst))

theorem initialGreenKernel_eq_left {W : Set (X n)} (G₁ G₂ : (X n) × (X n) → ℝ)
    {q : (X n) × (X n)} (hy : q.2 ∈ W) : initialGreenKernel W G₁ G₂ q = G₁ q := by
  simp [initialGreenKernel, hy]

theorem initialGreenKernel_eq_right {W : Set (X n)} {G₁ G₂ : (X n) × (X n) → ℝ}
    (he : EqOn G₁ G₂ (OffDiagonal W)) {q : (X n) × (X n)} (hx : q.1 ∈ W) (hne : q.1 ≠ q.2) :
    initialGreenKernel W G₁ G₂ q = G₂ q := by
  by_cases hy : q.2 ∈ W
  · rw [initialGreenKernel_eq_left G₁ G₂ hy]
    exact he ⟨hx, hy, hne⟩
  · simp [initialGreenKernel, hy]

/-- The normalized Green-germ hypothesis supplies the compatible seed
for product continuation, in both variables and with the prescribed
restrictions on the original overlap. -/
theorem initialGreenKernel_productSolution [NeZero n]
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) {g₁ g₂ : (MetricField n)}
    (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W)) :
    ProductSolutionOn g₁ g₂ (knownCross Ω W) (initialGreenKernel W G₁ G₂) := by
  let U₁ := OffDiagonal Ω ∩ Prod.snd ⁻¹' W
  let U₂ := OffDiagonal Ω ∩ Prod.fst ⁻¹' W
  have hU₁ : IsOpen U₁ := (isOpen_offDiagonal hΩ).inter (hW.preimage continuous_snd)
  have hU₂ : IsOpen U₂ := (isOpen_offDiagonal hΩ).inter (hW.preimage continuous_fst)
  have h₁ : ProductSolutionOn g₁ g₂ U₁ G₁ := by
    refine ⟨hG₁.1.mono inter_subset_left, ?_, ?_⟩
    · intro q hq
      exact (hG₁.harmonic_left hΩ hg₁ hq.1.2.1).2 q.1 ⟨hq.1.1, hq.1.2.2⟩
    · intro q hq
      have he := laplace_congrOn hW hmetric (f := fun y => G₁ (q.1, y)) (fun _ _ => rfl) hq.2
      exact he.symm.trans
        ((hG₁.harmonic_right hΩ hg₁ hq.1.1).2 q.2 ⟨hq.1.2.1, Ne.symm hq.1.2.2⟩)
  have h₂ : ProductSolutionOn g₁ g₂ U₂ G₂ := by
    refine ⟨hG₂.1.mono inter_subset_left, ?_, ?_⟩
    · intro q hq
      have he := laplace_congrOn hW hmetric (f := fun x => G₂ (x, q.2)) (fun _ _ => rfl) hq.2
      exact he.trans
        ((hG₂.harmonic_left hΩ hg₂ hq.1.2.1).2 q.1 ⟨hq.1.1, hq.1.2.2⟩)
    · intro q hq
      exact (hG₂.harmonic_right hΩ hg₂ hq.1.1).2 q.2 ⟨hq.1.2.1, Ne.symm hq.1.2.2⟩
  have hF₁ := h₁.congr hU₁ (fun _ hp => initialGreenKernel_eq_left G₁ G₂ hp.2)
  have hF₂ := h₂.congr hU₂ (fun _ hp => initialGreenKernel_eq_right hgreen hp.2 hp.1.2.2)
  have hf (q : (X n) × (X n)) (hq : q ∈ knownCross Ω W) : q ∈ U₁ ∨ q ∈ U₂ :=
    hq.2.imp (fun h => ⟨hq.1, h⟩) (fun h => ⟨hq.1, h⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases hf q hq with hq₁ | hq₂
    · exact (hF₁.1.contDiffAt (hU₁.mem_nhds hq₁)).contDiffWithinAt
    · exact (hF₂.1.contDiffAt (hU₂.mem_nhds hq₂)).contDiffWithinAt
  · intro q hq
    exact (hf q hq).elim (hF₁.2.1 q) (hF₂.2.1 q)
  · intro q hq
    exact (hf q hq).elim (hF₁.2.2 q) (hF₂.2.2 q)

end CalderonN
