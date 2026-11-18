import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unique actual realizations glue without imposing derivative bounds on
    the auxiliary choices used to obtain their smooth local representatives. -/
lemma exists_contDiffOn_unique_local_realization {Y : Set P} (hY : IsOpen Y)
    (R : P → E → Prop)
    (hUnique : ∀ x ∈ Y,∀ u v,R x u → R x v → u=v)
    (hLocal : ∀ y ∈ Y,∃ F : P → E,ContDiffAt ℝ ∞ F y ∧ ∀ᶠ x in 𝓝 y,R x (F x)) :
    ∃ F : P → E,ContDiffOn ℝ ∞ F Y ∧ ∀ x ∈ Y,R x (F x) := by
  classical
  have hPoint (x : P) (hx : x ∈ Y) : ∃ u,R x u := by
    obtain ⟨F,hF,hR⟩ := hLocal x hx
    exact ⟨F x,hR.self_of_nhds⟩
  let F : P → E := fun x => if hx : x ∈ Y then Classical.choose (hPoint x hx) else 0
  have hF (x : P) (hx : x ∈ Y) : R x (F x) := by
    dsimp only [F]
    rw [dite_eq_left hx]
    exact Classical.choose_spec (hPoint x hx)
  refine ⟨F,?_,hF⟩
  intro y hy
  obtain ⟨G,hG,hRG⟩ := hLocal y hy
  have hEq : F =ᶠ[𝓝 y] G := by
    filter_upwards [hY.mem_nhds hy,hRG] with x hx hRx
    exact hUnique x hx (F x) (G x) (hF x hx) hRx
  exact (hG.congr_of_eventuallyEq hEq).contDiffWithinAt
end ShrinkingSpheres
