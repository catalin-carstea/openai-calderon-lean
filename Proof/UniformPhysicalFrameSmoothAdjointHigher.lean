import Proof.HalfDegreeAdjointHigherLift
import Proof.UniformPhysicalFrameDegreeData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A genuine globally smooth higher adjoint for each SAME physical first
error. The graph and the radius bound are produced before every test. -/
theorem uniform_physical_frame_first_error_smooth_adjoint_higher {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CA : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CA ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ∀ i : I,ContDiffOn ℝ ∞ (H i) Y ∧ ∀ x ∈ Y,
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H i x)=
          (P.first.low i x).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖H i x‖ ≤ CA*d.radius x := by
  obtain ⟨η,CD,hη,hη1,hCD,hData⟩ :=
    uniform_physical_frame_first_error_degree_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,|CF|+CD,hη,hη1,add_nonneg (abs_nonneg _) hCD,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨S,hS⟩ := hData floor hf ε hε hSmall d hd CF CT P
  refine ⟨fun i x => halfDegreeAdjointHigherLift (P.first.low i x) (S i x),?_⟩
  intro i
  refine ⟨contDiffOn_halfDegreeAdjointHigherLift _ _ (P.first.low_smooth i) (hS i).1,?_⟩
  intro x hx
  refine ⟨halfDegreeAdjointHigherLift_inclusion _ _ ((hS i).2 x hx).2,?_⟩
  have hr : 0 ≤ d.radius x := (hd.2.2.2.2.1.2 x hx).1.le
  calc
    _ ≤ ‖P.first.low i x‖+‖S i x‖ := norm_halfDegreeAdjointHigherLift_le _ _
    _ ≤ CF*d.radius x+CD*d.radius x := add_le_add (P.first.low_bound i x hx) ((hS i).2 x hx).1
    _ ≤ |CF| * d.radius x+CD*d.radius x := add_le_add (mul_le_mul_of_nonneg_right (le_abs_self CF) hr) le_rfl
    _ = _ := by ring
end ShrinkingSpheres
