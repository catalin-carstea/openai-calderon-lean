import Proof.FirstScalarWeakEnergyFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- A constant center coefficient, first model and true residual have one
    genuine smooth common-support affine family on the whole parameter space. -/
theorem exists_affine_commonSupport_matrix_family
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a1 aR : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1) (haR : ContDiff ℝ ∞ aR)
    (S1 SR : Set X) (hS1 : IsCompact S1) (hSR : IsCompact SR)
    (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0) (hzR : ∀ p z,z ∉ SR → aR (p,z) = 0)
    (c r : ℝ) :
    ∃ a : P × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
      ∃ hz : ∀ p z,z ∉ S → a (p,z) = 0,
      ∀ p z,z ∈ Metric.closedBall (0:X) 2 → a (p,z) = c • (1:Mat)+r • a1 (p,z)+aR (p,z) := by
  have hFlatTheorem := exists_compact_flat_matrix_field
  obtain ⟨A0,hA0,hA0Support,hA0Flat⟩ := hFlatTheorem
  let a : P × X → Mat := fun v => c • A0 v.2+r • a1 v+aR v
  have ha : ContDiff ℝ ∞ a :=
    (((hA0.comp contDiff_snd).const_smul c).add (ha1.const_smul r)).add haR
  let S := tsupport A0 ∪ S1 ∪ SR
  have hS : IsCompact S := (hA0Support.union hS1).union hSR
  have hz (p : P) (z : X) (hzS : z ∉ S) : a (p,z) = 0 := by
    have hn0 : z ∉ tsupport A0 := fun h => hzS (Or.inl (Or.inl h))
    have hn1 : z ∉ S1 := fun h => hzS (Or.inl (Or.inr h))
    have hnR : z ∉ SR := fun h => hzS (Or.inr h)
    have h0 : A0 z = 0 := by
      by_contra hn
      exact hn0 (subset_closure hn)
    simp only [a,h0,hz1 p z hn1,hzR p z hnR,smul_zero,zero_add]
  refine ⟨a,ha,S,hS,hz,?_⟩
  intro p z hzB
  change c • A0 z+r • a1 (p,z)+aR (p,z) = _
  rw [hA0Flat z hzB]

end ShrinkingSpheres
