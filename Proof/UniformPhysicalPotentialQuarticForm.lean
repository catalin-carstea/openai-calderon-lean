import Proof.UniformPhysicalPotentialQuarticData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Enlarge the budgets while retaining every SAME actual adjoint and
mixed commutator witness. -/
def PhysicalPotentialQuarticData.enlarge {Y : Set X} {d : Data} {CF CT : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} {y : X} {CA CK CA' CK' : ℝ}
    (W : PhysicalPotentialQuarticData P y CA CK) (hr : 0 ≤ d.radius y)
    (hCA : CA ≤ CA') (hCK : CK ≤ CK') : PhysicalPotentialQuarticData P y CA' CK' := {
  adjointHigh := W.adjointHigh
  commLow := W.commLow
  commHigh := W.commHigh
  adjoint_compatible := W.adjoint_compatible
  commutator_compatible := W.commutator_compatible
  commutator_balanced := W.commutator_balanced
  adjoint_bound := fun a => (W.adjoint_bound a).trans
    (mul_le_mul_of_nonneg_right hCA (potentialGeneratorWeight_nonneg hr a))
  commLow_bound := fun a b => (W.commLow_bound a b).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK (potentialGeneratorWeight_nonneg hr a))
      (potentialGeneratorWeight_nonneg hr b))
  commHigh_bound := fun a b => (W.commHigh_bound a b).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK (potentialGeneratorWeight_nonneg hr a))
      (potentialGeneratorWeight_nonneg hr b)) }

lemma PhysicalPrincipalData.potentialQuarticWeakValue_enlarge {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} {CA CK CA' CK' : ℝ}
    (W : PhysicalPotentialQuarticData P y CA CK) (hr : 0 ≤ d.radius y) (hCA : CA ≤ CA') (hCK : CK ≤ CK')
    (u : SphereSobolev (3/2:ℝ)) :
    P.potentialQuarticWeakValue (W.enlarge hr hCA hCK) u=P.potentialQuarticWeakValue W u := rfl

/-- Closed actual full-matrix quartic weak bound, with all constants before
profiles and frames and every coefficient cross term retained. The physical
norm-square identification and complementary potential remainder are separate
outstanding inferences. -/
theorem uniform_physical_potential_quartic_weak_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CG CK CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CG ∧ 0 ≤ CK ∧ 0 ≤ CE ∧
      physicalPotentialGeneratorBudget CF ≤ CG ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,∀ y ∈ Y,
      ∃ W : PhysicalPotentialQuarticData P y CG CK,∀ u : SphereSobolev (3/2:ℝ),
      |P.potentialQuarticWeakValue W u| ≤ CE*ε*beta d.γ d.radius y*‖u‖^2 := by
  have hData := uniform_physical_potential_quartic_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CA,CK,hη,hη1,hCA,hCK,hProduce⟩ := hData
  let CG := max CA (physicalPotentialGeneratorBudget CF)
  let CE := 4*CG^2*CK*(49*potentialWordEntryBudget K)^2
  have hCG : 0 ≤ CG := hCA.trans (le_max_left _ _)
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  have hBudget : physicalPotentialGeneratorBudget CF ≤ CG := le_max_right _ _
  refine ⟨η,CG,CK,CE,hη,hη1,hCG,hCK,hCE,hBudget,?_⟩
  intro floor hf ε hε hSmall d hd CT P y hy
  obtain ⟨W⟩ := hProduce floor hf ε hε hSmall d hd CF CT P y hy
  let W' : PhysicalPotentialQuarticData P y CG CK := W.enlarge (hd.2.2.2.2.1.2 y hy).1.le (le_max_left _ _) le_rfl
  refine ⟨W',?_⟩
  intro u
  exact P.abs_potentialQuarticWeakValue_small hd hK hf hε (hSmall.trans hη1) hy hCG hCK hBudget W' u
end ShrinkingSpheres
