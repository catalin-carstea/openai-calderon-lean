import Proof.PotentialCoreHalfMassPairing
import Proof.ModelDefectFiveHalfSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalPrincipalData.potentialModelDefectRealForm
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  ⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG y),
    P.potentialQuadraticCoreL W (ambientModelDefectFiveHalfSection d G hG y)⟫_ℝ

def potentialModelDefectBudget (K CF CG : ℝ) : ℝ :=
  CG^2*(49*potentialWordEntryBudget K)*(∑ i : I,‖flatLoweringSobolevL (3/2:ℝ) i‖)

lemma potentialModelDefectBudget_nonneg (K CF CG : ℝ) (hK : 1 ≤ K) :
    0 ≤ potentialModelDefectBudget K CF CG := by
  have hWord : 0 ≤ potentialWordEntryBudget K := by dsimp only [potentialWordEntryBudget];positivity
  exact mul_nonneg (mul_nonneg (sq_nonneg CG) (mul_nonneg (by norm_num) hWord))
    (Finset.sum_nonneg (fun i _ => norm_nonneg _))

theorem PhysicalPrincipalData.potential_model_defect_form_bound
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hK : 1 ≤ K) (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {y : X} (hy : y ∈ Y) {CG CK : ℝ} (hCG : 0 ≤ CG)
    (hBudget : physicalPotentialGeneratorBudget CF ≤ CG)
    (W : PhysicalPotentialQuarticData P y CG CK) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) :
    |P.potentialModelDefectRealForm W G hG| ≤
      potentialModelDefectBudget K CF CG*ε*beta d.γ d.radius y*
        ‖ambientSobolevSection (3/2:ℝ) (by norm_num) G hG y‖^2 := by
  let U := ambientSobolevSection (3/2:ℝ) (by norm_num) G hG y
  let V := ambientModelDefectFiveHalfSection d G hG y
  let CZ := ∑ i : I,‖flatLoweringSobolevL (3/2:ℝ) i‖
  let β := beta d.γ d.radius y
  let mass := potentialWordMass d y
  have hr := (hd.2.2.2.2.1.2 y hy).1.le
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hM : 0 ≤ mass := potentialWordMass_nonneg d y hr
  have hCZ : 0 ≤ CZ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  have hZ := norm_ambientModelDefectFiveHalfSection_half_le d G hG y hFrame
  have hMass := hd.potentialWordMass_le hK hf hε hε1 hy
  calc
    _ ≤ CG^2*mass*‖U‖*‖sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) V‖ :=
      P.abs_potentialQuadraticCoreL_half_mass_le hy hr hCG hBudget W U V
    _ ≤ CG^2*mass*‖U‖*(CZ*β*‖U‖) :=
      mul_le_mul_of_nonneg_left hZ (mul_nonneg (mul_nonneg (sq_nonneg CG) hM) (norm_nonneg _))
    _ = (CG^2*CZ*β*‖U‖^2)*mass := by ring
    _ ≤ (CG^2*CZ*β*‖U‖^2)*((49*potentialWordEntryBudget K)*ε) :=
      mul_le_mul_of_nonneg_left hMass (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg CG) hCZ) hβ) (sq_nonneg _))
    _ = _ := by dsimp only [potentialModelDefectBudget,U,CZ,β];ring

end ShrinkingSpheres
