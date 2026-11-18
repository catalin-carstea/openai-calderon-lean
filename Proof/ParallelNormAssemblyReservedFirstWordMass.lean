import Proof.ParallelNormAssemblyReservedFirstWords
import Proof.PrincipalFirstErrorCoordinateSharpWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

/-- Complete coordinate angular-word coefficient mass of the SAME
first-base coefficient, at the original epsilon/beta scale. The bounded
geometric remainder is estimated separately at order zero. -/
theorem effective_first_normalized_word_mass_bound {Y Ω : Set X} {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε CF CT : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hK : 1 ≤ K) (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (b : I) :
    let BD := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
    let BE := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
    ∑ a : PhysicalPotentialGeneratorIndex,|effectiveFirstWordCoefficient d b y a| ≤
      (BD+6+3*BE)*ε/beta d.γ d.radius y := by
  dsimp only
  let BD := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
  let BE := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let β := beta d.γ d.radius y
  have hβ1 : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ : 0 < β := zero_lt_one.trans_le hβ1
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hr1 : d.radius y ≤ 1 :=
    ((radius_bounds (d.radius y) β floor ε hr.le hf (hd.2.2.2.2.1.2 y hy).2.1
      (hd.2.2.2.2.2 y hy).2).2.2).trans hε1
  have hBE : 0 ≤ BE := principalFirstErrorCoordinateTwoJetBudget_nonneg _ _ _ _
    (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
  have hDE : |principalModelDegreeCoordinateWeight d b y| ≤ BD*ε/β :=
    (hd.principalModelDegreeCoordinateWeight_bounds hY (by omega) hK hf hε hε1 hy b 0).1
  have hR (a : I) : |principalModelRaisingCoordinateWeight d a b y| ≤ 2*ε/β :=
    (hd.principalModelRaisingCoordinateWeight_bounds hY hK hf hε hε1 hy a b 0).1
  have hE (a : I) : |d.radius y*principalFirstErrorCoordinateWeight d a b y| ≤ BE*ε/β := by
    rw [abs_mul,abs_of_pos hr]
    have hh := (hd.principalFirstErrorCoordinateWeight_small_two_jet_bounds hY hm hK hf hε hε1 hy a b 0 0).1
    calc
      _ ≤ 1*(BE*ε/β^2) := mul_le_mul hr1 hh (abs_nonneg _) zero_le_one
      _ = (BE*ε/β)/β := by field_simp <;> ring
      _ ≤ BE*ε/β := div_le_self (by positivity) hβ1
  simp only [effectiveFirstWordCoefficient,Fintype.sum_sum_type,Fintype.sum_unique]
  calc
    _ ≤ BD*ε/β+((∑ _a : I,2*ε/β)+(∑ _a : I,BE*ε/β)) :=
      add_le_add hDE (add_le_add (Finset.sum_le_sum (fun a _ => hR a)) (Finset.sum_le_sum (fun a _ => hE a)))
    _ = _ := by simp only [Fin.sum_univ_three];ring

end ShrinkingSpheres.ParallelEnergy
