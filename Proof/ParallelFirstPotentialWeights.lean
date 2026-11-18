import Proof.ParallelNormAssemblyReservedFirstWordMass
import Proof.AdmissibleRadiusSmallJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

/-- One scalar budget for each actual normalized complete first word,
including its native radius factor. -/
def firstPotentialWordBudget (K M1 M2 C2 : ℝ) : ℝ :=
  principalModelDegreeCoordinateBudget K M1 C2+2+
    principalFirstErrorCoordinateTwoJetBudget K |M1| |M2| C2+
    (K+1)*principalFirstErrorCoordinateTwoJetBudget K |M1| |M2| C2

lemma firstPotentialWordBudget_nonneg (K M1 M2 C2 : ℝ) (hK : 0 ≤ K) :
    0 ≤ firstPotentialWordBudget K M1 M2 C2 := by
  have hD := principalModelDegreeCoordinateBudget_nonneg K M1 C2 hK
  have hE := principalFirstErrorCoordinateTwoJetBudget_nonneg K |M1| |M2| C2 hK (abs_nonneg _) (abs_nonneg _)
  unfold firstPotentialWordBudget
  positivity

lemma firstPotential_word_smooth {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (b : I) (a : PhysicalPotentialGeneratorIndex) :
    ContDiffOn ℝ ∞ (fun y => effectiveFirstWordCoefficient d b y a) Y := by
  rcases a with u | (a | a)
  · exact hd.contDiffOn_principalModelDegreeCoordinateWeight hY hK b
  · exact hd.contDiffOn_principalModelRaisingCoordinateWeight hK a b
  · exact hd.2.2.2.2.1.1.mul (hd.contDiffOn_principalFirstErrorCoordinateWeight hK a b)

/-- Original sharp first-word weights; no frame derivative occurs. -/
theorem firstPotential_word_bounds {Y Ω : Set X} {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hK : 1 ≤ K) (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {y : X} (hy : y ∈ Y) (b i : I) (a : PhysicalPotentialGeneratorIndex) :
    let C := firstPotentialWordBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
    |effectiveFirstWordCoefficient d b y a| ≤ C*ε/beta d.γ d.radius y ∧
      |fderiv ℝ (fun x => effectiveFirstWordCoefficient d b x a) y (axis i)| ≤ C*ε := by
  let BD := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
  let BE := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let C := firstPotentialWordBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  let β := beta d.γ d.radius y
  have hD : 0 ≤ BD := principalModelDegreeCoordinateBudget_nonneg _ _ _ (zero_le_one.trans hK)
  have hE : 0 ≤ BE := principalFirstErrorCoordinateTwoJetBudget_nonneg _ _ _ _ (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
  have hKC : 0 ≤ (K+1)*BE := by positivity
  have hDC : BD ≤ C := by change BD ≤ BD+2+BE+(K+1)*BE;linarith
  have h2C : 2 ≤ C := by change 2 ≤ BD+2+BE+(K+1)*BE;linarith
  have hEC : BE ≤ C := by change BE ≤ BD+2+BE+(K+1)*BE;linarith
  have hE1C : (K+1)*BE ≤ C := by change (K+1)*BE ≤ BD+2+BE+(K+1)*BE;linarith
  have hβ1 : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ : 0 < β := zero_lt_one.trans_le hβ1
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hr1 : d.radius y ≤ 1 :=
    ((radius_bounds (d.radius y) β floor ε hr.le hf (hd.2.2.2.2.1.2 y hy).2.1
      (hd.2.2.2.2.2 y hy).2).2.2).trans hε1
  have hGrow (A : ℝ) (hAC : A ≤ C) : A*ε/β ≤ C*ε/β ∧ A*ε ≤ C*ε :=
    ⟨div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hε) hβ.le,
      mul_le_mul_of_nonneg_right hAC hε⟩
  rcases a with u | (a | a)
  · have hh := hd.principalModelDegreeCoordinateWeight_bounds hY (by omega) hK hf hε hε1 hy b i
    exact ⟨hh.1.trans (hGrow BD hDC).1,hh.2.trans (hGrow BD hDC).2⟩
  · have hh := hd.principalModelRaisingCoordinateWeight_bounds hY hK hf hε hε1 hy a b i
    exact ⟨hh.1.trans (hGrow 2 h2C).1,hh.2.trans (hGrow 2 h2C).2⟩
  · have hRaw := hd.principalFirstErrorCoordinateWeight_small_two_jet_bounds hY hm hK hf hε hε1 hy a b i i
    have hEN : |principalFirstErrorCoordinateWeight d a b y| ≤ BE*ε :=
      hRaw.1.trans (div_le_self (mul_nonneg hE hε) (by nlinarith only [hβ1] : 1 ≤ β^2))
    have hED : |fderiv ℝ (principalFirstErrorCoordinateWeight d a b) y (axis i)| ≤ BE*ε :=
      hRaw.2.1.trans (div_le_self (mul_nonneg hE hε) hβ1)
    have hRD : |fderiv ℝ d.radius y (axis i)| ≤ K*ε :=
      (hd.coordinate_radius_two_small_jet_bounds hY (by omega) hK hf hy i i).1.trans
        (div_le_self (by positivity) hβ1)
    constructor
    · change |d.radius y*principalFirstErrorCoordinateWeight d a b y| ≤ _
      rw [abs_mul,abs_of_pos hr]
      calc
        _ ≤ 1*(BE*ε/β^2) := mul_le_mul hr1 hRaw.1 (abs_nonneg _) zero_le_one
        _ = (BE*ε/β)/β := by field_simp <;> ring
        _ ≤ BE*ε/β := div_le_self (by positivity) hβ1
        _ ≤ C*ε/β := (hGrow BE hEC).1
    · change |fderiv ℝ (fun x => d.radius x*principalFirstErrorCoordinateWeight d a b x) y (axis i)| ≤ _
      have hDR := (hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
      have hDE := ((hd.contDiffOn_principalFirstErrorCoordinateWeight (zero_lt_one.trans_le hK) a b).contDiffAt
        (hY.mem_nhds hy)).differentiableAt (by simp)
      change |fderiv ℝ (d.radius * principalFirstErrorCoordinateWeight d a b) y (axis i)| ≤ _
      rw [fderiv_mul hDR hDE]
      simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
      rw [add_comm (d.radius y*fderiv ℝ (principalFirstErrorCoordinateWeight d a b) y (axis i))]
      calc
        _ ≤ |principalFirstErrorCoordinateWeight d a b y| *|fderiv ℝ d.radius y (axis i)|+
            |d.radius y| *|fderiv ℝ (principalFirstErrorCoordinateWeight d a b) y (axis i)| :=
          (abs_add_le _ _).trans (add_le_add (abs_mul _ _).le (abs_mul _ _).le)
        _ ≤ (BE*ε)*(K*ε)+1*(BE*ε) := add_le_add
          (mul_le_mul hEN hRD (abs_nonneg _) (by positivity))
          (mul_le_mul (by simpa only [abs_of_pos hr] using hr1) hED (abs_nonneg _) zero_le_one)
        _ = (K*BE*ε)*ε+BE*ε := by ring
        _ ≤ (K*BE*ε)*1+BE*ε := add_le_add (mul_le_mul_of_nonneg_left hε1 (show 0 ≤ K*BE*ε by positivity)) le_rfl
        _ = ((K+1)*BE)*ε := by ring
        _ ≤ C*ε := (hGrow _ hE1C).2

end ShrinkingSpheres.ParallelEnergy
