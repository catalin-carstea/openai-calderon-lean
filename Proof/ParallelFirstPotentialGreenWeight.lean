import Proof.ParallelFirstPotentialWeights
import Proof.HalfCovariantEnergyControl
import Proof.ParallelFirstSelfDefectHigherBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

def firstPotentialGreenWeight (d : Data) (b : I) (a : PhysicalPotentialGeneratorIndex) (y : X) : ℝ :=
  2*metricDensity d.γ y*effectiveFirstWordCoefficient d b y a

lemma firstPotential_green_weight_smooth {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (b : I) (a : PhysicalPotentialGeneratorIndex) :
    ContDiffOn ℝ ∞ (firstPotentialGreenWeight d b a) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  exact (contDiffOn_const.mul (hg.contDiffOn_density hK)).mul (firstPotential_word_smooth hY hd hK b a)

/-- The actual density-weighted scalar coefficient satisfies uniform
Green budgets using only the original profile and reference-metric jets. -/
theorem firstPotential_green_weight_bounds {Y Ω : Set X} {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hK : 1 ≤ K) (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {y : X} (hy : y ∈ Y) (b i : I) (a : PhysicalPotentialGeneratorIndex) :
    let C := firstPotentialWordBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
    let Q := 27*K*|M ⟨1,by omega⟩|
    |firstPotentialGreenWeight d b a y| ≤ (2*C)*metricDensity d.γ y ∧
      |fderiv ℝ (firstPotentialGreenWeight d b a) y (axis i)| ≤ (2*C*(Q+1))*metricDensity d.γ y := by
  let C := firstPotentialWordBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  let Q := 27*K*|M ⟨1,by omega⟩|
  have hC : 0 ≤ C := firstPotentialWordBudget_nonneg _ _ _ _ (zero_le_one.trans hK)
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  have hW := firstPotential_word_bounds hm hY hd hK hf hε hε1 hy b i a
  have hβ1 : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hWV : |effectiveFirstWordCoefficient d b y a| ≤ C :=
    hW.1.trans ((div_le_self (mul_nonneg hC hε) hβ1).trans ((mul_le_mul_of_nonneg_left hε1 hC).trans_eq (mul_one C)))
  have hWD : |fderiv ℝ (fun x => effectiveFirstWordCoefficient d b x a) y (axis i)| ≤ C :=
    hW.2.trans ((mul_le_mul_of_nonneg_left hε1 hC).trans_eq (mul_one C))
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hDμ : |fderiv ℝ (metricDensity d.γ) y (axis i)| ≤ Q*metricDensity d.γ y :=
    hd.relative_density_axis_bound hΩ (by omega) (zero_lt_one.trans_le hK) hy i
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun j k => (hd.1.1.1 j k).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hμD := ((hg.contDiffOn_density (zero_lt_one.trans_le hK)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hwD := ((firstPotential_word_smooth hY hd (zero_lt_one.trans_le hK) b a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  constructor
  · unfold firstPotentialGreenWeight
    rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hμ)]
    exact (mul_le_mul_of_nonneg_left hWV (mul_nonneg (by norm_num) hμ)).trans_eq (by ring)
  · have hEq : firstPotentialGreenWeight d b a=
        (fun x => (2:ℝ)) * (metricDensity d.γ * fun x => effectiveFirstWordCoefficient d b x a) := by
      funext x
      change 2*metricDensity d.γ x*effectiveFirstWordCoefficient d b x a = 2*(metricDensity d.γ x*effectiveFirstWordCoefficient d b x a)
      ring
    rw [hEq,fderiv_mul (differentiableAt_const (2:ℝ)) (hμD.mul hwD),fderiv_const_apply]
    simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.zero_apply,smul_eq_mul,mul_zero,add_zero]
    rw [fderiv_mul hμD hwD]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ 2*(|metricDensity d.γ y| *|fderiv ℝ (fun x => effectiveFirstWordCoefficient d b x a) y (axis i)|+
          |effectiveFirstWordCoefficient d b y a| *|fderiv ℝ (metricDensity d.γ) y (axis i)|) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (abs_mul _ _).le (abs_mul _ _).le)) (by norm_num)
      _ ≤ 2*(metricDensity d.γ y*C+C*(Q*metricDensity d.γ y)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add ((by simpa only [abs_of_nonneg hμ] using mul_le_mul_of_nonneg_left hWD (abs_nonneg (metricDensity d.γ y))))
          (mul_le_mul hWV hDμ (abs_nonneg _) hC)
      _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
