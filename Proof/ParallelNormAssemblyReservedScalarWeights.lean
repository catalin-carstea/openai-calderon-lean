import Proof.PrincipalDensityProductJets
import Proof.PhysicalScalarCoreDomain

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

def scalarPotentialWeight (d : Data) (a b : I) (y : X) : ℝ :=
  metricDensity d.γ y*scalarPrincipalMatrix d.γ d.g₂ d.radius y a b

lemma scalar_potential_weight_smooth {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (a b : I) :
    ContDiffOn ℝ ∞ (scalarPotentialWeight d a b) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  exact (hg.contDiffOn_density hK).mul (hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK a b)

lemma scalar_potential_weight_symmetric {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (a b : I) : scalarPotentialWeight d a b y=scalarPotentialWeight d b a y := by
  have hSym : (scalarPrincipalMatrix d.γ d.g₂ d.radius y).IsHermitian :=
    (hd.principal_properties hK (hSub hy)).1.isHermitian.smul (by simp [isSelfAdjoint_iff])
  have hh := congrFun (congrFun hSym a) b
  simp only [Matrix.conjTranspose_apply,star_trivial] at hh
  exact congrArg (fun z : ℝ => metricDensity d.γ y*z) hh.symm

/-- Sharp SAME scalar density weights and their coordinate first jets. -/
theorem uniform_scalar_potential_weight_bounds {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q0 Q1 : ℝ,0 ≤ Q0 ∧ 0 ≤ Q1 ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a b : I,
      |scalarPotentialWeight d a b y| ≤ Q0*ε/(beta d.γ d.radius y)^2*metricDensity d.γ y ∧
      ∀ i : I,|fderiv ℝ (scalarPotentialWeight d a b) y (axis i)| ≤
        Q1*ε/beta d.γ d.radius y*metricDensity d.γ y := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  refine ⟨|principalZeroBudget K|,|principalDensityProductFirstBudget K M1|,abs_nonneg _,abs_nonneg _,?_⟩
  intro floor hf ε hε hε1 d hd y hy a b
  have hKp := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hFrame := fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hD (u v : I) : ‖fderiv ℝ (fun x => d.γ x u v) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) (hSub hy) u v).trans (le_abs_self _)
  have hD2 (u v : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x u v)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound hm (hSub hy) u v).trans (le_abs_self _)
  have hβ : 0 < beta d.γ d.radius y := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hA : |scalarPrincipalMatrix d.γ d.g₂ d.radius y a b| ≤
      principalZeroBudget K*ε/(beta d.γ d.radius y)^2 := by
    simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul,principalZeroBudget] using
      (principal_radius_zero_first_weights hY hg hg2 hK d.frame hFrame hd.2.2.2.2.1 hf
        hε hε1 hd.2.2.2.2.2 hy M1 (abs_nonneg _) hD a b 0).1
  refine ⟨?_,?_⟩
  · calc
      _ = metricDensity d.γ y*|scalarPrincipalMatrix d.γ d.g₂ d.radius y a b| := by
        rw [scalarPotentialWeight,abs_mul,abs_of_nonneg (show 0 ≤ metricDensity d.γ y from Real.sqrt_nonneg _)]
      _ ≤ metricDensity d.γ y*(|principalZeroBudget K| *ε/(beta d.γ d.radius y)^2) :=
        mul_le_mul_of_nonneg_left (hA.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) hε) (sq_nonneg _))) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · intro i
    have hh := (scalar_principal_density_product_two_jets hY hg hg2 hK d.frame hFrame
      hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy M1 M2 (abs_nonneg _) (abs_nonneg _) hD hD2 a b i i).1
    change |coordDeriv i (fun x => metricDensity d.γ x*scalarPrincipalMatrix d.γ d.g₂ d.radius x a b) y| ≤ _
    exact hh.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.sqrt_nonneg _)) hε) hβ.le).trans_eq (by unfold metricDensity;ring))

end ShrinkingSpheres.ParallelEnergy
