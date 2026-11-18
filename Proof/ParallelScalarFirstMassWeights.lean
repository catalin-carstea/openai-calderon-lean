import Proof.UniformActualHalfCovariantFirstForm
import Proof.ScalarPrincipalSharpTwoJets
import Proof.PhysicalScalarCoreDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

/-- The two actual scalar density weights in the coefficient-jet sector. -/
def scalarFirstMassWeight (d : Data) (t : Fin 2) (a b k : I) (x : X) : ℝ :=
  (if t=0 then metricDensity d.γ x else fderiv ℝ (metricDensity d.γ) x (axis k))*
    scalarPrincipalMatrix d.γ d.g₂ d.radius x a b

lemma scalar_first_mass_product_weight_bound
    (f g : X → ℝ) (y v : X) (A0 A1 B ε β μ : ℝ)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hμ : 0 ≤ μ)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (hf0 : |f y| ≤ A0*ε/β^2) (hf1 : |fderiv ℝ f y v| ≤ A1*ε/β)
    (hg0 : |g y| ≤ B*μ) (hg1 : |fderiv ℝ g y v| ≤ B*μ) :
    |g y*f y| ≤ B*(A0+A1)*ε/β^2*μ ∧
      |fderiv ℝ (fun x => g x*f x) y v| ≤ B*(A0+A1)*ε/β*μ := by
  have hβp : 0 < β := zero_lt_one.trans_le hβ
  have hf0' : |f y| ≤ A0*ε/β := hf0.trans
    (div_le_div_of_nonneg_left (mul_nonneg hA0 hε) hβp (by nlinarith only [hβ]))
  constructor
  · rw [abs_mul]
    calc
      _ ≤ (B*μ)*(A0*ε/β^2) := mul_le_mul hg0 hf0 (abs_nonneg _) (mul_nonneg hB hμ)
      _ ≤ (B*μ)*((A0+A1)*ε/β^2) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA1) hε) (sq_nonneg _))
        (mul_nonneg hB hμ)
      _ = _ := by ring
  · have hD := DFunLike.congr_fun (fderiv_mul hg hf) v
    change fderiv ℝ (fun x => g x*f x) y v=_ at hD
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hD
    rw [hD]
    calc
      _ ≤ |g y*fderiv ℝ f y v|+|f y*fderiv ℝ g y v| := abs_add_le _ _
      _ ≤ (B*μ)*(A1*ε/β)+(A0*ε/β)*(B*μ) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul hg0 hf1 (abs_nonneg _) (mul_nonneg hB hμ))
          (mul_le_mul hf0' hg1 (abs_nonneg _) (by positivity))
      _ = _ := by ring

/-- Common genuine first jets for both actual scalar-density weights,
with constants before every radius profile and orthonormal frame. -/
theorem uniform_scalar_first_mass_weight_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ t : Fin 2,∀ a b k : I,
      ContDiffOn ℝ ∞ (scalarFirstMassWeight d t a b k) Y ∧ ∀ y ∈ Y,∀ i : I,
        |scalarFirstMassWeight d t a b k y| ≤ A*ε/(beta d.γ d.radius y)^2*metricDensity d.γ y ∧
        |fderiv ℝ (scalarFirstMassWeight d t a b k) y (axis i)| ≤ A*ε/beta d.γ d.radius y*metricDensity d.γ y := by
  let A0 := abs (principalZeroBudget K)
  let A1 := abs (principalFirstBudget K (abs (M ⟨1,by omega⟩)))
  let B1 := 27*K*|M ⟨1,by omega⟩|
  let B2 := 972*K^2*|M ⟨1,by omega⟩|^2+27*K*|M ⟨2,by omega⟩|
  let B := 1+B1+B2
  have hA0 : 0 ≤ A0 := abs_nonneg _
  have hA1 : 0 ≤ A1 := abs_nonneg _
  have hB1 : 0 ≤ B1 := by dsimp only [B1];positivity
  have hB2 : 0 ≤ B2 := by dsimp only [B2];positivity
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have h1B : 1 ≤ B := by dsimp only [B];linarith only [hB1,hB2]
  have hB1B : B1 ≤ B := by dsimp only [B];linarith only [hB2]
  have hB2B : B2 ≤ B := by dsimp only [B];linarith only [hB1]
  refine ⟨B*(A0+A1),mul_nonneg hB (add_nonneg hA0 hA1),?_⟩
  intro floor hf ε hε hε1 d hd t a b k
  let f := fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b
  let g := fun x => if t=0 then metricDensity d.γ x else fderiv ℝ (metricDensity d.γ) x (axis k)
  have hFS : ContDiffOn ℝ ∞ f Y := hd.contDiffOn_scalarPrincipalMatrix_entry hSub (zero_lt_one.trans_le hK) a b
  have hμS : ContDiffOn ℝ ∞ (metricDensity d.γ) Y :=
    (hd.1.1.contDiffOn_density (zero_lt_one.trans_le hK)).mono hSub
  have hGS : ContDiffOn ℝ ∞ g Y := by
    dsimp only [g]
    split_ifs
    · exact hμS
    · exact contDiffOn_coordDeriv hY hμS k
  refine ⟨hGS.mul hFS,?_⟩
  intro y hy i
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hWeights := scalar_principal_sharp_two_jet_weights hY hg hg2 hK d.frame hFrame
    hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
    (abs_nonneg _) (abs_nonneg _)
    (fun i j => (hd.1.reference_fderiv_bound (by omega) (hSub hy) i j).trans (le_abs_self _))
    (fun i j => (hd.1.reference_second_fderiv_bound hm (hSub hy) i j).trans (le_abs_self _)) a b i i
  have hf0 : |f y| ≤ A0*ε/(beta d.γ d.radius y)^2 := hWeights.1.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε) (sq_nonneg _))
  have hf1 : |fderiv ℝ f y (axis i)| ≤ A1*ε/beta d.γ d.radius y := hWeights.2.1.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε) (zero_le_one.trans hβ))
  have hDensity (r s : I) := hd.1.1.relative_density_coordinate_jets hΩ (zero_lt_one.trans_le hK) (hSub hy)
    |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (abs_nonneg _) (abs_nonneg _)
    (fun j k => (hd.1.reference_fderiv_bound (by omega) (hSub hy) j k).trans (le_abs_self _))
    (fun j k => (hd.1.reference_second_fderiv_bound hm (hSub hy) j k).trans (le_abs_self _)) r s
  have hg0 : |g y| ≤ B*metricDensity d.γ y := by
    dsimp only [g]
    split_ifs
    · rw [abs_of_nonneg hμ]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h1B hμ
    · exact (hDensity k k).1.trans (mul_le_mul_of_nonneg_right hB1B hμ)
  have hg1 : |fderiv ℝ g y (axis i)| ≤ B*metricDensity d.γ y := by
    dsimp only [g]
    split_ifs
    · exact (hDensity i i).1.trans (mul_le_mul_of_nonneg_right hB1B hμ)
    · exact (hDensity k i).2.trans (mul_le_mul_of_nonneg_right hB2B hμ)
  exact scalar_first_mass_product_weight_bound f g y (axis i) A0 A1 B ε _ _ hA0 hA1 hB hε hβ hμ
    ((hFS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hGS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hf0 hf1 hg0 hg1

end ShrinkingSpheres.ParallelEnergy
