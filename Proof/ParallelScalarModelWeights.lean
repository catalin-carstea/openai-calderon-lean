import Proof.PhysicalScalarCoreDomain
import Proof.ScalarPrincipalSharpTwoJets
import Proof.InverseMetricDerivative
import Proof.ProfileRadiusSecondJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

/-- Ordinary coordinates for the actual inverse-metric contraction. -/
def scalarModelLeadingWeight (d : Data) (a b k c : I) (x : X) : ℝ :=
  scalarPrincipalMatrix d.γ d.g₂ d.radius x a b*(d.γ x)⁻¹ k c

def scalarModelZeroWeight (d : Data) (a b k c : I) (x : X) : ℝ :=
  scalarModelLeadingWeight d a b k c x*coordDeriv k (fun y => Real.log (d.radius y)) x

lemma scalar_model_background_product_jet
    (f g : X → ℝ) (y v : X) (A0 A1 B D ε β : ℝ)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hB : 0 ≤ B) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (hf0 : |f y| ≤ A0*ε/β^2) (hf1 : |fderiv ℝ f y v| ≤ A1*ε/β)
    (hg0 : |g y| ≤ B) (hg1 : |fderiv ℝ g y v| ≤ D) :
    |f y*g y| ≤ (A0*B)*ε/β^2 ∧
    |fderiv ℝ (fun x => f x*g x) y v| ≤ (A1*B+A0*D)*ε/β := by
  have hβp := zero_lt_one.trans_le hβ
  have hf0' : |f y| ≤ A0*ε/β := hf0.trans
    (div_le_div_of_nonneg_left (mul_nonneg hA0 hε) hβp (by nlinarith only [hβ]))
  constructor
  · rw [abs_mul]
    exact (mul_le_mul hf0 hg0 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  · have hDiff := DFunLike.congr_fun (fderiv_mul hf hg) v
    change fderiv ℝ (fun x => f x*g x) y v=_ at hDiff
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hDiff
    rw [hDiff]
    calc
      _ ≤ |f y*fderiv ℝ g y v|+|g y*fderiv ℝ f y v| := abs_add_le _ _
      _ ≤ (A0*ε/β)*D+B*(A1*ε/β) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul hf0' hg1 (abs_nonneg _) (by positivity))
          (mul_le_mul hg0 hf1 (abs_nonneg _) hB)
      _ = _ := by ring

/-- The SAME actual scalar matrix times inverse-metric coordinate weights
retains sharp epsilon/beta² and epsilon/beta first jets. -/
theorem uniform_scalar_model_leading_weight_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ A0 A1 : ℝ,0 ≤ A0 ∧ 0 ≤ A1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ a b k c : I,
      ContDiffOn ℝ ∞ (scalarModelLeadingWeight d a b k c) Y ∧ ∀ y ∈ Y,∀ i : I,
        |scalarModelLeadingWeight d a b k c y| ≤ A0*ε/(beta d.γ d.radius y)^2 ∧
        |fderiv ℝ (scalarModelLeadingWeight d a b k c) y (axis i)| ≤ A1*ε/beta d.γ d.radius y := by
  let B0 := abs (principalZeroBudget K)
  let B1 := abs (principalFirstBudget K (abs (M ⟨1,by omega⟩)))
  let DG := 9*K^2*|M ⟨1,by omega⟩|
  have hB0 : 0 ≤ B0 := abs_nonneg _
  have hB1 : 0 ≤ B1 := abs_nonneg _
  have hDG : 0 ≤ DG := by dsimp only [DG];positivity
  refine ⟨B0*K,B1*K+B0*DG,mul_nonneg hB0 (zero_le_one.trans hK),by positivity,?_⟩
  intro floor hf ε hε hε1 d hd a b k c
  let f := fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b
  let g := fun x => (d.γ x)⁻¹ k c
  have hFS : ContDiffOn ℝ ∞ f Y := hd.contDiffOn_scalarPrincipalMatrix_entry hSub (zero_lt_one.trans_le hK) a b
  have hGS : ContDiffOn ℝ ∞ g Y := (hd.1.1.contDiffOn_inverse_entry (zero_lt_one.trans_le hK) k c).mono hSub
  refine ⟨hFS.mul hGS,?_⟩
  intro y hy i
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
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
  have hf0 : |f y| ≤ B0*ε/(beta d.γ d.radius y)^2 := hWeights.1.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε) (sq_nonneg _))
  have hf1 : |fderiv ℝ f y (axis i)| ≤ B1*ε/beta d.γ d.radius y := hWeights.2.1.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε) (zero_le_one.trans hβ))
  have hg0 : |g y| ≤ K := hd.1.1.inverse_entry_bound (zero_lt_one.trans_le hK) (hSub hy) k c
  have hg1 : |fderiv ℝ g y (axis i)| ≤ DG := by
    simpa only [norm_axis,mul_one] using hd.1.1.inverse_derivative_entry_bound hΩ
      (zero_lt_one.trans_le hK) (hSub hy) |M ⟨1,by omega⟩| (abs_nonneg _)
      (fun i j => (hd.1.reference_fderiv_bound (by omega) (hSub hy) i j).trans (le_abs_self _)) (axis i) k c
  exact scalar_model_background_product_jet f g y (axis i) B0 B1 K DG ε _ hB0 hB1
    (zero_le_one.trans hK) hDG hε hβ
    ((hFS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hGS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hf0 hf1 hg0 hg1

/-- The actual log-radius factor is paired with the sharp scalar weight
before its first derivative is bounded. -/
theorem uniform_scalar_model_zero_weight_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Z0 Z1 : ℝ,0 ≤ Z0 ∧ 0 ≤ Z1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ a b k c : I,
      ContDiffOn ℝ ∞ (scalarModelZeroWeight d a b k c) Y ∧ ∀ y ∈ Y,∀ i : I,
        |scalarModelZeroWeight d a b k c y| ≤ Z0*ε/beta d.γ d.radius y ∧
        |fderiv ℝ (scalarModelZeroWeight d a b k c) y (axis i)| ≤ Z1*ε := by
  obtain ⟨A0,A1,hA0,hA1,hLeading⟩ := uniform_scalar_model_leading_weight_jets hY hΩ hSub hm K ρ c₀ M Cj hK
  let G := 9*K*|M ⟨1,by omega⟩|
  let L2 := 9*K^2*|Cj 2|+3*G*K
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hL2 : 0 ≤ L2 := by dsimp only [L2];positivity
  refine ⟨A0*K,A1*K+A0*L2,mul_nonneg hA0 (zero_le_one.trans hK),by positivity,?_⟩
  intro floor hf ε hε hε1 d hd a b k c
  let w := scalarModelLeadingWeight d a b k c
  let ell := coordDeriv k (fun x => Real.log (d.radius x))
  have hW := hLeading floor hf ε hε hε1 d hd a b k c
  have hLog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hEll : ContDiffOn ℝ ∞ ell Y := contDiffOn_coordDeriv hY hLog k
  refine ⟨hW.1.mul hEll,?_⟩
  intro y hy i
  let β := beta d.γ d.radius y
  have hβ : 0 < β := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hE0 : |ell y| ≤ K*β := hg.coord_logRadius_bound hK d.frame d.radius hy (hFrame y hy) k
  have hGamma (p q r : I) : |christoffel d.γ y p q r| ≤ G :=
    hd.1.1.christoffel_entry_bound (zero_lt_one.trans_le hK) (hSub hy) |M ⟨1,by omega⟩| (abs_nonneg _)
      (fun i j => (hd.1.reference_fderiv_bound (by omega) (hSub hy) i j).trans (le_abs_self _)) p q r
  have hE1 : |fderiv ℝ ell y (axis i)| ≤ L2*β^2 :=
    hd.2.2.2.2.1.coordinate_log_second_bound hg hK d.frame hFrame hf hG hy hGamma i k
  have hDiff := DFunLike.congr_fun (fderiv_mul
    ((hW.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hEll.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))) (axis i)
  change fderiv ℝ (scalarModelZeroWeight d a b k c) y (axis i)=_ at hDiff
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hDiff
  constructor
  · change |w y*ell y| ≤ _
    rw [abs_mul]
    exact (mul_le_mul ((hW.2 y hy i).1) hE0 (abs_nonneg _) (by positivity)).trans_eq (by dsimp only [β] at hβ ⊢;field_simp [hβ.ne'] <;> ring)
  · rw [hDiff]
    calc
      _ ≤ |w y*fderiv ℝ ell y (axis i)|+|ell y*fderiv ℝ w y (axis i)| := abs_add_le _ _
      _ ≤ (A0*ε/β^2)*(L2*β^2)+(K*β)*(A1*ε/β) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul ((hW.2 y hy i).1) hE1 (abs_nonneg _) (by positivity))
          (mul_le_mul hE0 ((hW.2 y hy i).2) (abs_nonneg _) (by positivity))
      _ = _ := by dsimp only [β] at hβ ⊢;field_simp [hβ.ne'] <;> ring

end ShrinkingSpheres.ParallelEnergy
