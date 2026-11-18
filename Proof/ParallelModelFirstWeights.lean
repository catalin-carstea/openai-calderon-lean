import Proof.ParallelModelFirstHodgeIntegral
import Proof.InverseMetricDerivative
import Proof.ProfileRadiusSecondJet
import Proof.UniformActualHalfCovariantFirstForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

theorem uniform_model_first_leading_weight_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q1 : ℝ,0 ≤ Q1 ∧ ∀ floor ε : ℝ,∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ k c : I,
      ContDiffOn ℝ ∞ (modelFirstLeadingWeight d k c) Y ∧ ∀ y ∈ Y,∀ i : I,
      |modelFirstLeadingWeight d k c y| ≤ K*metricDensity d.γ y ∧
      |fderiv ℝ (modelFirstLeadingWeight d k c) y (axis i)| ≤ Q1*metricDensity d.γ y := by
  let MD := 27*K*|M ⟨1,by omega⟩|
  let DI := 9*K^2*|M ⟨1,by omega⟩|
  have hMD : 0 ≤ MD := by dsimp only [MD];positivity
  have hDI : 0 ≤ DI := by dsimp only [DI];positivity
  refine ⟨MD*K+DI,by positivity,?_⟩
  intro floor ε d hd k c
  have hMuS := (hd.1.1.contDiffOn_density (zero_lt_one.trans_le hK)).mono hSub
  have hGS := (hd.1.1.contDiffOn_inverse_entry (zero_lt_one.trans_le hK) k c).mono hSub
  refine ⟨hMuS.mul hGS,?_⟩
  intro y hy i
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hG : |(d.γ y)⁻¹ k c| ≤ K := hd.1.1.inverse_entry_bound (zero_lt_one.trans_le hK) (hSub hy) k c
  have hDG : |fderiv ℝ (fun x => (d.γ x)⁻¹ k c) y (axis i)| ≤ DI := by
    simpa only [norm_axis,mul_one] using hd.1.1.inverse_derivative_entry_bound hΩ
      (zero_lt_one.trans_le hK) (hSub hy) |M ⟨1,by omega⟩| (abs_nonneg _)
      (fun p q => (hd.1.reference_fderiv_bound (by omega) (hSub hy) p q).trans (le_abs_self _)) (axis i) k c
  have hDM : |fderiv ℝ (metricDensity d.γ) y (axis i)| ≤ MD*metricDensity d.γ y :=
    hd.relative_density_axis_bound hΩ hm (zero_lt_one.trans_le hK) hy i
  have hDiff := DFunLike.congr_fun (fderiv_mul
    ((hMuS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hGS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))) (axis i)
  change fderiv ℝ (modelFirstLeadingWeight d k c) y (axis i)=_ at hDiff
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hDiff
  constructor
  · rw [modelFirstLeadingWeight,abs_mul,abs_of_nonneg hμ]
    exact (mul_le_mul_of_nonneg_left hG hμ).trans_eq (mul_comm _ _)
  · rw [hDiff]
    calc
      _ ≤ |metricDensity d.γ y*fderiv ℝ (fun x => (d.γ x)⁻¹ k c) y (axis i)|+
          |(d.γ y)⁻¹ k c*fderiv ℝ (metricDensity d.γ) y (axis i)| := abs_add_le _ _
      _ ≤ metricDensity d.γ y*DI+K*(MD*metricDensity d.γ y) := by
        simp only [abs_mul,abs_of_nonneg hμ]
        exact add_le_add (mul_le_mul_of_nonneg_left hDG hμ)
          (mul_le_mul hG hDM (abs_nonneg _) (zero_le_one.trans hK))
      _ = _ := by ring

def modelFirstZeroWeight (d : Data) (k c : I) (y : X) : ℝ :=
  modelFirstLeadingWeight d k c y*coordDeriv k (fun x => Real.log (d.radius x)) y

/-- The physical zero-model weight has its genuine beta and beta² jets;
no small radius or frame derivative bound is introduced. -/
theorem uniform_model_first_zero_weight_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q0 Q1 : ℝ,0 ≤ Q0 ∧ 0 ≤ Q1 ∧
      ∀ floor,1 ≤ floor → ∀ ε : ℝ,∀ d,Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ k c : I,
      ContDiffOn ℝ ∞ (modelFirstZeroWeight d k c) Y ∧ ∀ y ∈ Y,∀ i : I,
      |modelFirstZeroWeight d k c y| ≤ Q0*beta d.γ d.radius y*metricDensity d.γ y ∧
      |fderiv ℝ (modelFirstZeroWeight d k c) y (axis i)| ≤ Q1*(beta d.γ d.radius y)^2*metricDensity d.γ y := by
  obtain ⟨QL,hQL,hLead⟩ := uniform_model_first_leading_weight_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  let G := 9*K*|M ⟨1,by omega⟩|
  let L2 := 9*K^2*|Cj 2|+3*G*K
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hL2 : 0 ≤ L2 := by dsimp only [L2];positivity
  refine ⟨K^2,K*L2+K*QL,sq_nonneg K,by positivity,?_⟩
  intro floor hf ε d hd k c
  let w := modelFirstLeadingWeight d k c
  let ell := coordDeriv k (fun x => Real.log (d.radius x))
  have hW := hLead floor ε d hd k c
  have hLog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hEll : ContDiffOn ℝ ∞ ell Y := contDiffOn_coordDeriv hY hLog k
  refine ⟨hW.1.mul hEll,?_⟩
  intro y hy i
  let β := beta d.γ d.radius y
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hg : Elliptic Y K d.γ := ⟨fun p q => (hd.1.1.1 p q).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hFrame : ∀ x ∈ Y,∀ p q,metricPair d.γ x (d.frame x p) (d.frame x q)=if p=q then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hE0 : |ell y| ≤ K*β := hg.coord_logRadius_bound hK d.frame d.radius hy (hFrame y hy) k
  have hGamma (p q r : I) : |christoffel d.γ y p q r| ≤ G :=
    hd.1.1.christoffel_entry_bound (zero_lt_one.trans_le hK) (hSub hy) |M ⟨1,by omega⟩| (abs_nonneg _)
      (fun p q => (hd.1.reference_fderiv_bound (by omega) (hSub hy) p q).trans (le_abs_self _)) p q r
  have hE1 : |fderiv ℝ ell y (axis i)| ≤ L2*β^2 :=
    hd.2.2.2.2.1.coordinate_log_second_bound hg hK d.frame hFrame hf hG hy hGamma i k
  have hDiff := DFunLike.congr_fun (fderiv_mul
    ((hW.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hEll.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))) (axis i)
  change fderiv ℝ (modelFirstZeroWeight d k c) y (axis i)=_ at hDiff
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hDiff
  constructor
  · rw [modelFirstZeroWeight,abs_mul]
    exact (mul_le_mul (hW.2 y hy i).1 hE0 (abs_nonneg _) (mul_nonneg (zero_le_one.trans hK) hμ)).trans_eq (by ring)
  · rw [hDiff]
    have hE02 : |ell y| ≤ K*β^2 := hE0.trans (mul_le_mul_of_nonneg_left (by nlinarith only [hβ] : β ≤ β^2) (zero_le_one.trans hK))
    calc
      _ ≤ |w y*fderiv ℝ ell y (axis i)|+|ell y*fderiv ℝ w y (axis i)| := abs_add_le _ _
      _ ≤ (K*metricDensity d.γ y)*(L2*β^2)+(K*β^2)*(QL*metricDensity d.γ y) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (hW.2 y hy i).1 hE1 (abs_nonneg _) (mul_nonneg (zero_le_one.trans hK) hμ))
          (mul_le_mul hE02 (hW.2 y hy i).2 (abs_nonneg _) (by positivity))
      _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
