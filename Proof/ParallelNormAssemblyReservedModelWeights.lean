import Proof.UniformActualHalfCovariantFirstForm
import Proof.InverseMetricDerivative

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

def modelPotentialLeadingWeight (d : Data) (k c : I) (x : X) : ℝ :=
  metricDensity d.γ x*(d.γ x)⁻¹ k c

/-- Fixed-coordinate model-leading weights include the actual density;
only reference metric derivatives enter these relative first-jet budgets. -/
theorem uniform_model_potential_leading_weight_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q0 Q1 : ℝ,0 ≤ Q0 ∧ 0 ≤ Q1 ∧
    ∀ floor ε d,Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ k c : I,
      ContDiffOn ℝ ∞ (modelPotentialLeadingWeight d k c) Y ∧ ∀ y ∈ Y,∀ i : I,
        |modelPotentialLeadingWeight d k c y| ≤ Q0*metricDensity d.γ y ∧
        |fderiv ℝ (modelPotentialLeadingWeight d k c) y (axis i)| ≤ Q1*metricDensity d.γ y := by
  let M1 := |M ⟨1,by omega⟩|
  let MD := 27*K*M1
  let MI := 9*K^2*M1
  have hKp := zero_lt_one.trans_le hK
  have hK0 := zero_le_one.trans hK
  have hMD : 0 ≤ MD := by dsimp only [MD,M1];positivity
  have hMI : 0 ≤ MI := by dsimp only [MI,M1];positivity
  refine ⟨K,MD*K+MI,hK0,by positivity,?_⟩
  intro floor ε d hd k c
  have hMu := (hd.1.1.contDiffOn_density hKp).mono hSub
  have hInv := (hd.1.1.contDiffOn_inverse_entry hKp k c).mono hSub
  refine ⟨hMu.mul hInv,?_⟩
  intro y hy i
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hI := hd.1.1.inverse_entry_bound hKp (hSub hy) k c
  have hID : |fderiv ℝ (fun x => (d.γ x)⁻¹ k c) y (axis i)| ≤ MI := by
    simpa only [norm_axis,mul_one,MI,M1] using
      hd.1.1.inverse_derivative_entry_bound hΩ hKp (hSub hy) M1 (abs_nonneg _)
        (fun a b => (hd.1.reference_fderiv_bound (by omega) (hSub hy) a b).trans (le_abs_self _))
        (axis i) k c
  have hMDensity : |fderiv ℝ (metricDensity d.γ) y (axis i)| ≤ MD*metricDensity d.γ y :=
    hd.relative_density_axis_bound hΩ (by omega) hKp hy i
  have hDiff := DFunLike.congr_fun (fderiv_mul
    ((hMu.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hInv.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))) (axis i)
  change fderiv ℝ (modelPotentialLeadingWeight d k c) y (axis i)=_ at hDiff
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hDiff
  constructor
  · change |metricDensity d.γ y*(d.γ y)⁻¹ k c| ≤ _
    rw [abs_mul,abs_of_nonneg hμ]
    exact (mul_le_mul_of_nonneg_left hI hμ).trans_eq (mul_comm _ _)
  · rw [hDiff]
    calc
      _ ≤ |metricDensity d.γ y*fderiv ℝ (fun x => (d.γ x)⁻¹ k c) y (axis i)|+
          |(d.γ y)⁻¹ k c*fderiv ℝ (metricDensity d.γ) y (axis i)| := abs_add_le _ _
      _ = metricDensity d.γ y*|fderiv ℝ (fun x => (d.γ x)⁻¹ k c) y (axis i)|+
          |(d.γ y)⁻¹ k c| *|fderiv ℝ (metricDensity d.γ) y (axis i)| := by
        rw [abs_mul,abs_of_nonneg hμ,abs_mul]
      _ ≤ metricDensity d.γ y*MI+K*(MD*metricDensity d.γ y) := add_le_add
        (mul_le_mul_of_nonneg_left hID hμ)
        (mul_le_mul hI hMDensity (abs_nonneg _) hK0)
      _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
