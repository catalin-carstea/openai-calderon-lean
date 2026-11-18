import Proof.ParallelScalarModelWeights
import Proof.UniformActualHalfCovariantFirstForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

def scalarModelZeroDensityWeight (d : Data) (a b k c : I) (x : X) : ℝ :=
  metricDensity d.γ x*scalarModelZeroWeight d a b k c x

lemma scalarModelZeroDensityWeight_symmetric {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (a b k c : I) :
    scalarModelZeroDensityWeight d a b k c y=scalarModelZeroDensityWeight d b a k c y := by
  have hA : (scalarPrincipalMatrix d.γ d.g₂ d.radius y).IsHermitian :=
    (hd.principal_properties hK (hSub hy)).1.isHermitian.smul (by simp [isSelfAdjoint_iff])
  have hSym := Matrix.isHermitian_iff_isSymm.mp hA
  have hEntry : scalarPrincipalMatrix d.γ d.g₂ d.radius y a b=
      scalarPrincipalMatrix d.γ d.g₂ d.radius y b a := hSym.apply b a
  exact congrArg (fun t : ℝ => metricDensity d.γ y*((t*(d.γ y)⁻¹ k c)*
    coordDeriv k (fun x => Real.log (d.radius x)) y)) hEntry

/-- The exact physical density is included before estimating the
log-radius-weighted scalar pair. -/
theorem uniform_scalar_model_zero_density_weight_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Z0 Z1 : ℝ,0 ≤ Z0 ∧ 0 ≤ Z1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ a b k c : I,
      ContDiffOn ℝ ∞ (scalarModelZeroDensityWeight d a b k c) Y ∧ ∀ y ∈ Y,∀ i : I,
        |scalarModelZeroDensityWeight d a b k c y| ≤ Z0*ε/beta d.γ d.radius y*metricDensity d.γ y ∧
        |fderiv ℝ (scalarModelZeroDensityWeight d a b k c) y (axis i)| ≤ Z1*ε*metricDensity d.γ y := by
  obtain ⟨Z0,Z1,hZ0,hZ1,hW⟩ := uniform_scalar_model_zero_weight_jets hY hΩ hSub hm K ρ c₀ M Cj hK
  let MD := 27*K*|M ⟨1,by omega⟩|
  have hMD : 0 ≤ MD := by dsimp only [MD];positivity
  refine ⟨Z0,MD*Z0+Z1,hZ0,by positivity,?_⟩
  intro floor hf ε hε hε1 d hd a b k c
  have hWS := hW floor hf ε hε hε1 d hd a b k c
  have hMuS := (hd.1.1.contDiffOn_density (zero_lt_one.trans_le hK)).mono hSub
  refine ⟨hMuS.mul hWS.1,?_⟩
  intro y hy i
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hDiff := DFunLike.congr_fun (fderiv_mul
    ((hMuS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hWS.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))) (axis i)
  change fderiv ℝ (scalarModelZeroDensityWeight d a b k c) y (axis i)=_ at hDiff
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hDiff
  constructor
  · change |metricDensity d.γ y*scalarModelZeroWeight d a b k c y| ≤ _
    rw [abs_mul,abs_of_nonneg hμ]
    exact (mul_le_mul_of_nonneg_left (hWS.2 y hy i).1 hμ).trans_eq (by ring)
  · rw [hDiff]
    have hW0 : |scalarModelZeroWeight d a b k c y| ≤ Z0*ε :=
      (hWS.2 y hy i).1.trans (div_le_self (mul_nonneg hZ0 hε) hβ)
    calc
      _ ≤ |metricDensity d.γ y*fderiv ℝ (scalarModelZeroWeight d a b k c) y (axis i)|+
          |scalarModelZeroWeight d a b k c y*fderiv ℝ (metricDensity d.γ) y (axis i)| := abs_add_le _ _
      _ ≤ metricDensity d.γ y*(Z1*ε)+(Z0*ε)*(MD*metricDensity d.γ y) := by
        simp only [abs_mul,abs_of_nonneg hμ]
        exact add_le_add (mul_le_mul_of_nonneg_left (hWS.2 y hy i).2 hμ)
          (mul_le_mul hW0 (hd.relative_density_axis_bound hΩ (by omega) (zero_lt_one.trans_le hK) hy i)
            (abs_nonneg _) (mul_nonneg hZ0 hε))
      _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
