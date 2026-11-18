import Proof.ParallelNormAssemblyUniform
import Proof.ParallelNormAssemblyReservedComplete
import Proof.ParallelFirstSelf
import Proof.ParallelScalarFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set MeasureTheory

namespace ShrinkingSpheres
open ParallelEnergy

/-- The complete physical norm comparison, assembled from the three actual
uniform sector bounds on the same fixed first and potential packets. -/
theorem uniform_physical_truncated_norm_comparison_closed {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) (hCF : 0 ≤ CF) (hCT : 0 ≤ CT) :
    UniformPhysicalTruncatedNormComparison Y Ω K ρ c₀ M Cj CF CT := by
  apply uniform_physical_truncated_norm_comparison_of_uniform_remaining_sectors
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT
  intro CB CS CG CK hCB hCS hCG hCK
  obtain ⟨ηF,CFB,hηF,hηF1,hCFB,hFirst⟩ := uniform_first_self_norm_comparison
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT CB CS CG CK hCF hCT hCB hCS hCG hCK
  obtain ⟨ηS,CSB,hηS,hηS1,hCSB,hCross⟩ := uniform_scalar_first_cross_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT CB CS CG CK hCF hCT hCB hCS hCG hCK
  obtain ⟨B,ηR,CR,hηR,hηR1,hCR,hReserved⟩ :=
    uniform_reserved_complex_density_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT
      CB CS CG CK hCB hCS hCG hCK
  let C : Fin 5 → ℝ := ![0,CFB,0,CSB,CR]
  refine ⟨max 1 B,min ηF (min ηS ηR),C,
    lt_min hηF (lt_min hηS hηR),(min_le_left _ _).trans hηF1,?_,?_⟩
  · intro i
    fin_cases i <;> simp [C,hCFB,hCSB,hCR]
  · intro floor hf ε hε hSmall d hd P WF W φ hφ E D
    have hf1 : 1 ≤ floor := (le_max_left 1 B).trans hf
    have hfB : B ≤ floor := (le_max_right 1 B).trans hf
    have heF : ε ≤ ηF := hSmall.trans (min_le_left _ _)
    have heS : ε ≤ ηS := (hSmall.trans (min_le_right _ _)).trans (min_le_left _ _)
    have heR : ε ≤ ηR := (hSmall.trans (min_le_right _ _)).trans (min_le_right _ _)
    have hF := (hFirst floor hf1 ε hε heF d hd P WF W φ E D hφ).2
    have hS := (hCross floor hf1 ε hε heS d hd P WF W φ E D hφ).2
    have hR := (hReserved floor hfB ε hε heR d hd P WF W φ hφ E D).2
    exact ⟨by simpa [C] using hF,by simpa [C] using hS,by simpa [C] using hR⟩

end ShrinkingSpheres
