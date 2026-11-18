import Proof.UniformEffectiveFirstCovariantHigher
import Proof.UniformEffectiveFirstStrongHalf

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A single smooth coarse family for the complete effective first
coefficient has BOTH genuine endpoint graphs and the original epsilon
bounds. Constants and smooth families precede all later test sections. -/
theorem uniform_effective_first_covariant_balanced
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ∀ y ∈ Y,
          CoarseCovariantRotationGraph d y (axis i) (P.firstCovariantCoordinateCoarseL b) (S b i y) ∧
          ∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
          ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
            (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b i y)=
              L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H=
              (S b i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
            ‖L‖ ≤ CE*ε ∧ ‖H‖ ≤ CE*ε := by
  obtain ⟨ηL,CL,hηL,hηL1,hCL,hLow⟩ := uniform_effective_first_covariant_strong_half
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηH,CH,hηH,hηH1,hCH,hHigh⟩ := uniform_effective_first_covariant_higher
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let C := CL+CH
  refine ⟨min ηL ηH,C,lt_min hηL hηH,(min_le_left _ _).trans hηL1,add_nonneg hCL hCH,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  obtain ⟨S,hS⟩ := hLow floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P
  obtain ⟨T,hT⟩ := hHigh floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P
  refine ⟨S,?_⟩
  intro b i
  refine ⟨(hS b i).1,?_⟩
  intro y hy
  obtain ⟨hGraph,L,hL,hLN⟩ := (hS b i).2 y hy
  obtain ⟨hGraphH,H,hH,hHN⟩ := (hT b i).2 y hy
  have hSame : T b i y=S b i y := coarseCovariantRotationGraph_unique hGraphH hGraph
  refine ⟨hGraph,L,H,hL,?_,?_,?_⟩
  · simpa only [hSame] using hH
  · exact hLN.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCH) hε)
  · exact hHN.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCL) hε)

end ShrinkingSpheres
