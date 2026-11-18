import Proof.HalfCovariantAdjointPairing
import Proof.PhysicalFirstCoordinateAdjointFamily
import Proof.UniformPhysicalFirstCoordinateData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Covariant derivatives of the SAME true-adjoint coefficients inherit
the required weak bound from the forward derivative. No derivative budget
for an arbitrary frame or an independently chosen adjoint is an input. -/
theorem uniform_physical_first_coordinate_adjoint_derivative_pair_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CB CS CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CB ∧ 0 ≤ CS ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ W : PhysicalFirstCommutatorPacket P CB CS ε,
      ∃ H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (∀ b,ContDiffOn ℝ ∞ (H b) Y) ∧
      (∀ b,∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H b x)=
        (P.firstDerivativeCoordinateHalfL x b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
      ∀ x ∈ Y,∀ b i : I,∀ u v : SphereSobolev (3/2:ℝ),
        |sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
          (halfOperatorCovariantDerivativeL d (fun y => (P.firstDerivativeCoordinateHalfL y b).adjoint)
            (W.coordinateAdjointHigher b) x (axis i) v)| ≤
          CE*ε*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v‖*‖u‖ := by
  have hWProduce := uniform_physical_first_commutator_packet hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηW,CB,CS,hηW,hηW1,hCB,hCS,hWData⟩ := hWProduce
  have hHProduce := uniform_physical_first_coordinate_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηH,CE,hηH,hηH1,hCE,hHData⟩ := hHProduce
  refine ⟨min ηW ηH,CB,CS,CE,lt_min hηW hηH,(min_le_left _ _).trans hηW1,hCB,hCS,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨W⟩ := hWData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CT P
  obtain ⟨H,hH⟩ := hHData floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P
  refine ⟨W,H,(fun b => (hH b).2.1),(fun b x hx => ((hH b).2.2 x hx).1),?_⟩
  intro x hx b i u v
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let D := halfOperatorCovariantDerivativeL d (fun y => P.firstDerivativeCoordinateHalfL y b) (H b) x (axis i)
  have hPair := half_covariant_adjoint_pairing d (fun y => P.firstDerivativeCoordinateHalfL y b)
    (H b) (W.coordinateAdjointHigher b) ((hH b).1.contDiffAt (hY.mem_nhds hx)) (axis i)
    (((hH b).2.2 x hx).1) (W.coordinateAdjointHigher_balanced b hx) u v
  rw [hPair]
  change |⟪J v,D u⟫_ℝ| ≤ CE*ε*‖J v‖*‖u‖
  have hD : ‖D‖ ≤ CE*ε := ((hH b).2.2 x hx).2.2.2 i
  calc
    _ ≤ ‖J v‖*‖D u‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖J v‖*((CE*ε)*‖u‖) := mul_le_mul_of_nonneg_left
      ((D.le_opNorm u).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring
end ShrinkingSpheres
