import Proof.PhysicalTruncatedCovariantDerivativeNormalForm
import Proof.UniformScalarPrincipalConnectionTwoJets
import Proof.InclusionWeightedCoarseCovariantJets
import Proof.UniformPhysicalFirstCoordinateCoarseTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME effective first coefficient in the exact ordered-covariant
residual normal form has genuine coarse two-jets with the original sharp
epsilon/beta, epsilon, epsilon beta bounds. -/
theorem uniform_physical_first_covariant_coordinate_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∀ b i : I,ContDiffOn ℝ ∞ (P.firstCovariantCoordinateCoarseL b) Y ∧
          ContDiffOn ℝ ∞ (S b i) Y ∧ ∀ y ∈ Y,
          CoarseCovariantRotationGraph d y (axis i) (P.firstCovariantCoordinateCoarseL b) (S b i y) ∧
          ‖P.firstCovariantCoordinateCoarseL b y‖ ≤ C*ε/beta d.γ d.radius y ∧
          ‖S b i y‖ ≤ C*ε ∧
          ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
            CoarseCovariantRotationGraph d y (axis j) (S b i) T ∧ ‖T‖ ≤ C*ε*beta d.γ d.radius y := by
  obtain ⟨η,CB,hη,hη1,hCB,hFull⟩ := uniform_physical_first_coordinate_coarse_two_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets
    hY hΩ (by omega) K ρ c₀ M Cj hK
  let C := CB+CW
  refine ⟨η,C,hη,hη1,add_nonneg hCB hCW,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hε1 : ε ≤ 1 := hSmall.trans hη1
  obtain ⟨S0,hS0⟩ := hFull floor hf ε hε hSmall d hd CF CT P
  have hW := hWeight floor hf ε hε hε1 d hd
  let w := scalarPrincipalConnectionWeight d
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let S := fun (b i : I) (x : X) => S0 b i x-coordDeriv i (w b) x • I10
  have hWS (b : I) : ContDiffOn ℝ ∞ (w b) Y := (hW b).1
  have hWDS (b i : I) : ContDiffOn ℝ ∞ (coordDeriv i (w b)) Y := contDiffOn_coordDeriv hY (hWS b) i
  have hFWS (b : I) : ContDiffOn ℝ ∞ (fun x => w b x • I10) Y := (hWS b).smul contDiffOn_const
  have hDWIS (b i : I) : ContDiffOn ℝ ∞ (fun x => coordDeriv i (w b) x • I10) Y :=
    (hWDS b i).smul contDiffOn_const
  refine ⟨S,?_⟩
  intro b i
  have hFS : ContDiffOn ℝ ∞ (P.firstCovariantCoordinateCoarseL b) Y :=
    (hS0 b i).1.sub (hFWS b)
  have hSS : ContDiffOn ℝ ∞ (S b i) Y := (hS0 b i).2.1.sub (hDWIS b i)
  refine ⟨hFS,hSS,?_⟩
  intro y hy
  let β := beta d.γ d.radius y
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hB := (hS0 b i).2.2 y hy
  have hw (i j : I) := (hW b).2 y hy i j
  have hWG (j : I) := coarse_covariant_scalar_inclusion_two_jets d (w b) y i j
    ((hWS b).contDiffAt (hY.mem_nhds hy))
  have hFirstGraph : CoarseCovariantRotationGraph d y (axis i) (P.firstCovariantCoordinateCoarseL b) (S b i y) :=
    hB.1.sub (hWG i).1 (((hS0 b i).1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hFWS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hW0 : ‖w b y • I10‖ ≤ CW*ε/β :=
    (norm_scalar_coarse_inclusion_le _).trans ((hw i i).1.trans (by
      change CW*ε/β^2 ≤ CW*ε/β
      gcongr
      nlinarith only [hβ]))
  have hW1 : ‖coordDeriv i (w b) y • I10‖ ≤ CW*ε :=
    (norm_scalar_coarse_inclusion_le _).trans ((hw i i).2.1.trans (div_le_self (mul_nonneg hCW hε) hβ))
  refine ⟨hFirstGraph,?_,?_,?_⟩
  · have hh : ‖P.firstCovariantCoordinateCoarseL b y‖ ≤ CB*ε/β+CW*ε/β :=
      (norm_sub_le _ _).trans (add_le_add hB.2.1 hW0)
    exact hh.trans_eq (by dsimp only [C];ring)
  · have hh : ‖S b i y‖ ≤ CB*ε+CW*ε :=
      (norm_sub_le _ _).trans (add_le_add hB.2.2.1 hW1)
    exact hh.trans_eq (by dsimp only [C];ring)
  · intro j
    obtain ⟨T0,hT0,hT0N⟩ := hB.2.2.2 j
    let TW := coordDeriv j (coordDeriv i (w b)) y • I10
    refine ⟨T0-TW,?_,?_⟩
    · exact hT0.sub (hWG j).2
        (((hS0 b i).2.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hDWIS b i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    · have hWN : ‖TW‖ ≤ CW*ε*β := (norm_scalar_coarse_inclusion_le _).trans
        ((hw i j).2.2.trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ (mul_nonneg hCW hε)))
      have hh : ‖T0-TW‖ ≤ CB*ε*β+CW*ε*β :=
        (norm_sub_le _ _).trans (add_le_add hT0N hWN)
      exact hh.trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres
