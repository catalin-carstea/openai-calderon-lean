import Proof.PhysicalFirstCoordinateCoarse
import Proof.UniformPrincipalModelCoordinateCoarseTwoJets
import Proof.UniformPrincipalFirstCorrectionCoordinateCoarseTwoJets
import Proof.UniformPhysicalFirstErrorCoordinateCoarseTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The complete SAME actual first-base coordinate coefficient has genuine
coarse covariant jets through two with epsilon/beta, epsilon, epsilon beta
bounds, uniformly over the original profiles and arbitrary smooth frames. -/
theorem uniform_physical_first_coordinate_coarse_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∀ b i : I,ContDiffOn ℝ ∞ (P.firstDerivativeCoordinateCoarseL b) Y ∧
          ContDiffOn ℝ ∞ (S b i) Y ∧ ∀ y ∈ Y,
          CoarseCovariantRotationGraph d y (axis i) (P.firstDerivativeCoordinateCoarseL b) (S b i y) ∧
          ‖P.firstDerivativeCoordinateCoarseL b y‖ ≤ C*ε/beta d.γ d.radius y ∧
          ‖S b i y‖ ≤ C*ε ∧
          ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
            CoarseCovariantRotationGraph d y (axis j) (S b i) T ∧ ‖T‖ ≤ C*ε*beta d.γ d.radius y := by
  classical
  obtain ⟨CM,hCM,hModel⟩ := uniform_principal_model_coordinate_coarse_two_jets
    hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨ηC,CC,hηC,hηC1,hCC,hCorr⟩ := uniform_principal_first_correction_coordinate_coarse_two_jets
    hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hError⟩ := uniform_physical_first_error_coordinate_coarse_two_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let C := CM+CC+CE
  have hThree {V : Type} [SeminormedAddCommGroup V] (u v w : V) {a b c : ℝ}
      (hu : ‖u‖ ≤ a) (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ c) : ‖u+v+w‖ ≤ a+b+c :=
    (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hu hv)) hw)
  refine ⟨min ηC ηE,C,lt_min hηC hηE,(min_le_left _ _).trans hηC1,
    add_nonneg (add_nonneg hCM hCC) hCE,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_left _ _).trans hηC1)
  obtain ⟨SC,hSC⟩ := hCorr floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd
  obtain ⟨SE,hSE⟩ := hError floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P
  let S := fun (b i : I) (x : X) => principalModelCoordinateFirstCoarseJet d b i x+SC b i x+SE b i x
  have hK0 := zero_lt_one.trans_le hK
  have hMS (b : I) := (hd.principalModelCoordinateCoarse_smooth hY hΩ hK0 b 0).1
  have hCS (b : I) := hd.principalFirstCorrectionCoordinateCoarse_smooth hY hΩ hK0 b
  have hES (b : I) := P.firstErrorCoordinateCoarse_smooth hd hY hΩ hSub hK0 b
  have hMDS (b i : I) := (hd.principalModelCoordinateCoarse_smooth hY hΩ hK0 b i).2
  have hSS (b i : I) : ContDiffOn ℝ ∞ (S b i) Y :=
    (((hMDS b i).add (hSC b i).1).add (hSE b i).1)
  refine ⟨S,?_⟩
  intro b i
  refine ⟨P.firstDerivativeCoordinateCoarse_smooth hd hY hΩ hSub hK0 b,hSS b i,?_⟩
  intro y hy
  let β := beta d.γ d.radius y
  let r := d.radius y
  have hβ1 : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ : 0 < β := zero_lt_one.trans_le hβ1
  have hr : 0 ≤ r := (hd.2.2.2.2.1.2 y hy).1.le
  have hrβ2 : r*β^2 ≤ ε := (hd.2.2.2.2.2 y hy).2
  have hrβ : r*β ≤ ε :=
    (mul_le_mul_of_nonneg_left (by nlinarith only [hβ1] : β ≤ β^2) hr).trans hrβ2
  have hrSmall : r ≤ ε/β := (le_div_iff₀ hβ).mpr hrβ
  have hM := hModel floor hf ε hε hε1 d hd b i i y hy
  have hC := (hSC b i).2 y hy
  have hE := (hSE b i).2 y hy
  have hFirstGraph : CoarseCovariantRotationGraph d y (axis i)
      (P.firstDerivativeCoordinateCoarseL b) (S b i y) :=
    ((hM.1.add hC.1 (((hMS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hCS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))).add hE.1
      ((((hMS b).add (hCS b)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hES b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
  have hC0 : ‖principalFirstCorrectionCoordinateCoarseL d b y‖ ≤ CC*ε/β := hC.2.1.trans (by
    change CC*ε/β^2 ≤ CC*ε/β
    gcongr
    nlinarith only [hβ1])
  have hE0 : ‖principalFirstErrorCoordinateCoarseL d P.adjoint P.center b y‖ ≤ CE*ε/β := hE.2.1.trans (by
    exact (mul_le_mul_of_nonneg_left hrSmall hCE).trans_eq (by ring))
  have hC1 : ‖SC b i y‖ ≤ CC*ε := hC.2.2.1.trans (div_le_self (mul_nonneg hCC hε) hβ1)
  have hE1 : ‖SE b i y‖ ≤ CE*ε := hE.2.2.1.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrβ hCE)
  refine ⟨hFirstGraph,?_,?_,?_⟩
  · exact (hThree _ _ _ hM.2.2.1 hC0 hE0).trans_eq (by dsimp only [C];ring)
  · exact (hThree _ _ _ hM.2.2.2.1 hC1 hE1).trans_eq (by dsimp only [C];ring)
  · intro j
    obtain ⟨TC,hTC,hTCN⟩ := hC.2.2.2 j
    obtain ⟨TE,hTE,hTEN⟩ := hE.2.2.2 j
    let TM := principalModelCoordinateSecondCoarseJet d b i j y
    have hMJ := hModel floor hf ε hε hε1 d hd b i j y hy
    refine ⟨TM+TC+TE,?_,?_⟩
    · exact ((hMJ.2.1.add hTC
        (((hMDS b i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hSC b i).1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))).add hTE
        ((((hMDS b i).add (hSC b i).1).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hSE b i).1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
    · have hTCGrow : ‖TC‖ ≤ CC*ε*β := hTCN.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ1 (mul_nonneg hCC hε))
      have hTEGrow : ‖TE‖ ≤ CE*ε*β := hTEN.trans (by
        calc
          CE*r*β^2 = CE*(r*β^2) := by ring
          _ ≤ CE*ε := mul_le_mul_of_nonneg_left hrβ2 hCE
          _ ≤ CE*ε*β := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ1 (mul_nonneg hCE hε))
      exact (hThree _ _ _ hMJ.2.2.2.2 hTCGrow hTEGrow).trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres
