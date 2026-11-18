import Proof.ParallelScalarFirstModelHalfTwoJets
import Proof.ParallelScalarFirstNativeCoordinatePacket
import Proof.ParallelScalarFirstForwardPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact owned correction producer consumed by the complete-coefficient
assembly; it is not an added hypothesis of the frozen proposition. -/
def CorrectionStrongHalfTwoJetBound
    (Y Ω : Set X) {m : ℕ} (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) : Prop :=
  ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d →
    ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
    ∃ L : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    ∀ b i : I,ContDiffOn ℝ ∞ (S b i) Y ∧ ContDiffOn ℝ ∞ (L b i) Y ∧ ∀ y ∈ Y,
      CoarseCovariantRotationGraph d y (axis i) (principalFirstCorrectionCoordinateCoarseL d b) (S b i y) ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b i y)=
        (L b i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      ‖L b i y‖ ≤ CE*ε ∧
      ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        CoarseCovariantRotationGraph d y (axis j) (S b i) T ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
          N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖N‖ ≤ CE*ε*beta d.γ d.radius y

/-- Complete model, geometric correction, actual native remainder and
scalar connection drift are assembled through genuine first/second
coarse/half graphs. Every family precedes every test. -/
theorem uniform_effective_first_coarse_strong_half_two_jets_of_correction
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hCorrection : CorrectionStrongHalfTwoJetBound Y Ω K ρ c₀ M Cj) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,Nonempty (EffectiveFirstCoarseStrongHalfTwoJets P C ε) := by
  obtain ⟨CM,hCM,hModel⟩ := uniform_principal_model_coordinate_strong_half_two_jet_bounds
    hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨ηC,CC,hηC,hηC1,hCC,hCorr⟩ := hCorrection
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hError⟩ := uniform_first_error_coordinate_strong_half_two_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets hY hΩ (by omega) K ρ c₀ M Cj hK
  let C := CM+CC+CE+CW
  have hC : 0 ≤ C := by dsimp only [C];positivity
  refine ⟨min ηC ηE,C,lt_min hηC hηE,(min_le_left _ _).trans hηC1,hC,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_left _ _).trans hηC1)
  obtain ⟨SC,LC,hSC⟩ := hCorr floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd
  obtain ⟨SE,LE,hSE⟩ := hError floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P
  let w := scalarPrincipalConnectionWeight d
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let Ih := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let S := fun (b i : I) (x : X) => principalModelCoordinateFirstCoarseJet d b i x+SC b i x+SE b i x-
    coordDeriv i (w b) x • I10
  let L := fun (b i : I) (x : X) => principalModelCoordinateFirstHalfJet d b i x+LC b i x+LE b i x-
    coordDeriv i (w b) x • Ih
  have hW := hWeight floor hf ε hε hε1 d hd
  have hWS (b : I) : ContDiffOn ℝ ∞ (w b) Y := (hW b).1
  have hWDS (b i : I) : ContDiffOn ℝ ∞ (coordDeriv i (w b)) Y := contDiffOn_coordDeriv hY (hWS b) i
  have hMS (b i : I) := (hd.principalModelCoordinateCoarse_smooth hY hΩ (zero_lt_one.trans_le hK) b i).2
  have hML (b i : I) := principalModelCoordinateFirstHalfJet_smooth hY hΩ hd (zero_lt_one.trans_le hK) b i
  have hSS (b i : I) : ContDiffOn ℝ ∞ (S b i) Y :=
    (((hMS b i).add (hSC b i).1).add (hSE b i).1).sub ((hWDS b i).smul contDiffOn_const)
  have hLS (b i : I) : ContDiffOn ℝ ∞ (L b i) Y :=
    (((hML b i).add (hSC b i).2.1).add (hSE b i).2.1).sub ((hWDS b i).smul contDiffOn_const)
  have hModelS (b : I) := (hd.principalModelCoordinateCoarse_smooth hY hΩ (zero_lt_one.trans_le hK) b 0).1
  have hCorrS (b : I) := hd.principalFirstCorrectionCoordinateCoarse_smooth hY hΩ (zero_lt_one.trans_le hK) b
  have hErrorS (b : I) := P.firstErrorCoordinateCoarse_smooth hd hY hΩ hSub (zero_lt_one.trans_le hK) b
  refine ⟨⟨S,L,hSS,hLS,?_,?_,?_,?_⟩⟩
  · intro b i y hy
    have hM := (hd.principalModelCoordinate_coarse_covariant_graphs hY hΩ (zero_lt_one.trans_le hK) hy b i i).1
    have hCC := ((hSC b i).2.2 y hy).1
    have hEC := ((hSE b i).2.2 y hy).1
    have hScalar := coarse_covariant_scalar_inclusion_graph d (w b) y (axis i)
      (((hWS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    have hFull := (hM.add hCC (((hModelS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hCorrS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))).add hEC
        ((((hModelS b).add (hCorrS b)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hErrorS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    exact hFull.sub hScalar
      (((P.firstDerivativeCoordinateCoarse_smooth hd hY hΩ hSub (zero_lt_one.trans_le hK) b).contDiffAt
        (hY.mem_nhds hy)).differentiableAt (by simp))
      ((((hWS b).smul contDiffOn_const).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  · intro b i y hy
    apply ContinuousLinearMap.ext
    intro u
    have hM := DFunLike.congr_fun (principalModelCoordinateFirstHalfJet_coarse d b i y) u
    have hC' := DFunLike.congr_fun (((hSC b i).2.2 y hy).2.1) u
    have hE' := DFunLike.congr_fun (((hSE b i).2.2 y hy).2.1) u
    simp only [ContinuousLinearMap.comp_apply] at hM hC' hE'
    simp only [S,L,I10,Ih,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,_root_.smul_apply,
      map_add,map_sub,map_smul,hM,hC',hE',sphereSobolevInclusionL_trans_apply]
  · intro b i y hy
    have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hRad := radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε
      (hd.2.2.2.2.1.2 y hy).1.le hf (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2
    have hrβ : d.radius y*beta d.γ d.radius y ≤ ε := hRad.2.1.trans (div_le_self hε hf)
    have hEN : ‖LE b i y‖ ≤ CE*ε := (((hSE b i).2.2 y hy).2.2.1).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrβ hCE)
    have hWN : ‖coordDeriv i (w b) y • Ih‖ ≤ CW*ε := by
      rw [norm_smul,Real.norm_eq_abs]
      exact ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (abs_nonneg _)).trans_eq
        (mul_one _)).trans (((hW b).2 y hy i i).2.1.trans (div_le_self (mul_nonneg hCW hε) hβ))
    have hMN := (hModel floor hf ε hε hε1 d hd b i i y hy).1
    have hh := (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hMN
        (((hSC b i).2.2 y hy).2.2.1))) hEN)) hWN)
    exact hh.trans_eq (by dsimp only [C];ring)
  · intro b i j y hy
    obtain ⟨TC,NC,hTC,hNC,hNCN⟩ := ((hSC b i).2.2 y hy).2.2.2 j
    obtain ⟨TE,NE,hTE,hNE,hNEN⟩ := ((hSE b i).2.2 y hy).2.2.2 j
    let TM := principalModelCoordinateSecondCoarseJet d b i j y
    let NM := principalModelCoordinateSecondHalfJet d b i j y
    let ddw := coordDeriv j (coordDeriv i (w b)) y
    let T := TM+TC+TE-ddw • I10
    let N := NM+NC+NE-ddw • Ih
    refine ⟨T,N,?_,?_,?_⟩
    · have hM := (hd.principalModelCoordinate_coarse_covariant_graphs hY hΩ (zero_lt_one.trans_le hK) hy b i j).2
      have hScalar := coarse_covariant_scalar_inclusion_graph d (coordDeriv i (w b)) y (axis j)
        (((hWDS b i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      exact ((hM.add hTC (((hMS b i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        ((((hSC b i).1).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))).add hTE
          ((((hMS b i).add (hSC b i).1).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
          ((((hSE b i).1).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))).sub hScalar
            (((((hMS b i).add (hSC b i).1).add (hSE b i).1).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
            ((((hWDS b i).smul contDiffOn_const).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    · apply ContinuousLinearMap.ext
      intro u
      have hM := DFunLike.congr_fun (principalModelCoordinateSecondHalfJet_coarse d b i j y) u
      have hC' := DFunLike.congr_fun hNC u
      have hE' := DFunLike.congr_fun hNE u
      simp only [ContinuousLinearMap.comp_apply] at hM hC' hE'
      simp only [T,N,TM,NM,I10,Ih,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,_root_.smul_apply,
        map_add,map_sub,map_smul,hM,hC',hE',sphereSobolevInclusionL_trans_apply]
    · have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
      have hβ0 : 0 ≤ beta d.γ d.radius y := zero_le_one.trans hβ
      have hEN : ‖NE‖ ≤ CE*ε*beta d.γ d.radius y := by
        calc
          _ ≤ CE*d.radius y*(beta d.γ d.radius y)^2 := hNEN
          _ ≤ CE*ε := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hd.2.2.2.2.2 y hy).2 hCE
          _ ≤ CE*ε*beta d.γ d.radius y := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ (mul_nonneg hCE hε)
      have hWN : ‖ddw • Ih‖ ≤ CW*ε*beta d.γ d.radius y := by
        rw [norm_smul,Real.norm_eq_abs]
        have h0 : |ddw| ≤ CW*ε := ((hW b).2 y hy i j).2.2
        exact ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (abs_nonneg _)).trans_eq
          (mul_one _)).trans (h0.trans
            (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ (mul_nonneg hCW hε)))
      have hMN := (hModel floor hf ε hε hε1 d hd b i j y hy).2
      have hh := (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hMN hNCN)) hEN)) hWN)
      exact hh.trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres.ParallelEnergy
