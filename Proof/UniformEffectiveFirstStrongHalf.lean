import Proof.UniformPrincipalCorrectionStrongHalf
import Proof.UniformPhysicalFirstErrorStrongHalf
import Proof.UniformPrincipalModelStrongHalf
import Proof.UniformPhysicalFirstCovariantCoordinateTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The COMPLETE effective first coefficient of the actual ordered
covariant residual has genuine strong half-domain covariant jets. Model,
bounded geometric correction, native error and scalar connection drift
are assembled with the original uniform epsilon bound. -/
theorem uniform_effective_first_covariant_strong_half
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
            (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b i y)=
              L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧ ‖L‖ ≤ CE*ε := by
  obtain ⟨CM,hCM,hModel⟩ := uniform_principal_model_coordinate_strong_half hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨ηC,CC,hηC,hηC1,hCC,hCorr⟩ :=
    uniform_principal_first_correction_coordinate_strong_half hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hError⟩ :=
    uniform_physical_first_error_coordinate_strong_half hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets hY hΩ (by omega) K ρ c₀ M Cj hK
  let C := CM+CC+CE+CW
  have hC : 0 ≤ C := by dsimp only [C];positivity
  refine ⟨min ηC ηE,C,lt_min hηC hηE,(min_le_left _ _).trans hηC1,hC,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_left _ _).trans hηC1)
  obtain ⟨SC,hSC⟩ := hCorr floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd
  obtain ⟨SE,hSE⟩ := hError floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P
  let w := scalarPrincipalConnectionWeight d
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let Ih := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let S := fun (b i : I) (x : X) =>
    principalModelCoordinateFirstCoarseJet d b i x+SC b i x+SE b i x-coordDeriv i (w b) x • I10
  have hW := hWeight floor hf ε hε hε1 d hd
  have hWS (b : I) : ContDiffOn ℝ ∞ (w b) Y := (hW b).1
  have hWD (b i : I) : ContDiffOn ℝ ∞ (fun x => coordDeriv i (w b) x • I10) Y :=
    (contDiffOn_coordDeriv hY (hWS b) i).smul contDiffOn_const
  have hMS (b : I) := (hd.principalModelCoordinateCoarse_smooth hY hΩ (zero_lt_one.trans_le hK) b 0).1
  have hMD (b i : I) := (hd.principalModelCoordinateCoarse_smooth hY hΩ (zero_lt_one.trans_le hK) b i).2
  have hCS (b : I) := hd.principalFirstCorrectionCoordinateCoarse_smooth hY hΩ (zero_lt_one.trans_le hK) b
  have hES (b : I) := P.firstErrorCoordinateCoarse_smooth hd hY hΩ hSub (zero_lt_one.trans_le hK) b
  refine ⟨S,?_⟩
  intro b i
  have hFullS := P.firstDerivativeCoordinateCoarse_smooth hd hY hΩ hSub (zero_lt_one.trans_le hK) b
  have hScalarS : ContDiffOn ℝ ∞ (fun x => w b x • I10) Y := (hWS b).smul contDiffOn_const
  refine ⟨(((hMD b i).add (hSC b i).1).add (hSE b i).1).sub (hWD b i),?_⟩
  intro y hy
  obtain ⟨hMC,hMN⟩ := hModel floor hf ε hε hε1 d hd b i y hy
  obtain ⟨hCC,LC,hLC,hLCN⟩ := (hSC b i).2 y hy
  obtain ⟨hEC,LE,hLE,hLEN,hLEE⟩ := (hSE b i).2 y hy
  have hSCalar := coarse_covariant_scalar_inclusion_graph d (w b) y (axis i)
    (((hWS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hFullGraph : CoarseCovariantRotationGraph d y (axis i)
      (P.firstDerivativeCoordinateCoarseL b)
      (principalModelCoordinateFirstCoarseJet d b i y+SC b i y+SE b i y) :=
    (hMC.add hCC (((hMS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((hCS b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))).add hEC
        ((((hMS b).add (hCS b)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        (((hES b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hGraph : CoarseCovariantRotationGraph d y (axis i) (P.firstCovariantCoordinateCoarseL b) (S b i y) :=
    hFullGraph.sub hSCalar ((hFullS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      ((hScalarS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  let L := principalModelCoordinateFirstHalfJet d b i y+LC+LE-coordDeriv i (w b) y • Ih
  have hCompat : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b i y)=
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro u
    have hM := DFunLike.congr_fun (principalModelCoordinateFirstHalfJet_coarse d b i y) u
    have hC' := DFunLike.congr_fun hLC u
    have hE' := DFunLike.congr_fun hLE u
    simp only [ContinuousLinearMap.comp_apply] at hM hC' hE'
    simp only [S,L,I10,Ih,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,_root_.smul_apply,
      map_add,map_sub,map_smul,hM,hC',hE',sphereSobolevInclusionL_trans_apply]
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hWBound : ‖coordDeriv i (w b) y • Ih‖ ≤ CW*ε := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ |coordDeriv i (w b) y| *1 := mul_le_mul_of_nonneg_left
        (norm_sphereSobolevInclusionL_le _ _ _) (abs_nonneg _)
      _ = |coordDeriv i (w b) y| := mul_one _
      _ ≤ CW*ε/beta d.γ d.radius y := ((hW b).2 y hy i i).2.1
      _ ≤ CW*ε := div_le_self (mul_nonneg hCW hε) hβ
  have hNorm : ‖L‖ ≤ C*ε := by
    have hh := (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add hMN hLCN)) hLEE)) hWBound)
    exact hh.trans_eq (by dsimp only [C];ring)
  exact ⟨hGraph,L,hCompat,hNorm⟩

end ShrinkingSpheres
