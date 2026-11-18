import Proof.FramedRaisingStrongHalfJet
import Proof.UniformPrincipalModelCoordinateCoarseTwoJets

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

def principalModelCoordinateFirstHalfJet (d : Data) (b i : I) (y : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i) • degreeHalfL+
    ∑ a : I,(principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstHalfJet d i a y+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingHalfL d y (axis a))

lemma principalModelCoordinateFirstHalfJet_coarse (d : Data) (b i : I) (y : X) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (principalModelCoordinateFirstCoarseJet d b i y)=
      (principalModelCoordinateFirstHalfJet d b i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hD := DFunLike.congr_fun degreeHalfL_coarse u
  have hR (a : I) := DFunLike.congr_fun (framedRaisingHalfL_coarse d y (axis a)) u
  have hJ (a : I) := DFunLike.congr_fun (framedRaisingFirstHalfJet_coarse d i a y) u
  simp only [ContinuousLinearMap.comp_apply] at hD hR hJ
  simp only [principalModelCoordinateFirstCoarseJet,principalModelCoordinateFirstHalfJet,
    ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sum_apply,_root_.smul_apply,
    map_add,map_sum,map_smul,hD,hR,hJ]

/-- The complete degree-plus-raising model covariant jet has a genuine
strong half-domain extension with the original uniform epsilon bound. -/
theorem uniform_principal_model_coordinate_strong_half {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 1 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ CE : ℝ,0 ≤ CE ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b i : I,∀ y ∈ Y,
        CoarseCovariantRotationGraph d y (axis i) (principalModelCoordinateCoarseL d b)
          (principalModelCoordinateFirstCoarseJet d b i y) ∧
        ‖principalModelCoordinateFirstHalfJet d b i y‖ ≤ CE*ε := by
  obtain ⟨Q0,hQ0,hRaising⟩ := uniform_framed_raising_strong_half_one_jet hY hΩ hm K ρ c₀ M Cj hK
  let BD := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
  let B := BD+2
  let Q := Q0+2
  let CE := 7*B*Q
  have hBD : 0 ≤ BD := principalModelDegreeCoordinateBudget_nonneg _ _ _ (zero_le_one.trans hK)
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  have hBDB : BD ≤ B := le_add_of_nonneg_right (by norm_num)
  have h2B : 2 ≤ B := by dsimp only [B];linarith only [hBD]
  have hQ0Q : Q0 ≤ Q := le_add_of_nonneg_right (by norm_num)
  have h2Q : 2 ≤ Q := by dsimp only [Q];linarith only [hQ0]
  refine ⟨CE,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hε1 d hd b i y hy
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hD := hd.principalModelDegreeCoordinateWeight_bounds hY hm hK hf hε hε1 hy b i
  have hDegree : ‖fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i) • degreeHalfL‖ ≤ B*Q*ε := by
    rw [norm_smul,Real.norm_eq_abs]
    have hdf : |fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i)| ≤ B*ε :=
      hD.2.trans (mul_le_mul_of_nonneg_right hBDB hε)
    have hDN : ‖degreeHalfL‖ ≤ Q := (norm_sphereSobolevShiftedDegreeL_le_two _).trans h2Q
    exact (mul_le_mul hdf hDN (norm_nonneg _) (mul_nonneg hB hε)).trans_eq (by ring)
  have hRaise (a : I) : ‖principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstHalfJet d i a y+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingHalfL d y (axis a)‖ ≤ 2*B*Q*ε := by
    have hw := hd.principalModelRaisingCoordinateWeight_bounds hY hK hf hε hε1 hy a b i
    have hN := hRaising floor ε d hd y hy i a
    have h0 : |principalModelRaisingCoordinateWeight d a b y| ≤ B*ε :=
      hw.1.trans ((div_le_self (mul_nonneg (by norm_num) hε) hβ).trans (mul_le_mul_of_nonneg_right h2B hε))
    have h1 : |fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i)| ≤ B*ε :=
      hw.2.trans (mul_le_mul_of_nonneg_right h2B hε)
    have hA : ‖principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstHalfJet d i a y‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul h0 (hN.2.trans hQ0Q) (norm_nonneg _) (mul_nonneg hB hε)
    have hB' : ‖fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingHalfL d y (axis a)‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul h1 (hN.1.trans hQ0Q) (norm_nonneg _) (mul_nonneg hB hε)
    exact ((norm_add_le _ _).trans (add_le_add hA hB')).trans_eq (by ring)
  have hSum : ‖∑ a : I,(principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstHalfJet d i a y+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingHalfL d y (axis a))‖ ≤ 3*(2*B*Q*ε) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun a _ => hRaise a)).trans_eq (by simp only [Fin.sum_univ_three];ring))
  refine ⟨(hd.principalModelCoordinate_coarse_covariant_graphs hY hΩ (zero_lt_one.trans_le hK) hy b i i).1,?_⟩
  exact ((norm_add_le _ _).trans (add_le_add hDegree hSum)).trans_eq (by dsimp only [CE];ring)

end ShrinkingSpheres
