import Proof.UniformPrincipalModelCoordinateCoarseTwoJets
import Proof.FramedRaisingHalfCovariantData

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

def framedRaisingFirstHigherJet (d : Data) (i b : I) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ a : I,christoffel d.γ x a i b • framedRaisingHigherL d x (axis a)

lemma framedRaisingFirstHigherJet_coarse (d : Data) (i b : I) (x : X) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (framedRaisingFirstHigherJet d i b x)=
      (framedRaisingFirstCoarseJet d i b x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hR (a : I) := DFunLike.congr_fun (framedRaisingHigherL_coarse d x (axis a)) u
  simp only [ContinuousLinearMap.comp_apply] at hR
  simp only [framedRaisingFirstCoarseJet,framedRaisingFirstHigherJet,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul,hR]

theorem uniform_framed_raising_higher_one_jet {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 1 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ,0 ≤ Q ∧ ∀ floor ε : ℝ,∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i b : I,
        ‖framedRaisingHigherL d y (axis b)‖ ≤ Q ∧ ‖framedRaisingFirstHigherJet d i b y‖ ≤ Q := by
  let M1 := |M ⟨1,by omega⟩|
  let G := 9*K*M1
  let Q0 := framedRaisingHalfBudget K (M 0) (M ⟨1,by omega⟩)
  let Q := Q0+3*G*Q0
  have hK0 := zero_le_one.trans hK
  have hQ0 : 0 ≤ Q0 := framedRaisingHalfBudget_nonneg _ _ _ hK0
  have hG : 0 ≤ G := by dsimp only [G,M1];positivity
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  refine ⟨Q,hQ,?_⟩
  intro floor ε d hd y hy i b
  have hyΩ := hd.2.1.center_mem hy
  have hMetric (a c : I) : ‖fderiv ℝ (fun x => d.γ x a c) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound hm hyΩ a c).trans (le_abs_self _)
  have hGamma (a : I) : |christoffel d.γ y a i b| ≤ G :=
    hd.1.1.christoffel_entry_bound (zero_lt_one.trans_le hK) hyΩ M1 (abs_nonneg _) hMetric a i b
  have hRaise (a : I) : ‖framedRaisingHigherL d y (axis a)‖ ≤ Q0 :=
    ((hd.framedRaisingHalf_covariant_data hY hΩ hm hK a) y hy).2.1
  have hJet : ‖framedRaisingFirstHigherJet d i b y‖ ≤ 3*G*Q0 :=
    norm_weighted_sum_three_le _ _ _ _ hG hGamma hRaise
  refine ⟨(hRaise b).trans ?_,hJet.trans ?_⟩
  · exact le_add_of_nonneg_right (by positivity)
  · dsimp only [Q]
    linarith only [hQ0]


def principalModelCoordinateFirstHigherJet (d : Data) (b i : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i) • degreeHigherL+
    ∑ a : I,(principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstHigherJet d i a y+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingHigherL d y (axis a))

lemma principalModelCoordinateFirstHigherJet_coarse (d : Data) (b i : I) (y : X) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (principalModelCoordinateFirstHigherJet d b i y)=
      (principalModelCoordinateFirstCoarseJet d b i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hD := DFunLike.congr_fun degreeHigherL_coarse u
  have hR (a : I) := DFunLike.congr_fun (framedRaisingHigherL_coarse d y (axis a)) u
  have hJ (a : I) := DFunLike.congr_fun (framedRaisingFirstHigherJet_coarse d i a y) u
  simp only [ContinuousLinearMap.comp_apply] at hD hR hJ
  simp only [principalModelCoordinateFirstCoarseJet,principalModelCoordinateFirstHigherJet,
    ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sum_apply,_root_.smul_apply,
    map_add,map_sum,map_smul,hD,hR,hJ]

theorem uniform_principal_model_coordinate_covariant_higher {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 1 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ CE : ℝ,0 ≤ CE ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b i : I,∀ y ∈ Y,
        CoarseCovariantRotationGraph d y (axis i) (principalModelCoordinateCoarseL d b)
          (principalModelCoordinateFirstCoarseJet d b i y) ∧
        ‖principalModelCoordinateFirstHigherJet d b i y‖ ≤ CE*ε := by
  obtain ⟨Q0,hQ0,hRaising⟩ := uniform_framed_raising_higher_one_jet hY hΩ hm K ρ c₀ M Cj hK
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
  have hDegree : ‖fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i) • degreeHigherL‖ ≤ B*Q*ε := by
    rw [norm_smul,Real.norm_eq_abs]
    have hdf : |fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i)| ≤ B*ε :=
      hD.2.trans (mul_le_mul_of_nonneg_right hBDB hε)
    have hDN : ‖degreeHigherL‖ ≤ Q := (norm_sphereSobolevShiftedDegreeL_le_two _).trans h2Q
    exact (mul_le_mul hdf hDN (norm_nonneg _) (mul_nonneg hB hε)).trans_eq (by ring)
  have hRaise (a : I) : ‖principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstHigherJet d i a y+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingHigherL d y (axis a)‖ ≤ 2*B*Q*ε := by
    have hw := hd.principalModelRaisingCoordinateWeight_bounds hY hK hf hε hε1 hy a b i
    have hN := hRaising floor ε d hd y hy i a
    have h0 : |principalModelRaisingCoordinateWeight d a b y| ≤ B*ε :=
      hw.1.trans ((div_le_self (mul_nonneg (by norm_num) hε) hβ).trans (mul_le_mul_of_nonneg_right h2B hε))
    have h1 : |fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i)| ≤ B*ε :=
      hw.2.trans (mul_le_mul_of_nonneg_right h2B hε)
    have hA : ‖principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstHigherJet d i a y‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul h0 (hN.2.trans hQ0Q) (norm_nonneg _) (mul_nonneg hB hε)
    have hB' : ‖fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingHigherL d y (axis a)‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul h1 (hN.1.trans hQ0Q) (norm_nonneg _) (mul_nonneg hB hε)
    exact ((norm_add_le _ _).trans (add_le_add hA hB')).trans_eq (by ring)
  have hSum : ‖∑ a : I,(principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstHigherJet d i a y+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingHigherL d y (axis a))‖ ≤ 3*(2*B*Q*ε) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun a _ => hRaise a)).trans_eq (by simp only [Fin.sum_univ_three];ring))
  refine ⟨(hd.principalModelCoordinate_coarse_covariant_graphs hY hΩ (zero_lt_one.trans_le hK) hy b i i).1,?_⟩
  exact ((norm_add_le _ _).trans (add_le_add hDegree hSum)).trans_eq (by dsimp only [CE];ring)

end ShrinkingSpheres
