import Proof.ParallelScalarFirstRaisingHalfTwoJets
import Proof.ParallelScalarFirstHalfProductNorm
import Proof.UniformPrincipalModelStrongHalf

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def principalModelCoordinateSecondHalfJet (d : Data) (b i j : I) (x : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  fderiv ℝ (fun y => fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i)) x (axis j) •
      degreeHalfL+
    ∑ a : I,((principalModelRaisingCoordinateWeight d a b x • framedRaisingSecondHalfJet d i j a x+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis j) • framedRaisingFirstHalfJet d i a x)+
      (fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i) • framedRaisingFirstHalfJet d j a x+
        fderiv ℝ (fun y => fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i)) x (axis j) •
          framedRaisingHalfL d x (axis a)))

lemma principalModelCoordinateSecondHalfJet_coarse (d : Data) (b i j : I) (x : X) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (principalModelCoordinateSecondCoarseJet d b i j x)=
      (principalModelCoordinateSecondHalfJet d b i j x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hD := DFunLike.congr_fun degreeHalfL_coarse u
  have hR (a : I) := DFunLike.congr_fun (framedRaisingHalfL_coarse d x (axis a)) u
  have h1 (a k : I) := DFunLike.congr_fun (framedRaisingFirstHalfJet_coarse d k a x) u
  have h2 (a : I) := DFunLike.congr_fun (framedRaisingSecondHalfJet_coarse d i j a x) u
  simp only [ContinuousLinearMap.comp_apply] at hD hR h1 h2
  simp only [principalModelCoordinateSecondCoarseJet,principalModelCoordinateSecondHalfJet,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.add_apply,_root_.smul_apply,
    map_sum,map_add,map_smul,hD,hR,h1,h2]

lemma principalModelCoordinateFirstHalfJet_smooth {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (b i : I) :
    ContDiffOn ℝ ∞ (principalModelCoordinateFirstHalfJet d b i) Y := by
  have hD := hd.contDiffOn_principalModelDegreeCoordinateWeight hY hK b
  have hDD := contDiffOn_coordDeriv hY hD i
  have hR (a : I) := hd.contDiffOn_principalModelRaisingCoordinateWeight hK a b
  have hRD (a : I) := contDiffOn_coordDeriv hY (hR a) i
  have hF (a : I) := (hd.framedRaisingHalf_smooth (axis a)).1
  have hS (a : I) := framedRaisingFirstHalfJet_smooth hΩ hd hK i a
  exact (hDD.smul contDiffOn_const).add (ContDiffOn.sum (fun a _ =>
    ((hR a).smul (hS a)).add ((hRD a).smul (hF a))))

/-- The baseline scalar product-rule bounds are applied to genuine strong
half raising jets. The first/second scales are epsilon and epsilon beta. -/
theorem uniform_principal_model_coordinate_strong_half_two_jet_bounds {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b i j : I,∀ y ∈ Y,
        ‖principalModelCoordinateFirstHalfJet d b i y‖ ≤ C*ε ∧
        ‖principalModelCoordinateSecondHalfJet d b i j y‖ ≤ C*ε*beta d.γ d.radius y := by
  obtain ⟨Q0,hQ0,hRaising⟩ := uniform_framed_raising_strong_half_two_jets hY hΩ hm K ρ c₀ M Cj hK
  let BD := principalModelDegreeCoordinateTwoJetBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) (Cj 3)
  let B := BD+2
  let Q := Q0+2
  let C := 16*B*Q
  have hBD : 0 ≤ BD := principalModelDegreeCoordinateTwoJetBudget_nonneg _ _ _ _ _ (zero_le_one.trans hK)
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  have hBDB : BD ≤ B := by exact le_add_of_nonneg_right (by norm_num)
  have h2B : 2 ≤ B := by dsimp only [B];linarith only [hBD]
  have hQ0Q : Q0 ≤ Q := le_add_of_nonneg_right (by norm_num)
  have h2Q : 2 ≤ Q := by dsimp only [Q];linarith only [hQ0]
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hε1 d hd b i j y hy
  let β := beta d.γ d.radius y
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hBε : 0 ≤ B*ε := mul_nonneg hB hε
  have hBεGrow : B*ε ≤ B*ε*β := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ hBε
  have hD (k l : I) := hd.principalModelDegreeCoordinateWeight_two_jet_bounds hY hm hK hf hε hε1 hy b k l
  have hD0 : |principalModelDegreeCoordinateWeight d b y| ≤ B*ε/β :=
    (hD i j).2.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBDB hε) hβ0)
  have hD1 (k : I) : |fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis k)| ≤ B*ε :=
    (hD k k).2.2.1.trans (mul_le_mul_of_nonneg_right hBDB hε)
  have hD2 : |fderiv ℝ (fun x => fderiv ℝ (principalModelDegreeCoordinateWeight d b) x (axis i)) y (axis j)| ≤
      B*ε*β := (hD i j).2.2.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBDB hε) hβ0)
  have hDegree := small_two_jet_product_bounds degreeHalfL 0 0 0
    (principalModelDegreeCoordinateWeight d b y)
    (fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i))
    (fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis j))
    (fderiv ℝ (fun x => fderiv ℝ (principalModelDegreeCoordinateWeight d b) x (axis i)) y (axis j))
    B Q ε β hB hε hβ hD0 (hD1 i) (hD1 j) hD2
    ((norm_sphereSobolevShiftedDegreeL_le_two _).trans h2Q)
    (by simpa only [norm_zero] using hQ) (by simpa only [norm_zero] using hQ)
    (by simpa only [norm_zero] using hQ)
  simp only [smul_zero,zero_add,add_zero] at hDegree
  have hRaise (a : I) :
      ‖principalModelRaisingCoordinateWeight d a b y • framedRaisingHalfL d y (axis a)‖ ≤ B*Q*ε/β ∧
      ‖principalModelRaisingCoordinateWeight d a b y • framedRaisingFirstHalfJet d i a y+
        fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) •
          framedRaisingHalfL d y (axis a)‖ ≤ 2*B*Q*ε ∧
      ‖(principalModelRaisingCoordinateWeight d a b y • framedRaisingSecondHalfJet d i j a y+
        fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis j) • framedRaisingFirstHalfJet d i a y)+
        (fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • framedRaisingFirstHalfJet d j a y+
          fderiv ℝ (fun x => fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i)) y (axis j) •
            framedRaisingHalfL d y (axis a))‖ ≤ 4*B*Q*ε*β := by
    have hw (k l : I) := hd.principalModelRaisingCoordinateWeight_two_jet_bounds hY hK hf hε hε1 hy a b k l
    have hN := hRaising floor ε d hd y hy i j a
    have hNj := hRaising floor ε d hd y hy j j a
    exact small_two_jet_product_bounds
      (framedRaisingHalfL d y (axis a)) (framedRaisingFirstHalfJet d i a y)
      (framedRaisingFirstHalfJet d j a y) (framedRaisingSecondHalfJet d i j a y)
      (principalModelRaisingCoordinateWeight d a b y)
      (fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i))
      (fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis j))
      (fderiv ℝ (fun x => fderiv ℝ (principalModelRaisingCoordinateWeight d a b) x (axis i)) y (axis j))
      B Q ε β hB hε hβ
      ((hw i j).1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2B hε) hβ0))
      ((hw i j).2.1.trans (mul_le_mul_of_nonneg_right h2B hε))
      ((hw j i).2.1.trans (mul_le_mul_of_nonneg_right h2B hε))
      ((hw i j).2.2.trans ((mul_le_mul_of_nonneg_right h2B hε).trans hBεGrow))
      (hN.1.trans hQ0Q) (hN.2.1.trans hQ0Q) (hNj.2.1.trans hQ0Q) (hN.2.2.trans hQ0Q)
  have hSum (F : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (A : ℝ)
      (hF : ∀ a,‖F a‖ ≤ A) : ‖∑ a : I,F a‖ ≤ 3*A := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun a _ => hF a)).trans_eq
      (by simp only [Fin.sum_univ_three];ring))
  constructor
  · have hh : ‖principalModelCoordinateFirstHalfJet d b i y‖ ≤ 2*B*Q*ε+3*(2*B*Q*ε) :=
      (norm_add_le _ _).trans (add_le_add hDegree.2.1 (hSum _ _ (fun a => (hRaise a).2.1)))
    exact hh.trans (by
      calc
        _ = 8*(B*Q*ε) := by ring
        _ ≤ 16*(B*Q*ε) := mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (mul_nonneg hB hQ) hε)
        _ = C*ε := by dsimp only [C];ring)
  · have hh : ‖principalModelCoordinateSecondHalfJet d b i j y‖ ≤ 4*B*Q*ε*β+3*(4*B*Q*ε*β) :=
      (norm_add_le _ _).trans (add_le_add hDegree.2.2 (hSum _ _ (fun a => (hRaise a).2.2)))
    exact hh.trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres.ParallelEnergy
