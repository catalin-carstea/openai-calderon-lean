import Proof.UniformFlatRaisingConstantAdjointHigher
import Proof.UniformPrincipalModelStrongHalf
import Proof.UniformPrincipalModelCovariantHigher

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

/-- A fixed physical-direction raising transpose, with the genuine HIGH graph. -/
def modelAdjointRaisingHigherL (d : Data)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y : X) (b : I) :=
  ∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis b) • AR j

lemma modelAdjointRaisingHigherL_graph (d : Data)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hAR : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AR j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (y : X) (b : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (modelAdjointRaisingHigherL d AR y b)=
      (framedRaisingHalfL d y (axis b)).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  finite_real_adjoint_balanced_combination _ _ _ _ hAR _

def modelAdjointRaisingFirstHigherJet (d : Data)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y : X) (i b : I) :=
  ∑ a : I,christoffel d.γ y a i b • modelAdjointRaisingHigherL d AR y a

lemma modelAdjointRaisingFirstHigherJet_graph (d : Data)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hAR : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AR j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (y : X) (i b : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (modelAdjointRaisingFirstHigherJet d AR y i b)=
      (framedRaisingFirstHalfJet d i b y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  finite_real_adjoint_balanced_combination _ _ _ _
    (fun a => modelAdjointRaisingHigherL_graph d AR hAR y a) _

def modelCoordinateFirstAdjointHigherJet (d : Data)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (b i : I) (y : X) :=
  fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i) • degreeHigherL+
    ∑ a : I,(principalModelRaisingCoordinateWeight d a b y • modelAdjointRaisingFirstHigherJet d AR y i a+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • modelAdjointRaisingHigherL d AR y a)

lemma modelCoordinateFirstAdjointHigherJet_graph (d : Data)
    (AR : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hAR : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AR j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (b i : I) (y : X) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (modelCoordinateFirstAdjointHigherJet d AR b i y)=
      (principalModelCoordinateFirstHalfJet d b i y).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hD := DFunLike.congr_fun degreeHigherL_adjoint_pair u
  have hR (a : I) := DFunLike.congr_fun (modelAdjointRaisingHigherL_graph d AR hAR y a) u
  have hJ (a : I) := DFunLike.congr_fun (modelAdjointRaisingFirstHigherJet_graph d AR hAR y i a) u
  simp only [ContinuousLinearMap.comp_apply] at hD hR hJ
  simp only [modelCoordinateFirstAdjointHigherJet,principalModelCoordinateFirstHalfJet,map_add,map_sum,map_smul,
    ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sum_apply,_root_.smul_apply,map_add,map_sum,map_smul,hD,hR,hJ]

/-- The SAME complete model first covariant jet has a genuine true-adjoint
HIGH endpoint with the original uniform epsilon norm. -/
theorem uniform_model_coordinate_first_jet_adjoint_higher
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ b i : I,∀ y ∈ Y,∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
          (principalModelCoordinateFirstHalfJet d b i y).adjoint.comp
            (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧ ‖H‖ ≤ CE*ε := by
  obtain ⟨η,CR,hη,hη1,hCR,hAdj⟩ := uniform_flat_raising_constant_adjoint_higher
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let G := 9*K*|M ⟨1,by omega⟩|
  let Q0 := 3*K*CR+9*G*K*CR
  let Q := Q0+2
  let BD := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
  let B := BD+2
  let CE := 7*B*Q
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hQ0 : 0 ≤ Q0 := by dsimp only [Q0];positivity
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  have hBD : 0 ≤ BD := principalModelDegreeCoordinateBudget_nonneg _ _ _ (zero_le_one.trans hK)
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have h2B : 2 ≤ B := by dsimp only [B];linarith
  have h2Q : 2 ≤ Q := by dsimp only [Q];linarith
  have hBDB : BD ≤ B := le_add_of_nonneg_right (by norm_num)
  refine ⟨η,CE,hη,hη1,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P b i y hy
  obtain ⟨AR,hAR⟩ := hAdj floor hf ε hε hSmall d hd CF CT P
  have hARg (j : I) := (hAR y hy j).1
  have hARN (j : I) := (hAR y hy j).2
  have hg : Elliptic Y K d.γ :=
    ⟨fun a c => (hd.1.1.1 a c).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hc (a j : I) : |frameCoordinateLinear d.γ d.frame y j (axis a)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact hg.frame_coordinate_abs_bound hK d.frame hy hFrame a j
  have hR (a : I) : ‖modelAdjointRaisingHigherL d AR y a‖ ≤ 3*K*CR :=
    norm_weighted_sum_three_le _ _ K CR (zero_le_one.trans hK) (hc a) hARN
  have hGamma (a c : I) : |christoffel d.γ y a i c| ≤ G :=
    hd.1.1.christoffel_entry_bound (zero_lt_one.trans_le hK) (hSub hy)
      |M ⟨1,by omega⟩| (abs_nonneg _)
      (fun j k => (hd.1.reference_fderiv_bound (by omega) (hSub hy) j k).trans (le_abs_self _)) a i c
  have hJ (a : I) : ‖modelAdjointRaisingFirstHigherJet d AR y i a‖ ≤ 9*G*K*CR :=
    (norm_weighted_sum_three_le _ _ G (3*K*CR) hG (fun c => hGamma c a) hR).trans_eq (by ring)
  have hRQ (a : I) : ‖modelAdjointRaisingHigherL d AR y a‖ ≤ Q :=
    (hR a).trans (by
      dsimp only [Q,Q0]
      have hn : 0 ≤ 9*G*K*CR := by positivity
      linarith)
  have hJQ (a : I) : ‖modelAdjointRaisingFirstHigherJet d AR y i a‖ ≤ Q :=
    (hJ a).trans (by
      dsimp only [Q,Q0]
      have hn : 0 ≤ 3*K*CR := by positivity
      linarith)
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hε1 := hSmall.trans hη1
  have hD := hd.principalModelDegreeCoordinateWeight_bounds hY (by omega) hK hf hε hε1 hy b i
  have hDegree : ‖fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i) • degreeHigherL‖ ≤ B*Q*ε := by
    rw [norm_smul,Real.norm_eq_abs]
    have hdf : |fderiv ℝ (principalModelDegreeCoordinateWeight d b) y (axis i)| ≤ B*ε :=
      hD.2.trans (mul_le_mul_of_nonneg_right hBDB hε)
    exact (mul_le_mul hdf ((norm_degreeHigherL_le_two).trans h2Q) (norm_nonneg _) (mul_nonneg hB hε)).trans_eq (by ring)
  have hOne (a : I) : ‖principalModelRaisingCoordinateWeight d a b y • modelAdjointRaisingFirstHigherJet d AR y i a+
      fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • modelAdjointRaisingHigherL d AR y a‖ ≤ 2*B*Q*ε := by
    have hw := hd.principalModelRaisingCoordinateWeight_bounds hY hK hf hε hε1 hy a b i
    have hw0 : |principalModelRaisingCoordinateWeight d a b y| ≤ B*ε :=
      hw.1.trans ((div_le_self (mul_nonneg (by norm_num) hε) hβ).trans (mul_le_mul_of_nonneg_right h2B hε))
    have hw1 : |fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i)| ≤ B*ε :=
      hw.2.trans (mul_le_mul_of_nonneg_right h2B hε)
    have hA : ‖principalModelRaisingCoordinateWeight d a b y • modelAdjointRaisingFirstHigherJet d AR y i a‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hw0 (hJQ a) (norm_nonneg _) (mul_nonneg hB hε)
    have hB' : ‖fderiv ℝ (principalModelRaisingCoordinateWeight d a b) y (axis i) • modelAdjointRaisingHigherL d AR y a‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hw1 (hRQ a) (norm_nonneg _) (mul_nonneg hB hε)
    exact ((norm_add_le _ _).trans (add_le_add hA hB')).trans_eq (by ring)
  refine ⟨modelCoordinateFirstAdjointHigherJet d AR b i y,modelCoordinateFirstAdjointHigherJet_graph d AR hARg b i y,?_⟩
  exact ((norm_add_le _ _).trans (add_le_add hDegree
    ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => hOne a))))).trans_eq
      (by simp only [Fin.sum_univ_three,CE];ring)

end ShrinkingSpheres.ParallelEnergy
