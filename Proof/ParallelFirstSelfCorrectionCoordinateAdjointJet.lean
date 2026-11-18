import Proof.ParallelFirstSelfCorrectionAdjointJet
import Proof.UniformPrincipalCorrectionStrongHalf
import Proof.PrincipalFirstCorrectionCoordinateWeights
import Proof.FrameAdjointEndpointCombination
import Proof.ParallelFirstSelfAdjointJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma half_covariant_higher_congr (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (A B : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (y a : X) (hAB : A y=B y) :
    halfOperatorCovariantDerivativeL d C A y a=halfOperatorCovariantDerivativeL d C B y a := by
  unfold halfOperatorCovariantDerivativeL
  rw [hAB]

def correctionCoordinateAdjointHigherL (d : Data) (b : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ a : I,principalFirstErrorCoordinateWeight d a b y • correctionAdjointHigherL d y (axis a)

lemma correctionCoordinateAdjointHigherL_graph (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (b : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (correctionCoordinateAdjointHigherL d b y)=
      (principalFirstCorrectionCoordinateHalfL d y b).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have h := finite_real_adjoint_balanced_combination
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (fun a => physicalFirstCorrectionHalfL d y (axis a))
    (fun a => correctionAdjointHigherL d y (axis a))
    (fun a => correctionAdjointHigherL_graph d y (axis a))
    (fun a => principalFirstErrorCoordinateWeight d a b y)
  exact h.trans (congrArg (fun L => L.adjoint.comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (principalFirstCorrectionCoordinateHalfL_eq d y hFrame b).symm)

/-- The complete weighted geometric-correction true-adjoint covariant jet
has the original epsilon HIGH bound for ANY already selected compatible
endpoint. The unrestricted frame derivatives cancel before the estimate. -/
theorem uniform_correction_coordinate_true_adjoint_covariant_higher
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) :
    ∃ CE : ℝ,0 ≤ CE ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b : I,
      ∀ AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ∀ y ∈ Y,
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH y)=
        (principalFirstCorrectionCoordinateHalfL d y b).adjoint.comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
      ∀ i : I,∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        halfOperatorCovariantDerivativeL d (fun x => (principalFirstCorrectionCoordinateHalfL d x b).adjoint) AH y (axis i)=
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H ∧ ‖H‖ ≤ CE*ε := by
  obtain ⟨QC,hQC,hDerivative⟩ := uniform_physical_correction_true_adjoint_covariant_higher
    hY hΩ hm K ρ c₀ M Cj hK
  let QB := 3*K*firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)
  let Q := QB+QC
  let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let CE := 6*B*Q
  have hQB : 0 ≤ QB := mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hK))
    (firstCorrectionGradeBound_nonneg _ _ _)
  have hQ : 0 ≤ Q := add_nonneg hQB hQC
  have hB : 0 ≤ B := principalFirstErrorCoordinateWeightBudget_nonneg _ _ (zero_le_one.trans hK) (abs_nonneg _)
  refine ⟨CE,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hε1 d hd b AH y hy hAH i
  let Lo := fun (a : I) (x : X) => physicalFirstCorrectionHalfL d x (axis a)
  let A0 := fun (a : I) (x : X) => correctionAdjointHigherL d x (axis a)
  let w := fun (a : I) (x : X) => principalFirstErrorCoordinateWeight d a b x
  let A := fun x => ∑ a : I,w a x • A0 a x
  let C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    fun x => ∑ a : I,w a x • (Lo a x).adjoint
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hKpos := zero_lt_one.trans_le hK
  have hWS (a : I) : ContDiffOn ℝ ∞ (w a) Y := hd.contDiffOn_principalFirstErrorCoordinateWeight hKpos a b
  have hLS (a : I) : ContDiffOn ℝ ∞ (Lo a) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hKpos (-(1/2:ℝ)) (axis a)).clm_comp contDiffOn_const
  have hAS (a : I) : ContDiffOn ℝ ∞ (fun x => (Lo a x).adjoint) Y := Adj.contDiff.comp_contDiffOn (hLS a)
  have hGraph (a : I) (x : X) := correctionAdjointHigherL_graph d x (axis a)
  have hLow (x : X) (hx : x ∈ Y) : principalFirstCorrectionCoordinateHalfL d x b=∑ a : I,w a x • Lo a x :=
    principalFirstCorrectionCoordinateHalfL_eq d x (hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)) b
  have hGerm : (fun x => (principalFirstCorrectionCoordinateHalfL d x b).adjoint) =ᶠ[𝓝 y] C := by
    filter_upwards [hY.mem_nhds hy] with x hx
    change Adj (principalFirstCorrectionCoordinateHalfL d x b)=∑ a : I,w a x • Adj (Lo a x)
    rw [hLow x hx,map_sum]
    simp only [map_smul]
  have hAGraph : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A y)=
      (principalFirstCorrectionCoordinateHalfL d y b).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    exact correctionCoordinateAdjointHigherL_graph d y
      (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)) b
  have hSame : AH y=A y := by
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    exact DFunLike.congr_fun (hAH.trans hAGraph.symm) u
  choose H1 hH1 hH1N using fun a : I => hDerivative floor hf ε hε hε1 d hd a (A0 a) y hy (hGraph a y) i
  let H := ∑ a : I,(directionalFDeriv (axis i) (w a) y • A0 a y+w a y • H1 a)
  have hSum := half_covariant_sum_smul_higher_graph d w
    (fun a x => (Lo a x).adjoint) A0 H1 y (axis i)
    (fun a => (hWS a).contDiffAt (hY.mem_nhds hy))
    (fun a => (hAS a).contDiffAt (hY.mem_nhds hy))
    (fun a => hGraph a y) hH1
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hOne (a : I) : ‖directionalFDeriv (axis i) (w a) y • A0 a y+w a y • H1 a‖ ≤ 2*B*Q*ε := by
    have hw := hd.principalFirstErrorCoordinateWeight_small_bounds hY (by omega) hK hf hε hε1 hy a b i
    have hw0 : |w a y| ≤ B*ε := hw.1.trans (div_le_self (mul_nonneg hB hε) hβ)
    have hN0 : ‖A0 a y‖ ≤ Q := by
      have hh : ‖A0 a y‖ ≤ QB :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans
            ((mul_one _).le.trans (by
              rw [ContinuousLinearMap.adjoint.norm_map]
              exact hd.norm_physicalFirstCorrectionAtL_axis_le hΩ hm hK hf hε hε1 (-(1/2:ℝ)) hy a)))
      exact hh.trans (le_add_of_nonneg_right hQC)
    have hN1 : ‖H1 a‖ ≤ Q := (hH1N a).trans (le_add_of_nonneg_left hQB)
    have h0 : ‖directionalFDeriv (axis i) (w a) y • A0 a y‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hw.2 hN0 (norm_nonneg _) (mul_nonneg hB hε)
    have h1 : ‖w a y • H1 a‖ ≤ (B*ε)*Q := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hw0 hN1 (norm_nonneg _) (mul_nonneg hB hε)
    exact ((norm_add_le _ _).trans (add_le_add h0 h1)).trans_eq (by ring)
  refine ⟨H,?_,?_⟩
  · rw [halfOperatorCovariantDerivativeL_congr_germ d _ _ AH y (axis i) hGerm,
      half_covariant_higher_congr d C AH A y (axis i) hSame]
    change halfOperatorCovariantDerivativeL d
      (fun x => ∑ a : I,w a x • (Lo a x).adjoint) (fun x => ∑ a : I,w a x • A0 a x) y (axis i)=_
    exact hSum
  · exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun a _ => hOne a)).trans_eq
      (by simp only [Fin.sum_univ_three,CE];ring))

end ShrinkingSpheres.ParallelEnergy
