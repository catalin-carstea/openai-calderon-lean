import Proof.ParallelFirstSelfErrorEndpointPacket
import Proof.ParallelFirstSelfAdjointJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- Typed point assembly of the original weighted native error's genuine
true-adjoint higher jets. The SAME global AH families are supplied before
the derivative direction; native choices are used only at this point. -/
theorem weighted_actual_error_true_adjoint_jet_at
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε CA CD B : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (hB : 0 ≤ B)
    {y : X} (hy : y ∈ Y) (hβ : 1 ≤ beta d.γ d.radius y)
    (p : (a : I) → FirstSelfActualErrorEndpointPacket Y d (axis a))
    (q : (a : I) → FirstSelfNativeAdjointPacket Y Ω d y (axis a) CD ε)
    (AH : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hAH : ∀ a,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH a y)=
      ((p a).low y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hAN : ∀ a,‖AH a y‖ ≤ CA*d.radius y)
    (w : I → X → ℝ) (hwS : ∀ a,ContDiffAt ℝ ∞ (w a) y)
    (i : I) (hw : ∀ a,|w a y| ≤ B)
    (hDw : ∀ a,|directionalFDeriv (axis i) (w a) y| ≤ B*beta d.γ d.radius y) :
    ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      halfOperatorCovariantDerivativeL d
        (fun x => ∑ a : I,w a x • ((p a).low x).adjoint)
        (fun x => ∑ a : I,w a x • AH a x) y (axis i)=
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H ∧
      ‖H‖ ≤ (3*B*(CA+CD))*d.radius y*beta d.γ d.radius y := by
  classical
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hC (a : I) : ContDiffAt ℝ ∞ (fun x => ((p a).low x).adjoint) y :=
    Adj.contDiff.contDiffAt.comp y ((p a).low_smooth.contDiffAt (hY.mem_nhds hy))
  have hOne (a : I) := (p a).true_adjoint_jet_at hY hΩ hSub hd hK hy (q a) (AH a) (hAH a)
    (axis i) (by simp only [norm_axis,le_refl])
  choose H hH hHN hHE using hOne
  have hNorm (a : I) : ‖H a‖ ≤ CD*d.radius y*beta d.γ d.radius y := by
    simpa only [norm_axis,mul_one] using hHN a
  let T := ∑ a : I,(directionalFDeriv (axis i) (w a) y • AH a y+w a y • H a)
  refine ⟨T,half_covariant_sum_smul_higher_graph d w
    (fun a x => ((p a).low x).adjoint) AH H y (axis i) hwS hC hAH hH,?_⟩
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  have hβ0 : 0 ≤ beta d.γ d.radius y := zero_le_one.trans hβ
  have hTerm (a : I) : ‖directionalFDeriv (axis i) (w a) y • AH a y+w a y • H a‖ ≤
      B*(CA+CD)*d.radius y*beta d.γ d.radius y := by
    have h1 : ‖directionalFDeriv (axis i) (w a) y • AH a y‖ ≤
        (B*beta d.γ d.radius y)*(CA*d.radius y) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hDw a) (hAN a) (norm_nonneg _) (mul_nonneg hB hβ0)
    have h2 : ‖w a y • H a‖ ≤ B*(CD*d.radius y*beta d.γ d.radius y) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hw a) (hNorm a) (norm_nonneg _) hB
    exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)
  calc
    _ ≤ ∑ a : I,‖directionalFDeriv (axis i) (w a) y • AH a y+w a y • H a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : I,B*(CA+CD)*d.radius y*beta d.γ d.radius y := Finset.sum_le_sum (fun a _ => hTerm a)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end ShrinkingSpheres.ParallelEnergy
