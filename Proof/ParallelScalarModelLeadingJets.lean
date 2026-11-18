import Proof.ParallelScalarModelRaising
import Proof.ParallelScalarModelBudgets
import Proof.FramedRaisingStrongHalfJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Uniform strong-half first jets of the exact inverse-metric scalar
contraction against the symmetric background raising coefficient. -/
theorem uniform_scalar_model_symmetric_half_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K)
    (WB : ScalarModelLeadingWeightBudget Y Ω m K ρ c₀ M Cj)
    (RB : ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj) :
    ∃ Q : ℝ,0 ≤ Q ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (∀ j : I,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
        (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) →
      ∀ a b k c : I,
      let w := scalarModelLeadingWeight d a b k c
      let C := scalarModelSymmetricCoefficient d w c
      let Ch := scalarModelSymmetricHigher A d w c
      ContDiffOn ℝ ∞ C Y ∧
      (∀ y ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch y)=
        (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
      (∀ y ∈ Y,(C y).adjoint=C y) ∧
      (∀ y ∈ Y,‖C y‖ ≤ Q*ε/beta d.γ d.radius y) ∧
      (∀ y ∈ Y,∀ i : I,∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        halfOperatorCovariantDerivativeL d C Ch y (axis i)=
          L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖L‖ ≤ Q*ε/beta d.γ d.radius y) := by
  let A0 := WB.zeroBound
  let A1 := WB.firstBound
  let QR := RB.bound
  have hA0 := WB.zero_nonneg
  have hA1 := WB.first_nonneg
  have hQR := RB.nonneg
  have hWeights := WB.actual
  have hRaising := RB.actual
  let Q := 2*A0*QR+2*A1*QR+2*A0*QR
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  refine ⟨Q,hQ,?_⟩
  intro floor hf ε hε hε1 d hd A hA a b k c
  let w := scalarModelLeadingWeight d a b k c
  have hW := hWeights floor hf ε hε hε1 d hd a b k c
  have hPoint (y : X) (hy : y ∈ Y) (i : I) := scalarModelSymmetricCoefficient_strong_jet hY hΩ hd
    (zero_lt_one.trans_le hK) A w c i hy hA (hW.1.contDiffAt (hY.mem_nhds hy))
    hA0 hA1 hQR hQR hε (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
    (hRaising floor ε d hd y hy i c).1 (hRaising floor ε d hd y hy i c).2
    (hW.2 y hy i).1 (hW.2 y hy i).2
  refine ⟨scalarModelSymmetricCoefficient_smooth hd w hW.1 c,
    fun y _ => scalarModelSymmetricHigher_balanced A d w c y hA,?_,?_,?_⟩
  · intro y _
    exact symmetric_scalar_adjoint _ (w y)
  · intro y hy
    exact (hPoint y hy 0).1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp only [Q];nlinarith only [mul_nonneg hA0 hQR,mul_nonneg hA1 hQR] : 2*A0*QR ≤ Q) hε)
      (le_trans zero_le_one (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)))
  · intro y hy i
    obtain ⟨L,hL,hLN⟩ := (hPoint y hy i).2
    refine ⟨L,hL,hLN.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ?_ hε) (le_trans zero_le_one (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)))⟩
    dsimp only [Q]
    nlinarith only [mul_nonneg hA0 hQR]

end ShrinkingSpheres.ParallelEnergy
