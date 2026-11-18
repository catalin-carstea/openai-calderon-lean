import Proof.ParallelScalarFirstPhysicalThird
import Proof.UniformEffectiveFirstLowEndpointData
import Proof.UniformEffectiveFirstStrongHalfAdjoint
import Proof.StrongHalfCovariantCalculus
import Proof.ScalarPrincipalSharpTwoJets

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

lemma norm_symmetric_scalar_jets {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B L : E →L[ℝ] E) (w dw A0 A1 CB CE ε β : ℝ)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hCB : 0 ≤ CB) (hCE : 0 ≤ CE)
    (hε : 0 ≤ ε) (hβ : 0 < β)
    (hB : ‖B‖ ≤ CB*ε/β) (hL : ‖L‖ ≤ CE*ε)
    (hw0 : |w| ≤ A0*ε) (hw1 : |w| ≤ A0*ε/β) (hdw : |dw| ≤ A1*ε) :
    ‖w • (B+B.adjoint)‖ ≤ (2*A0*CB)*ε^2/β ∧
      ‖dw • (B+B.adjoint)+w • (L+L.adjoint)‖ ≤ (2*A1*CB+2*A0*CE)*ε^2/β := by
  have hSB : ‖B+B.adjoint‖ ≤ 2*CB*ε/β := by
    calc
      _ ≤ ‖B‖+‖B.adjoint‖ := norm_add_le _ _
      _ = 2*‖B‖ := by rw [ContinuousLinearMap.adjoint.norm_map];ring
      _ ≤ _ := by convert mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring
  have hSL : ‖L+L.adjoint‖ ≤ 2*CE*ε := by
    calc
      _ ≤ ‖L‖+‖L.adjoint‖ := norm_add_le _ _
      _ = 2*‖L‖ := by rw [ContinuousLinearMap.adjoint.norm_map];ring
      _ ≤ _ := by convert mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring
  constructor
  · calc
      _ = |w| * ‖B+B.adjoint‖ := by rw [norm_smul,Real.norm_eq_abs]
      _ ≤ (A0*ε)*(2*CB*ε/β) := mul_le_mul hw0 hSB (norm_nonneg _) (mul_nonneg hA0 hε)
      _ = _ := by ring
  · calc
      _ ≤ ‖dw • (B+B.adjoint)‖+‖w • (L+L.adjoint)‖ := norm_add_le _ _
      _ = |dw| * ‖B+B.adjoint‖+|w| * ‖L+L.adjoint‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      _ ≤ (A1*ε)*(2*CB*ε/β)+(A0*ε/β)*(2*CE*ε) := add_le_add
        (mul_le_mul hdw hSB (norm_nonneg _) (mul_nonneg hA1 hε))
        (mul_le_mul hw1 hSL (norm_nonneg _) (by positivity))
      _ = _ := by ring

lemma symmetric_weighted_half_covariant_derivative (d : Data)
    (B : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H A : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (w : X → ℝ) (y a : X)
    (hB : ContDiffAt ℝ ∞ B y) (hBA : ContDiffAt ℝ ∞ (fun x => (B x).adjoint) y)
    (hw : ContDiffAt ℝ ∞ w y)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hD : halfOperatorCovariantDerivativeL d B H y a=
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hDA : halfOperatorCovariantDerivativeL d (fun x => (B x).adjoint) A y a=
      L.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    halfOperatorCovariantDerivativeL d (fun x => w x • (B x+(B x).adjoint))
      (fun x => w x • (H x+A x)) y a=
      (fderiv ℝ w y a • (B y+(B y).adjoint)+w y • (L+L.adjoint)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hSum := half_covariant_strong_add d B (fun x => (B x).adjoint) H A y a hB hBA L L.adjoint hD hDA
  exact half_covariant_strong_smul d w (fun x => B x+(B x).adjoint) (fun x => H x+A x)
    y a hw (hB.add hBA) (L+L.adjoint) hSum

/-- The actual scalar-weighted symmetric complete first coefficient has
uniform small half-domain norm and strong first covariant jet. All
packets are fixed before every test; no new adjoint family is selected. -/
theorem uniform_scalar_first_symmetric_half_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η Q : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ Q ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ CB CS : ℝ,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,∀ a b k : I,∀ y ∈ Y,
        let w := fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b
        let C := scalarFirstSymmetricCoefficient P w k
        let Ch := scalarFirstSymmetricHigher WF w k
        ‖C y‖ ≤ Q*ε^2/beta d.γ d.radius y ∧
        ∀ i : I,∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
          halfOperatorCovariantDerivativeL d C Ch y (axis i)=
            L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
          ‖L‖ ≤ Q*ε^2/beta d.γ d.radius y := by
  obtain ⟨ηB,CB,hηB,hηB1,hCB,hLow⟩ := uniform_effective_first_low_endpoint_data
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,CE,hηD,hηD1,hCE,hDer⟩ := uniform_effective_first_strong_half_derivative_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let A0 := abs (principalZeroBudget K)
  let A1 := abs (principalFirstBudget K (abs (M ⟨1,by omega⟩)))
  let Q := 2*A0*CB+2*A1*CB+2*A0*CE
  have hA0 : 0 ≤ A0 := abs_nonneg _
  have hA1 : 0 ≤ A1 := abs_nonneg _
  refine ⟨min ηB ηD,Q,lt_min hηB hηD,(min_le_left _ _).trans hηB1,by dsimp only [Q];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P CB0 CS WF a b k y hy
  have hε1 := hSmall.trans ((min_le_left _ _).trans hηB1)
  have hB := hLow floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P k
  have hD := hDer floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P CB0 CS WF y hy k
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hWeights (i : I) := scalar_principal_sharp_two_jet_weights hY hg hg2 hK d.frame hFrame
    hd.2.2.2.2.1 hf hε hε1 hd.2.2.2.2.2 hy |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
    (abs_nonneg _) (abs_nonneg _)
    (fun i j => (hd.1.reference_fderiv_bound (by omega) (hSub hy) i j).trans (le_abs_self _))
    (fun i j => (hd.1.reference_second_fderiv_bound (by omega) (hSub hy) i j).trans (le_abs_self _)) a b i i
  let β := beta d.γ d.radius y
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβpos := zero_lt_one.trans_le hβ
  let w := fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b
  have hwRaw : |w y| ≤ A0*ε/β^2 := (hWeights 0).1.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε) (sq_nonneg _))
  have hw1 : |w y| ≤ A0*ε/β := hwRaw.trans (div_le_div_of_nonneg_left (mul_nonneg hA0 hε)
    hβpos (by nlinarith only [hβ]))
  have hw0 : |w y| ≤ A0*ε := hw1.trans (div_le_self (mul_nonneg hA0 hε) hβ)
  have hdw (i : I) : |fderiv ℝ w y (axis i)| ≤ A1*ε := by
    have hh := (hWeights i).2.1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) hε) hβpos.le)
    exact hh.trans (div_le_self (mul_nonneg hA1 hε) hβ)
  have hWS := hd.contDiffOn_scalarPrincipalMatrix_entry hSub (zero_lt_one.trans_le hK) a b
  have hDrift := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub (zero_lt_one.trans_le hK) k
  have hAdjS := P.firstCovariantCoordinateAdjoint_smooth hd hY hΩ (zero_lt_one.trans_le hK) k hDrift
  have hQ0 : 2*A0*CB ≤ Q := by dsimp only [Q];nlinarith only [hA0,hA1,hCB,hCE]
  have hQ1 : 2*A1*CB+2*A0*CE ≤ Q := by dsimp only [Q];nlinarith only [hA0,hCB]
  obtain ⟨L0,hL0,hLA0,hLN0,hLAN0⟩ := hD 0
  have hNorm0 := (norm_symmetric_scalar_jets (P.firstCovariantCoordinateHalfL k y) L0
    (w y) (fderiv ℝ w y (axis 0)) A0 A1 CB CE ε β hA0 hA1 hCB hCE hε hβpos
    (hB.2 y hy) hLN0 hw0 hw1 (hdw 0)).1
  refine ⟨hNorm0.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hQ0 (sq_nonneg ε)) hβpos.le),?_⟩
  intro i
  obtain ⟨L,hL,hLA,hLN,hLAN⟩ := hD i
  let T := fderiv ℝ w y (axis i) • (P.firstCovariantCoordinateHalfL k y+(P.firstCovariantCoordinateHalfL k y).adjoint)+
    w y • (L+L.adjoint)
  refine ⟨T,symmetric_weighted_half_covariant_derivative d (P.firstCovariantCoordinateHalfL k)
    (P.firstCovariantCoordinateHigherL k) (WF.covariantCoordinateAdjointHigher k) w y (axis i)
    (hB.1.contDiffAt (hY.mem_nhds hy)) (hAdjS.contDiffAt (hY.mem_nhds hy))
    (hWS.contDiffAt (hY.mem_nhds hy)) L hL hLA,?_⟩
  have hNorm := (norm_symmetric_scalar_jets (P.firstCovariantCoordinateHalfL k y) L
    (w y) (fderiv ℝ w y (axis i)) A0 A1 CB CE ε β hA0 hA1 hCB hCE hε hβpos
    (hB.2 y hy) hLN hw0 hw1 (hdw i)).2
  exact hNorm.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hQ1 (sq_nonneg ε)) hβpos.le)

end ShrinkingSpheres.ParallelEnergy
