import Proof.RadialAdjointTaylorCancellation
import Proof.RadialTaylorHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P E H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]

def radialAdjointForcingHigherJetBudget (N : ℕ) (C normD0 : ℝ) : ℝ :=
  2*2^N*C^2+(2*normD0+2)*C

/-- The exact first-adjoint cancellation forcing retains the quadratic
    radius gain in all finite mixed parameter jets. -/
theorem norm_iteratedFDeriv_radialAdjointTaylorForcing_le
    (M0 M01 : P → E →L[ℝ] E) (M1 M11 : P → H →L[ℝ] H)
    (D D1 T Td : P → H →L[ℝ] E) (D0 : H →L[ℝ] E) (x : P)
    (hM0 : ContDiffAt ℝ ∞ M0 x) (hM01 : ContDiffAt ℝ ∞ M01 x)
    (hM1 : ContDiffAt ℝ ∞ M1 x) (hM11 : ContDiffAt ℝ ∞ M11 x)
    (hD : ContDiffAt ℝ ∞ D x) (hD1 : ContDiffAt ℝ ∞ D1 x)
    (hT : ContDiffAt ℝ ∞ T x) (hTd : ContDiffAt ℝ ∞ Td x)
    (N : ℕ) (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hM0Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n M0 x‖ ≤ C)
    (hDJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p => D p-D0-r • D1 p) x‖ ≤ C*r^2)
    (hQ0Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n
      (fun p => M0 p-ContinuousLinearMap.id ℝ E-r • M01 p) x‖ ≤ C*r^2)
    (hQ1Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n
      (fun p => M1 p-ContinuousLinearMap.id ℝ H-r • M11 p) x‖ ≤ C*r^2)
    (hDelJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p => M0 p-ContinuousLinearMap.id ℝ E) x‖ ≤ C*r)
    (hD1Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n D1 x‖ ≤ C)
    (hTJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n T x‖ ≤ C*r^2)
    (hTdJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n Td x‖ ≤ C*r^2)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => radialAdjointTaylorForcing (M0 p) (M01 p) (M1 p) (M11 p)
      (D p) D0 (D1 p) (T p) (Td p) r) x‖ ≤ radialAdjointForcingHigherJetBudget N C ‖D0‖*r^2 := by
  let J := fun p => D p-D0-r • D1 p
  let Q0 := fun p => M0 p-ContinuousLinearMap.id ℝ E-r • M01 p
  let Q1 := fun p => M1 p-ContinuousLinearMap.id ℝ H-r • M11 p
  let Del := fun p => M0 p-ContinuousLinearMap.id ℝ E
  let A := fun p => (M0 p).comp (J p)
  let B := fun p => (Q0 p).comp D0
  let G := fun p => D0.comp (Q1 p)
  let V := fun p => r • (Del p).comp (D1 p)
  have hJ : ContDiffAt ℝ ∞ J x := (hD.sub contDiffAt_const).sub (hD1.const_smul r)
  have hQ0 : ContDiffAt ℝ ∞ Q0 x := (hM0.sub contDiffAt_const).sub (hM01.const_smul r)
  have hQ1 : ContDiffAt ℝ ∞ Q1 x := (hM1.sub contDiffAt_const).sub (hM11.const_smul r)
  have hDel : ContDiffAt ℝ ∞ Del x := hM0.sub contDiffAt_const
  have hA : ContDiffAt ℝ ∞ A x := hM0.clm_comp hJ
  have hB : ContDiffAt ℝ ∞ B x := hQ0.clm_comp contDiffAt_const
  have hG : ContDiffAt ℝ ∞ G x := contDiffAt_const.clm_comp hQ1
  have hV : ContDiffAt ℝ ∞ V x := (hDel.clm_comp hD1).const_smul r
  have hAN : ‖iteratedFDeriv ℝ n A x‖ ≤ (2^N*C^2)*r^2 :=
    (norm_iteratedFDeriv_operator_comp_common_bound M0 J x hM0 hJ N C (C*r^2)
      hC (by positivity) hM0Jets hDJets n hn).trans_eq (by ring)
  have hBN : ‖iteratedFDeriv ℝ n B x‖ ≤ (‖D0‖*C)*r^2 :=
    (norm_iteratedFDeriv_operator_precomp_fixed_le Q0 D0 x hQ0 n).trans
      ((mul_le_mul_of_nonneg_left (hQ0Jets n hn) (norm_nonneg D0)).trans_eq (by ring))
  have hGN : ‖iteratedFDeriv ℝ n G x‖ ≤ (‖D0‖*C)*r^2 :=
    (norm_iteratedFDeriv_operator_postcomp_fixed_le D0 Q1 x hQ1 n).trans
      ((mul_le_mul_of_nonneg_left (hQ1Jets n hn) (norm_nonneg D0)).trans_eq (by ring))
  have hVN : ‖iteratedFDeriv ℝ n V x‖ ≤ (2^N*C^2)*r^2 := by
    rw [norm_iteratedFDeriv_const_smul_at _ x (hDel.clm_comp hD1) r n,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_operator_comp_common_bound Del D1 x hDel hD1 N (C*r) C
        (by positivity) hC hDelJets hD1Jets n hn) hr).trans_eq (by ring)
  have h1 := norm_iteratedFDeriv_add_at_le A B x hA hB n
  have h2 := norm_iteratedFDeriv_sub_at_le (fun p => A p+B p) G x (hA.add hB) hG n
  have h3 := norm_iteratedFDeriv_add_at_le (fun p => A p+B p-G p) V x ((hA.add hB).sub hG) hV n
  have h4 := norm_iteratedFDeriv_add_at_le (fun p => A p+B p-G p+V p) T x (((hA.add hB).sub hG).add hV) hT n
  have h5 := norm_iteratedFDeriv_sub_at_le (fun p => A p+B p-G p+V p+T p) Td x
    ((((hA.add hB).sub hG).add hV).add hT) hTd n
  change ‖iteratedFDeriv ℝ n (fun p => A p+B p-G p+V p+T p-Td p) x‖ ≤ _
  dsimp only [radialAdjointForcingHigherJetBudget]
  nlinarith only [h1,h2,h3,h4,h5,hAN,hBN,hGN,hVN,hTJets n hn,hTdJets n hn]

end ShrinkingSpheres
