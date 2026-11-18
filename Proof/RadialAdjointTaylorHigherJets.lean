import Proof.RadialAdjointForcingHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P E H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

def radialAdjointTaylorHigherJetBudget (N : ℕ) (CI C normD0 : ℝ) : ℝ :=
  let B := inverseFamilyJetBudget N CI C
  2^N*radialAdjointForcingHigherJetBudget N C normD0*B+2^N*C*(2^N*B*C)

/-- Every finite joint jet of the actual adjoint Taylor family retains r²
    after the genuine first-adjoint cancellation and canonical inversion. -/
theorem norm_iteratedFDeriv_radial_adjoint_taylor_higher_le
    (M0 M01 : P → E →L[ℝ] E) (M1 M11 : P → H →L[ℝ] H)
    (D D1 Da1 T Td : P → H →L[ℝ] E) (D0 : H →L[ℝ] E) (x : P)
    (hM0 : ContDiffAt ℝ ∞ M0 x) (hM01 : ContDiffAt ℝ ∞ M01 x)
    (hM1 : ContDiffAt ℝ ∞ M1 x) (hM11 : ContDiffAt ℝ ∞ M11 x)
    (hD : ContDiffAt ℝ ∞ D x) (hD1 : ContDiffAt ℝ ∞ D1 x) (hDa1 : ContDiffAt ℝ ∞ Da1 x)
    (hT : ContDiffAt ℝ ∞ T x) (hTd : ContDiffAt ℝ ∞ Td x)
    (hInv : (M1 x).IsInvertible)
    (hFirst : Da1 =ᶠ[𝓝 x] (fun p => D1 p+(M01 p).comp D0-D0.comp (M11 p)))
    (N : ℕ) (r CI C : ℝ) (hr : 0 ≤ r) (hCI : 0 ≤ CI) (hC : 0 ≤ C)
    (hNI : ‖(M1 x).inverse‖ ≤ CI)
    (hM0Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n M0 x‖ ≤ C)
    (hM1Jets : ∀ n : ℕ,1 ≤ n → n ≤ N → ‖iteratedFDeriv ℝ n M1 x‖ ≤ C)
    (hDJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p => D p-D0-r • D1 p) x‖ ≤ C*r^2)
    (hQ0Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n
      (fun p => M0 p-ContinuousLinearMap.id ℝ E-r • M01 p) x‖ ≤ C*r^2)
    (hQ1Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n
      (fun p => M1 p-ContinuousLinearMap.id ℝ H-r • M11 p) x‖ ≤ C*r^2)
    (hDel0Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p => M0 p-ContinuousLinearMap.id ℝ E) x‖ ≤ C*r)
    (hDel1Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p => M1 p-ContinuousLinearMap.id ℝ H) x‖ ≤ C*r)
    (hD1Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n D1 x‖ ≤ C)
    (hDa1Jets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n Da1 x‖ ≤ C)
    (hTJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n T x‖ ≤ C*r^2)
    (hTdJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n Td x‖ ≤ C*r^2)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => ((M0 p).comp (D p)+T p-Td p).comp (M1 p).inverse-
      D0-r • Da1 p) x‖ ≤ radialAdjointTaylorHigherJetBudget N CI C ‖D0‖*r^2 := by
  let Inv := fun p => (M1 p).inverse
  let Del1 := fun p => M1 p-ContinuousLinearMap.id ℝ H
  let F := fun p => radialAdjointTaylorForcing (M0 p) (M01 p) (M1 p) (M11 p) (D p) D0 (D1 p) (T p) (Td p) r
  let B := inverseFamilyJetBudget N CI C
  let CF := radialAdjointForcingHigherJetBudget N C ‖D0‖
  have hB : 0 ≤ B := inverseFamilyJetBudget_nonneg N CI C hCI hC
  have hCF : 0 ≤ CF := by dsimp only [CF,radialAdjointForcingHigherJetBudget];positivity
  have hInvSmooth : ContDiffAt ℝ ∞ Inv x := hInv.contDiffAt_map_inverse.comp x hM1
  have hDel1 : ContDiffAt ℝ ∞ Del1 x := hM1.sub contDiffAt_const
  have hF : ContDiffAt ℝ ∞ F x := by
    dsimp only [F,radialAdjointTaylorForcing]
    fun_prop
  have hIJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j Inv x‖ ≤ B :=
    norm_iteratedFDeriv_inverse_family_le_of_isInvertible M1 x hInv hM1 N CI C hCI hC hNI hM1Jets j hj
  have hInvNear := eventually_isInvertible_of_continuousAt M1 x hM1.continuousAt hInv
  have hDiff : (fun p => Inv p-ContinuousLinearMap.id ℝ H) =ᶠ[𝓝 x]
      (fun p => -(Inv p).comp (Del1 p)) := by
    filter_upwards [hInvNear] with p hp
    apply ContinuousLinearMap.ext
    intro u
    have he : (M1 p).inverse (M1 p u) = u := congrArg (fun L : H →L[ℝ] H => L u) hp.inverse_comp_self
    change (M1 p).inverse u-u = -((M1 p).inverse (M1 p u-u))
    rw [map_sub,he]
    abel
  have hIDJets (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun p => Inv p-ContinuousLinearMap.id ℝ H) x‖ ≤ (2^N*B*C)*r := by
    rw [(hDiff.iteratedFDeriv ℝ j).eq_of_nhds,
      norm_iteratedFDeriv_neg_at _ x (hInvSmooth.clm_comp hDel1) j]
    exact (norm_iteratedFDeriv_operator_comp_common_bound Inv Del1 x hInvSmooth hDel1 N B (C*r)
      hB (by positivity) hIJets hDel1Jets j hj).trans_eq (by ring)
  have hFJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j F x‖ ≤ CF*r^2 :=
    norm_iteratedFDeriv_radialAdjointTaylorForcing_le M0 M01 M1 M11 D D1 T Td D0 x
      hM0 hM01 hM1 hM11 hD hD1 hT hTd N r C hr hC hM0Jets hDJets hQ0Jets hQ1Jets hDel0Jets hD1Jets hTJets hTdJets j hj
  have hEq : (fun p => ((M0 p).comp (D p)+T p-Td p).comp (M1 p).inverse-D0-r • Da1 p) =ᶠ[𝓝 x]
      (fun p => (F p).comp (Inv p)+r • (Da1 p).comp (Inv p-ContinuousLinearMap.id ℝ H)) := by
    filter_upwards [hInvNear,hFirst] with p hp hFirstp
    exact radial_adjoint_taylor_cancellation (M0 p) (M01 p) (M1 p) (M11 p) (Inv p)
      (D p) D0 (D1 p) (Da1 p) (T p) (Td p) r hp.self_comp_inverse hFirstp
  rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds]
  have hFInvN : ‖iteratedFDeriv ℝ n (fun p => (F p).comp (Inv p)) x‖ ≤ (2^N*CF*B)*r^2 :=
    (norm_iteratedFDeriv_operator_comp_common_bound F Inv x hF hInvSmooth N (CF*r^2) B
      (by positivity) hB hFJets hIJets n hn).trans_eq (by ring)
  have hRInvN : ‖iteratedFDeriv ℝ n (fun p => r • (Da1 p).comp (Inv p-ContinuousLinearMap.id ℝ H)) x‖ ≤
      (2^N*C*(2^N*B*C))*r^2 := by
    rw [norm_iteratedFDeriv_const_smul_at _ x (hDa1.clm_comp (hInvSmooth.sub contDiffAt_const)) r n,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_operator_comp_common_bound Da1 (fun p => Inv p-ContinuousLinearMap.id ℝ H) x hDa1
        (hInvSmooth.sub contDiffAt_const) N C ((2^N*B*C)*r) hC (by positivity) hDa1Jets hIDJets n hn) hr).trans_eq (by ring)
  exact (norm_iteratedFDeriv_add_at_le _ _ x (hF.clm_comp hInvSmooth)
    ((hDa1.clm_comp (hInvSmooth.sub contDiffAt_const)).const_smul r) n).trans
      ((add_le_add hFInvN hRInvN).trans_eq (by dsimp only [radialAdjointTaylorHigherJetBudget,B,CF];ring))

end ShrinkingSpheres
