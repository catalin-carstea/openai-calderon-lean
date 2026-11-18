import Proof.ProfileLogCovectorThreeJets
import Proof.ScaledNormalFrameHorizontalInputJets
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The actual log-radius covector has three bounded jets after rescaling
    center and covector by beta. The constants precede every admitted profile. -/
theorem uniform_normalFrame_scaled_log_covector_three_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Cl : ℝ,1 ≤ Cl ∧ ∀ d : Data,Background Ω K M d.γ d.g₁ d.g₂ d.frame →
      ∀ floor c₀,1 ≤ floor → Profile Y d.γ d.frame d.radius floor c₀ Cj →
      ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      SmoothFiniteJetBound (normalFrameScaledLogCovector d.radius (beta d.γ d.radius y) y)
        ((0,L),0) 3 Cl := by
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let M3 := |M ⟨3,by omega⟩|
  let G := 9*K*M1
  let DG := 81*K^2*M1^2+9*K*M2
  let DDG := 9*(K*M3+2*(9*K^2*M1)*M2+(9*(162*K^3*M1^2+9*K^2*M2))*M1)
  let B := profileLogCovectorThreeJetBudget K G DG DDG (Cj 2) (Cj 3) (Cj 4)
  have hK0 := zero_le_one.trans hK
  have hM1 : 0 ≤ M1 := abs_nonneg _
  have hM2 : 0 ≤ M2 := abs_nonneg _
  have hM3 : 0 ≤ M3 := abs_nonneg _
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hDG : 0 ≤ DG := by dsimp only [DG];positivity
  have hDDG : 0 ≤ DDG := by dsimp only [DDG];positivity
  have hB : 0 ≤ B := profileLogCovectorThreeJetBudget_nonneg _ _ _ _ _ _ _ hK0 hG hDG hDDG
  refine ⟨1+6*B,by linarith only [hB],?_⟩
  intro d hd floor c₀ hf hp y hy L
  let β := beta d.γ d.radius y
  let p0 : NormalFrameRelativeParameter := ((0,L),0)
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hβ0 := zero_le_one.trans hβ
  have hCenter : normalFrameScaledCenter β y p0 = y := normalFrameScaledCenter_point β y L
  have hLog : ContDiffAt ℝ ∞ (fderiv ℝ (fun x => Real.log (d.radius x))) y :=
    ((hp.1.log (fun x hx => (hp.2 x hx).1.ne')).contDiffAt (hY.mem_nhds hy)).fderiv_right (m:=∞) (by simp)
  have hCenterSmooth : ContDiffAt ℝ ∞ (normalFrameScaledCenter β y) p0 :=
    contDiffAt_const.add (normalFrameScaledCenterL β).contDiff.contDiffAt
  have hLogAt : ContDiffAt ℝ ∞ (fderiv ℝ (fun x => Real.log (d.radius x))) (normalFrameScaledCenter β y p0) := by
    rwa [hCenter]
  have hΓ (a b c : I) : |christoffel d.γ y a b c| ≤ G :=
    hd.1.christoffel_entry_bound (zero_lt_one.trans_le hK) (hSub hy) M1 hM1
      (fun i j => (hd.reference_fderiv_bound (by omega) (hSub hy) i j).trans (le_abs_self _)) a b c
  have hDΓ (a b c i : I) : |coordDeriv a (fun x => christoffel d.γ x b c i) y| ≤ DG := by
    have hh := hd.1.christoffel_derivative_entry_bound hΩ (zero_lt_one.trans_le hK) (hSub hy)
      M1 M2 hM1 hM2
      (fun j k => (hd.reference_fderiv_bound (by omega) (hSub hy) j k).trans (le_abs_self _))
      (fun j k => (hd.reference_second_fderiv_bound (by omega) (hSub hy) j k).trans (le_abs_self _)) (axis a) b c i
    simpa only [norm_axis,mul_one,coordDeriv,DG] using hh
  have hDDΓ (a b c i j : I) : |coordDeriv a (coordDeriv b (fun x => christoffel d.γ x c i j)) y| ≤ DDG := by
    have hS := hd.1.contDiffOn_christoffel hΩ (zero_lt_one.trans_le hK) c i j
    have hh := norm_iteratedFDeriv_coordDeriv_le hΩ hS (hSub hy) b 1
    rw [norm_iteratedFDeriv_one] at hh
    have hN := hd.1.christoffel_second_fderiv_bound hΩ (zero_lt_one.trans_le hK) (hSub hy)
      M1 M2 M3 hM1 hM2 hM3
      (fun j k => (hd.reference_fderiv_bound (by omega) (hSub hy) j k).trans (le_abs_self _))
      (fun j k => (hd.reference_second_fderiv_bound (by omega) (hSub hy) j k).trans (le_abs_self _))
      (fun j k => (hd.reference_jet_bound ⟨3,by omega⟩ (hSub hy) j k).trans (le_abs_self _)) c i j
    have hN' : ‖iteratedFDeriv ℝ 2 (fun x => christoffel d.γ x c i j) y‖ ≤ DDG := by
      rw [norm_iteratedFDeriv_two_eq_nested]
      exact hN
    exact (coordDeriv_abs_le _ y a).trans (hh.trans hN')
  have hEll : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1 i j).mono hSub,fun x hx => hd.1.2 x (hSub hx)⟩
  have hJets := hp.log_covector_three_jets hY hEll hK d.frame
    (fun x hx i j => hd.2.2.2.2.2.2.2 x (hSub hx) i j) hf G DG DDG hG hDG hDDG hy hΓ hDΓ hDDΓ
  refine ⟨by positivity,(hLogAt.comp p0 hCenterSmooth).const_smul β⁻¹,?_⟩
  intro n hn
  have hh := norm_iteratedFDeriv_affine_rescaled_weighted_le (normalFrameScaledCenterL β) y p0
    (fderiv ℝ (fun x => Real.log (d.radius x))) hLogAt 3 1 β B hβ hB (norm_normalFrameScaledCenterL_le hβ0)
    (fun j hj => by
      change ‖iteratedFDeriv ℝ j (fderiv ℝ (fun x => Real.log (d.radius x))) (normalFrameScaledCenter β y p0)‖ ≤ _
      rw [hCenter]
      exact hJets j hj) n hn
  norm_num only [pow_one,Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one] at hh
  change ‖iteratedFDeriv ℝ n (fun p => β⁻¹ • fderiv ℝ (fun x => Real.log (d.radius x))
    (y+normalFrameScaledCenterL β p)) p0‖ ≤ 1+6*B
  exact hh.trans (by linarith)
end ShrinkingSpheres
