import Proof.AffineRescaledJetBounds
import Proof.ProfileLogCovectorHigherJets
import Proof.NormalFrameRelativeCoframeGeometry
import Proof.UniformSecondConnection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalFrameScaledCenterL (β : ℝ) : NormalFrameRelativeParameter →L[ℝ] X :=
  β⁻¹ • normalFrameRelativeCenterL

def normalFrameScaledCenter (β : ℝ) (y : X) (p : NormalFrameRelativeParameter) : X :=
  y+normalFrameScaledCenterL β p

lemma normalFrameScaledCenter_point (β : ℝ) (y : X) (L : X →L[ℝ] X) :
    normalFrameScaledCenter β y ((0,L),0) = y := by
  change y+β⁻¹ • (0:X) = y
  simp

lemma norm_normalFrameScaledCenterL_le {β : ℝ} (hβ : 0 ≤ β) : ‖normalFrameScaledCenterL β‖ ≤ β⁻¹ := by
  rw [normalFrameScaledCenterL,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hβ)]
  exact (mul_le_mul_of_nonneg_left norm_normalFrameRelativeCenterL_le_one (inv_nonneg.mpr hβ)).trans_eq (mul_one _)

def normalFrameScaledConnection (g : MetricField) (β : ℝ) (y : X) (p : NormalFrameRelativeParameter) :
    X →L[ℝ] X →L[ℝ] X := β⁻¹ • connectionBilinear g (normalFrameScaledCenter β y p)

def normalFrameScaledLogCovector (r : X → ℝ) (β : ℝ) (y : X) (p : NormalFrameRelativeParameter) :
    X →L[ℝ] ℝ := β⁻¹ • fderiv ℝ (fun x => Real.log (r x)) (normalFrameScaledCenter β y p)

/-- The actual connection and logarithmic profile covector have two uniformly
    bounded jets in beta-rescaled center variables. Only frozen budgets enter. -/
theorem uniform_normalFrame_scaled_horizontal_input_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ CG Cl : ℝ,1 ≤ CG ∧ 1 ≤ Cl ∧ ∀ d : Data,
      Background Ω K M d.γ d.g₁ d.g₂ d.frame → ∀ floor c₀,1 ≤ floor →
      Profile Y d.γ d.frame d.radius floor c₀ Cj → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (let β := beta d.γ d.radius y
       ContDiffAt ℝ ∞ (normalFrameScaledConnection d.γ β y) ((0,L),0) ∧
       ContDiffAt ℝ ∞ (normalFrameScaledLogCovector d.radius β y) ((0,L),0) ∧
       (∀ n : ℕ,n ≤ 2 → ‖iteratedFDeriv ℝ n (normalFrameScaledConnection d.γ β y) ((0,L),0)‖ ≤ CG) ∧
       ∀ n : ℕ,n ≤ 2 → ‖iteratedFDeriv ℝ n (normalFrameScaledLogCovector d.radius β y) ((0,L),0)‖ ≤ Cl) := by
  let D0 := 243*K*|M ⟨1,by omega⟩|
  let D1 := backgroundConnectionDerivativeBudget (by omega : 2 ≤ m) K M
  let D2 := backgroundSecondConnectionBudget hm K M
  let A := 1+D0+D1+D2
  let G := 9*K*|M ⟨1,by omega⟩|
  let DG := 81*K^2*|M ⟨1,by omega⟩|^2+9*K*|M ⟨2,by omega⟩|
  let B := profileLogCovectorJetBudget K G DG (Cj 2) (Cj 3)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hD0 : 0 ≤ D0 := by dsimp only [D0];positivity
  have hD1 : 0 ≤ D1 := by dsimp only [D1,backgroundConnectionDerivativeBudget];positivity
  have hD2 : 0 ≤ D2 := by dsimp only [D2,backgroundSecondConnectionBudget,secondConnectionBudget];positivity
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hDG : 0 ≤ DG := by dsimp only [DG];positivity
  have hB : 0 ≤ B := by
    have hh := profileLogThirdBudget_nonneg K G DG (Cj 2) (Cj 3) hK0 hG hDG
    dsimp only [B,profileLogCovectorJetBudget]
    positivity
  refine ⟨1+2*A,1+2*B,by linarith only [hA],by linarith only [hB],?_⟩
  intro d hd floor c₀ hf hp y hy L
  let β := beta d.γ d.radius y
  let p0 : NormalFrameRelativeParameter := ((0,L),0)
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hβInv : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
  have hCenter : normalFrameScaledCenter β y p0 = y := normalFrameScaledCenter_point β y L
  have hCenterSmooth : ContDiffAt ℝ ∞ (normalFrameScaledCenter β y) p0 :=
    contDiffAt_const.add (normalFrameScaledCenterL β).contDiff.contDiffAt
  have hConn : ContDiffAt ℝ ∞ (connectionBilinear d.γ) y :=
    (hd.1.contDiffOn_connectionBilinear hΩ (zero_lt_one.trans_le hK)).contDiffAt (hΩ.mem_nhds (hSub hy))
  have hLog : ContDiffAt ℝ ∞ (fderiv ℝ (fun x => Real.log (d.radius x))) y :=
    ((hp.1.log (fun x hx => (hp.2 x hx).1.ne')).contDiffAt (hY.mem_nhds hy)).fderiv_right (m:=∞) (by simp)
  have hConnAt : ContDiffAt ℝ ∞ (connectionBilinear d.γ) (normalFrameScaledCenter β y p0) := by rwa [hCenter]
  have hLogAt : ContDiffAt ℝ ∞ (fderiv ℝ (fun x => Real.log (d.radius x))) (normalFrameScaledCenter β y p0) := by rwa [hCenter]
  have hConnJets (n : ℕ) (hn : n ≤ 2) : ‖iteratedFDeriv ℝ n (connectionBilinear d.γ) y‖ ≤ A := by
    interval_cases n
    · rw [norm_iteratedFDeriv_zero]
      exact (hd.connection_budget (zero_lt_one.trans_le hK) (by omega) (hSub hy)).trans (by dsimp only [A,D0];linarith only [hD1,hD2])
    · rw [norm_iteratedFDeriv_one]
      exact (hd.connection_derivative_budget hΩ (zero_lt_one.trans_le hK) (by omega) (hSub hy)).trans (by dsimp only [A,D1];linarith only [hD0,hD2])
    · rw [norm_iteratedFDeriv_two_eq_nested]
      exact (hd.connection_second_derivative_budget hΩ (zero_lt_one.trans_le hK) hm (hSub hy)).trans (by dsimp only [A,D2];linarith only [hD0,hD1])
  have hΓ (a b c : I) : |christoffel d.γ y a b c| ≤ G :=
    hd.1.christoffel_entry_bound (zero_lt_one.trans_le hK) (hSub hy) _ (abs_nonneg _)
      (fun i j => (hd.reference_fderiv_bound (by omega) (hSub hy) i j).trans (le_abs_self _)) a b c
  have hDΓ (a b c i : I) : |coordDeriv a (fun x => christoffel d.γ x b c i) y| ≤ DG := by
    have hh := hd.1.christoffel_derivative_entry_bound hΩ (zero_lt_one.trans_le hK) (hSub hy)
      |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (abs_nonneg _) (abs_nonneg _)
      (fun j k => (hd.reference_fderiv_bound (by omega) (hSub hy) j k).trans (le_abs_self _))
      (fun j k => (hd.reference_second_fderiv_bound (by omega) (hSub hy) j k).trans (le_abs_self _)) (axis a) b c i
    simpa only [norm_axis,mul_one,coordDeriv,DG] using hh
  have he (x : X) (hx : x ∈ Y) (i j : I) := hd.2.2.2.2.2.2.2 x (hSub hx) i j
  have hEll : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1 i j).mono hSub,fun x hx => hd.1.2 x (hSub hx)⟩
  have hLogJets := hp.log_covector_higher_jets hY hEll hK d.frame he hf G DG hG hDG hy hΓ hDΓ
  refine ⟨(hConnAt.comp p0 hCenterSmooth).const_smul β⁻¹,(hLogAt.comp p0 hCenterSmooth).const_smul β⁻¹,?_,?_⟩
  · intro n hn
    have hh := norm_iteratedFDeriv_affine_rescaled_weighted_le (normalFrameScaledCenterL β) y p0
      (connectionBilinear d.γ) hConnAt 2 0 β A hβ hA (norm_normalFrameScaledCenterL_le hβ0)
      (fun j hj => by
        change ‖iteratedFDeriv ℝ j (connectionBilinear d.γ) (normalFrameScaledCenter β y p0)‖ ≤ _
        rw [hCenter]
        have hpow : 1 ≤ β^j := one_le_pow₀ hβ
        exact (hConnJets j hj).trans (by simpa only [Nat.add_zero,mul_one] using
          (mul_le_mul_of_nonneg_left hpow hA))) n hn
    simp only [pow_zero,inv_one,one_smul,show (2:ℕ).factorial=2 from rfl,Nat.cast_ofNat] at hh
    change ‖iteratedFDeriv ℝ n (fun p => β⁻¹ • connectionBilinear d.γ (normalFrameScaledCenter β y p)) p0‖ ≤ _
    rw [norm_iteratedFDeriv_const_smul_at (fun p => connectionBilinear d.γ (normalFrameScaledCenter β y p))
      p0 (hConnAt.comp p0 hCenterSmooth) β⁻¹ n,abs_of_nonneg (inv_nonneg.mpr hβ0)]
    exact (mul_le_mul hβInv hh (norm_nonneg _) zero_le_one).trans (by linarith)
  · intro n hn
    have hh := norm_iteratedFDeriv_affine_rescaled_weighted_le (normalFrameScaledCenterL β) y p0
      (fderiv ℝ (fun x => Real.log (d.radius x))) hLogAt 2 1 β B hβ hB (norm_normalFrameScaledCenterL_le hβ0)
      (fun j hj => by
        change ‖iteratedFDeriv ℝ j (fderiv ℝ (fun x => Real.log (d.radius x))) (normalFrameScaledCenter β y p0)‖ ≤ _
        rw [hCenter]
        exact hLogJets j hj) n hn
    simp only [pow_one,Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one] at hh
    norm_num only at hh
    change ‖iteratedFDeriv ℝ n (fun q => β⁻¹ • fderiv ℝ (fun x => Real.log (d.radius x))
      (y+normalFrameScaledCenterL β q)) p0‖ ≤ 1+2*B
    exact hh.trans (by linarith)

end ShrinkingSpheres
