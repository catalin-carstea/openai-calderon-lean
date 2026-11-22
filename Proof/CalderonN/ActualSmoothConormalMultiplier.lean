module

public import Proof.CalderonN.NormalizedBallTaylorBudgets
public import Proof.CalderonN.NormalizedMultiplierCommutator

import Proof.CalderonN.ActualAngularRadialWeights
import Proof.CalderonN.ActualRadialWeightJets
import Proof.CalderonN.SmoothConormalTaylorSymmetry
import Mathlib.Tactic

/-! The multiplication estimate applies to the normalized first-metric
conormal operator of the actual admitted normal ball. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_smooth_conormal_multiplier (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
      let ell := firstDensityCenterLinear d y
      ∃ (A : X dim → Mat dim) (hA : ContDiff ℝ ∞ A)
        (S : ∀ u : SmoothData dim, ConormalTaylorSolutions A ell u),
        EqOn A a (ball (0 : X dim) (5/4)) ∧
        ∀ (b : SmoothData dim) (J : ℝ), 0 ≤ J → SmoothMultiplierJetBound b J →
        ∀ u : SmoothData dim,
          let T (f : SmoothData dim) := (S f).remainder hA r
          ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num)
            (smoothSubtractData (T (smoothDataMul b u)) (smoothDataMul b (T u)))‖ ≤
          C*J*r^2*‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u‖ ∧
          ‖smoothBoundarySobolev hn (-(1/2) : ℝ) (by norm_num)
            (smoothSubtractData (T (smoothDataMul b u)) (smoothDataMul b (T u)))‖ ≤
          C*J*r^2*‖smoothBoundarySobolev hn (-(1/2) : ℝ) (by norm_num) u‖ := by
  have h₂ : 2 ≤ dim := by omega
  obtain ⟨F₀,η_B,P,Q,Inv,hF₀,hη_B,hP,hQ,hInv,hInv₀,hBall⟩ :=
    uniform_normalized_ballTaylor_budgets (Y:=Y) h₂ hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η_W,C,hη_W,hC,hWeight⟩ :=
    uniform_actual_radial_weight_remainder (Y:=Y) h₂ hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η_P,_,hη_P,_,hPositive⟩ :=
    uniform_actual_angular_radial_weights (Y:=Y) h₂ hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η_N,hη_N,hNormal⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ (by omega : 2 ≤ m)
    K ρ c₀ M Cj hK hρ 1 zero_le_one
  let C_W := 1+2*C
  obtain ⟨L,hL,hEstimate⟩ := norm_normalized_multiplier_commutator hn P Q Inv C_W hP hQ hInv
    (by dsimp only [C_W]; positivity)
  let η := min (min η_B η_W) (min (min η_P η_N) 1)
  refine ⟨η,L,lt_min (lt_min hη_B hη_W) (lt_min (lt_min hη_P hη_N) zero_lt_one),hL,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  let ell := firstDensityCenterLinear d y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε :=
    (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
  have h₀ := hs.trans (min_le_left (min η_B η_W) (min (min η_P η_N) 1))
  have h₁ := hs.trans (min_le_right (min η_B η_W) (min (min η_P η_N) 1))
  have h₂' := h₁.trans (min_le_left (min η_P η_N) 1)
  have hr₁ := hrε.trans (h₁.trans (min_le_right _ _))
  obtain ⟨F,F₁,lo,hi,hFA,hF₁,hEll,hFN₁,hDN,hRN,hInvF,hG,hDE,hRE,hCoer⟩ :=
    hBall floor hf ε he (h₀.trans (min_le_left _ _)) d hd y hy
  let A := coefficientMatrixField 2 F
  let hA := contDiff_coefficientMatrixField 2 F
  have hPos := (hPositive floor hf ε he (h₂'.trans (min_le_left _ _)) d hd y hy A hA hFA).1
  have hSym (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : (A z).IsSymm :=
    (hPos z (ball_subset_closedBall hz)).isHermitian.isSymm
  obtain ⟨hEllN,R,hWR,hR⟩ := hWeight floor hf ε he (h₀.trans (min_le_right _ _)) d hd y hy
  let D : SmoothData dim := ⟨fun z => r*ell z+R.1 z,(contDiff_const.mul ell.contDiff).add R.2⟩
  let W : SmoothData dim := ⟨fun z => 1+D.1 z,contDiff_const.add D.2⟩
  have hSphW (z : X dim) (hz : z ∈ standardSphere dim) : W.1 z = firstNormalRadialWeight d y r z := by
    change 1+(r*ell z+R.1 z) = _
    rw [← add_assoc]
    exact hWR hz
  have hNear (z : X dim) (hz : z ∈ standardSphere dim) :
      r • frameVector d.frame y z ∈ interior (disk d.γ y (max ρ (d.radius y))) := by
    have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
    have hw := frameVector_mem_disk d.γ d.frame y z 1 hFrame (sphere_subset_closedBall hz)
    exact (hNormal floor hf ε he (h₂'.trans (min_le_right _ _)) d hd y hy _ hw).1.1
  have hW (u : SmoothData dim) : EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim) := by
    intro z hz
    have hEq : A z = a z :=
      hFA (closedBall_subset_ball (by norm_num : (1:ℝ) < 5/4) (sphere_subset_closedBall hz))
    have hFlux : smoothBallFlux A u.1 z = smoothBallFlux a u.1 z := by
      ext k
      simp only [smoothBallFlux_apply,hEq]
    change smoothBallConormal A u.1 z = W.1 z*fderiv ℝ u.1 z z
    rw [smoothBallConormal,hFlux,hSphW z hz]
    exact hd.inner_actualNormalFlux_radial_row h₂ hΩ (zero_lt_one.trans_le hK) hy hr.ne' z (hNear z hz) u.1
  have hDR : EqOn D.1 (fun z => W.1 z-1) (standardSphere dim) := by
    intro z _
    change D.1 z = 1+D.1 z-1
    ring
  have hRR : EqOn R.1 (fun z => W.1 z-1-r*ell z) (standardSphere dim) := by
    intro z _
    change R.1 z = 1+(r*ell z+R.1 z)-1-r*ell z
    ring
  have hJet (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      (|W.1 z| ≤ C_W ∧ ‖fderiv ℝ W.1 z‖ ≤ C_W) ∧
      (|D.1 z| ≤ C_W*r ∧ ‖fderiv ℝ D.1 z‖ ≤ C_W*r) ∧
      (|R.1 z| ≤ C_W*r^2 ∧ ‖fderiv ℝ R.1 z‖ ≤ C_W*r^2) := by
    have hB := hR z (ball_subset_closedBall hz)
    have hEllz : |ell z| ≤ C := (ell.le_opNorm z).trans
      ((mul_le_mul hEllN (mem_ball_zero_iff.mp hz).le (norm_nonneg _) hC).trans_eq (mul_one _))
    have hNum : r*C+C*r^2 ≤ 2*C*r := by
      nlinarith only [mul_le_mul_of_nonneg_left hr₁ (mul_nonneg hC hr.le)]
    have hDW : |D.1 z| ≤ 2*C*r := by
      change |r*ell z+R.1 z| ≤ _
      exact (abs_add_le _ _).trans ((add_le_add (by
        rw [abs_mul,abs_of_pos hr]; exact mul_le_mul_of_nonneg_left hEllz hr.le) hB.1).trans
        hNum)
    have hDD : ‖fderiv ℝ D.1 z‖ ≤ 2*C*r := by
      change ‖fderiv ℝ (fun x => r*ell x+R.1 x) z‖ ≤ _
      have hDeriv : fderiv ℝ (fun x => r*ell x) z = r • ell := by
        change fderiv ℝ (r • ⇑ell) z = _
        rw [fderiv_const_smul (ell.differentiable z),ContinuousLinearMap.fderiv]
      have hAdd := fderiv_fun_add ((differentiableAt_const r).mul (ell.differentiable z))
        (R.2.differentiable (by simp) z)
      change fderiv ℝ (fun x => r*ell x+R.1 x) z = fderiv ℝ (fun x => r*ell x) z+_ at hAdd
      rw [hAdd,hDeriv]
      exact ((norm_add_le _ _).trans (add_le_add (by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left hEllN hr.le) hB.2)).trans hNum
    have hWD : fderiv ℝ W.1 z = fderiv ℝ D.1 z := by
      change fderiv ℝ (fun x => 1+D.1 x) z = _
      rw [fderiv_fun_add (differentiableAt_const (1:ℝ)) (D.2.differentiable (by simp) z),
        fderiv_fun_const,Pi.zero_apply,zero_add]
    have hBound : 2*C*r ≤ 2*C := by
      exact (mul_le_mul_of_nonneg_left hr₁ (by positivity : 0 ≤ 2*C)).trans_eq (mul_one _)
    have hW0 : |W.1 z| ≤ C_W := by
      change |1+D.1 z| ≤ C_W
      exact (abs_add_le _ _).trans (by rw [abs_one]; exact add_le_add_right (hDW.trans hBound) _)
    exact ⟨⟨hW0,(hWD ▸ hDD).trans (hBound.trans (by dsimp [C_W]; linarith))⟩,
      ⟨hDW.trans (by dsimp [C_W]; nlinarith only [hr]),
        hDD.trans (by dsimp [C_W]; nlinarith only [hr])⟩,
      ⟨hB.1.trans (mul_le_mul_of_nonneg_right (by dsimp [C_W]; linarith) (sq_nonneg r)),
        hB.2.trans (mul_le_mul_of_nonneg_right (by dsimp [C_W]; linarith) (sq_nonneg r))⟩⟩
  have hsub : ball (0 : X dim) 1 ⊆ ball (0 : X dim) (5/4) := ball_subset_ball (by norm_num)
  let S (f : SmoothData dim) := Classical.choice (exists_conormalTaylorSolutions_of_extension F F₀ hF₀
    (fun _ _ => rfl) hEll ell f)
  have hHalf := hEstimate F F₀ F₁ ell r hF₀ (hF₁.mono hsub) hSym hCoer hG hDE hRE
    hr.le hr₁ hFN₁ hDN hRN hInvF hInv₀ lo hi hEll W D R S hW hDR hRR hJet
  refine ⟨A,hA,S,hFA,fun b J hJ hb u => ⟨hHalf b J hJ hb u,?_⟩⟩
  exact norm_smooth_multiplier_commutator_negHalf_of_half hn b (fun f => (S f).remainder hA r)
    (fun f g => conormalTaylorSolutions_remainder_symmetric hn hA hSym (S f) (S g) r)
    (L*J*r^2) (by positivity) (hHalf b J hJ hb) u

end CalderonN
