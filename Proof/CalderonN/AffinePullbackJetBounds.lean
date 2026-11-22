module

public import Proof.CalderonN.CenterAffineCoordinates

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Third local jets of the actual normal pullback evaluated along the
explicit affine center and frame jets. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def affineNormalCoefficient (d : Data dim)
    (y a : X dim) (U P : FrameOperator dim) (c c' : ℝ)
    (p : CenterParameters dim) : Mat dim :=
  (c+p.1*c') • pullbackDivergenceMatrix (affineNormalPullbackData d y a U P p)

/-- The pointwise inputs for the finite-dimensional coefficient map use at
most four joint derivatives of the exponential and three of the metric. -/
theorem exists_affineNormalPullbackData_jet_envelope (dim : ℕ) [NeZero dim]
    (A V G : ℝ) (hA : 1 ≤ A) (hV : 1 ≤ V) (hG : 0 ≤ G) :
    ∃ B ≥ (1 : ℝ), ∀ (d : Data dim) (y a v : X dim) (U P : FrameOperator dim),
      ‖a‖ ≤ A → ‖v‖ ≤ 1 → ‖U‖ ≤ A → ‖P‖ ≤ A →
      (let b := (y,U v)
       ContDiffAt ℝ ∞ d.expMap b ∧ ContDiffAt ℝ ∞ d.g₁ (d.expMap b) ∧
       (∀ j, 1 ≤ j → j ≤ 4 → ‖iteratedFDeriv ℝ j d.expMap b‖ ≤ V) ∧
       ∀ j, j ≤ 3 → ‖iteratedFDeriv ℝ j d.g₁ (d.expMap b)‖ ≤ G) →
      ContDiffAt ℝ ∞ (affineNormalPullbackData d y a U P) ((0 : ℝ),v) ∧
        ∀ j, j ≤ 3 →
          ‖iteratedFDeriv ℝ j (affineNormalPullbackData d y a U P) ((0 : ℝ),v)‖ ≤ B := by
  let I := 1+8*‖(ContinuousLinearMap.apply (E := X dim) ℝ (X dim)).flip‖*A+A
  let VE := 6*V*I^3
  let J := (ContinuousLinearMap.compL ℝ (X dim) (X dim × X dim) (X dim)).flip
    (ContinuousLinearMap.inr ℝ (X dim) (X dim))
  let C := ContinuousLinearMap.compL ℝ (X dim) (X dim) (X dim)
  let B := 1+6*G*VE^3+8*‖C‖*(6*‖J‖*V*I^3)*A
  have hI : 1 ≤ I := by
    dsimp [I]
    exact (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (zero_le_one.trans hA))
  have hVE : 1 ≤ VE := by
    dsimp only [VE]
    calc
      (1:ℝ) ≤ 6*1*1^3 := by norm_num
      _ ≤ 6*V*I^3 := by gcongr
  have hB : 1 ≤ B := by
    dsimp [B]
    exact (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))
  refine ⟨B,hB,?_⟩
  intro d y a v U P ha hv hU hP hb
  obtain ⟨hE,hg,hEj,hgj⟩ := hb
  let x : CenterParameters dim := (0,v)
  let D := affineNormalInput y a U P
  let F := affineCenterFrame U P
  let Z := d.expMap ∘ D
  let W := d.g₁ ∘ Z
  let J₀ : X dim × X dim → FrameOperator dim := J ∘ fderiv ℝ d.expMap
  let M := J₀ ∘ D
  let T (p : CenterParameters dim) := C (M p) (F p)
  have hx : D x = (y,U v) := by simp [D,x,affineNormalInput,affineCenterFrame]
  have hD : ContDiffAt ℝ ∞ D x := (contDiff_affineNormalInput y a U P).contDiffAt
  have hE' : ContDiffAt ℝ ∞ d.expMap (D x) := by rwa [hx]
  have hZ : ContDiffAt ℝ ∞ Z x := hE'.comp x hD
  have hF : ContDiffAt ℝ ∞ F x := (contDiff_affineCenterFrame U P).contDiffAt
  have hW : ContDiffAt ℝ ∞ W x :=
    (show ContDiffAt ℝ ∞ d.g₁ (Z x) by rw [show Z x = d.expMap (y,U v) from congrArg d.expMap hx]; exact hg).comp x hZ
  have hJ₀ : ContDiffAt ℝ ∞ J₀ (D x) := J.contDiff.contDiffAt.comp _ (hE'.fderiv_right (by simp))
  have hM : ContDiffAt ℝ ∞ M x := hJ₀.comp x hD
  have hT : ContDiffAt ℝ ∞ T x := (C.contDiff.contDiffAt.comp _ hM).clm_apply hF
  refine ⟨hW.prodMk hT,?_⟩
  have hDj (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) : ‖iteratedFDeriv ℝ j D x‖ ≤ I :=
    (norm_iteratedFDeriv_affineNormalInput_le y a v U P A hA ha hv hU hP j hj hj3).trans
      (by dsimp [I]; linarith)
  have hZj (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) : ‖iteratedFDeriv ℝ j Z x‖ ≤ VE := by
    let LE (z : X dim × X dim) := d.expMap z-d.expMap (D x)
    have hLE : ContDiffAt ℝ ∞ LE (D x) := hE'.sub contDiffAt_const
    have hJet (k : ℕ) (hk : 1 ≤ k) :
        iteratedFDeriv ℝ k LE = iteratedFDeriv ℝ k d.expMap := by
      obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      funext w
      rw [iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right]
      simp only [LE,fderiv_sub_const]
    have hJetComp : iteratedFDeriv ℝ j (LE ∘ D) = iteratedFDeriv ℝ j Z := by
      obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      change iteratedFDeriv ℝ (l+1) (fun z => Z z-d.expMap (D x)) = _
      funext w
      rw [iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right]
      simp only [fderiv_sub_const]
    rw [← hJetComp]
    refine norm_iteratedFDeriv_comp_three_envelope D LE x hD hLE V I
      (zero_le_one.trans hV) hI (fun k hk => ?_) hDj j hj3
    by_cases hk0 : k = 0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,LE,sub_self,norm_zero] using zero_le_one.trans hV
    · rw [hJet k (by omega),hx]
      exact hEj k (by omega) (by omega)
  have hWj (j : ℕ) (hj : j ≤ 3) : ‖iteratedFDeriv ℝ j W x‖ ≤ 6*G*VE^3 := by
    have hZx : Z x = d.expMap (y,U v) := congrArg d.expMap hx
    exact norm_iteratedFDeriv_comp_three_envelope Z d.g₁ x hZ (hZx ▸ hg) G VE hG hVE
      (fun k hk => by rw [hZx]; exact hgj k hk) hZj j hj
  have hJj (k : ℕ) (hk : k ≤ 3) : ‖iteratedFDeriv ℝ k J₀ (D x)‖ ≤ ‖J‖*V := by
    have h := J.norm_iteratedFDeriv_comp_left
      (hE'.fderiv_right (m:=∞) (by simp)) (n:=k) (by simp)
    rw [norm_iteratedFDeriv_fderiv,hx] at h
    rw [hx]
    exact h.trans (mul_le_mul_of_nonneg_left (hEj (k+1) (by omega) (by omega)) (norm_nonneg _))
  have hMj (j : ℕ) (hj : j ≤ 3) : ‖iteratedFDeriv ℝ j M x‖ ≤ 6*‖J‖*V*I^3 := by
    have h := norm_iteratedFDeriv_comp_three_envelope D J₀ x hD hJ₀ (‖J‖*V) I
      (by positivity) hI hJj hDj j hj
    exact h.trans_eq (by ring)
  intro j hj
  have hTj := norm_iteratedFDeriv_bilinear_envelope_at C M F x j hM hF
    (6*‖J‖*V*I^3) A (by positivity) (zero_le_one.trans hA)
    (fun k hk => hMj k (hk.trans hj))
    (fun k _ => norm_iteratedFDeriv_affineCenterFrame_le U P v k A hU hP)
  have hPow : (2:ℝ)^j ≤ 8 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj).trans_eq (by norm_num)
  have hTj' : ‖iteratedFDeriv ℝ j T x‖ ≤ 8*‖C‖*(6*‖J‖*V*I^3)*A :=
    hTj.trans (by gcongr)
  change ‖iteratedFDeriv ℝ j (fun p => (W p,T p)) x‖ ≤ B
  exact (norm_iteratedFDeriv_prod_envelope_at W T x j hW hT (hWj j hj) hTj').trans
    (by dsimp [B]; have h₀ : 0 ≤ 6*G*VE^3 := by positivity
        have h₁ : 0 ≤ 8*‖C‖*(6*‖J‖*V*I^3)*A := by positivity
        exact max_le (by linarith) (by linarith))

end CalderonN
