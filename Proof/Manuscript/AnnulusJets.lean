module

public import Proof.Manuscript.AnnulusExpansion
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff

namespace CalderonPaper

variable {P E V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The mixed Fréchet jet, with derivatives in the covector taken first. -/
@[expose] def angularMixedJet (j l : ℕ) (f : P → E → V) (p : P) (ξ : E) :=
  iteratedFDeriv ℝ j (fun p' => iteratedFDeriv ℝ l (f p') ξ) p

/-- Remove the first N homogeneous terms outside the zero-frequency cutoff. -/
@[expose] def cutoffAngularRemainder (a : P → E → V) (b : ℕ → P → E → V)
    (χ : E → ℝ) (N : ℕ) (p : P) (ξ : E) : V :=
  a p ξ - χ ξ • ∑ k ∈ Finset.range N, homogeneousAngularCoefficient b k p ξ

private theorem iteratedFDeriv_smul_left {X W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : X → W) (j : ℕ) (x : X) {c : ℝ} (hc : c ≠ 0) :
    iteratedFDeriv ℝ j (fun y => c • f y) x = c • iteratedFDeriv ℝ j f x := by
  let L : W ≃L[ℝ] W := ContinuousLinearEquiv.smulLeft (M₁ := W) (Units.mk0 c hc)
  have heq := L.iteratedFDeriv_comp_left (f := f) (x := x) (i := j)
  ext v
  simpa [L, Function.comp_def] using congrArg (fun u => u v) heq

private theorem iteratedFDeriv_smul_right (f : E → V) (l : ℕ) (ξ : E)
    {h : ℝ} (hh : h ≠ 0) :
    iteratedFDeriv ℝ l (fun η => f (h • η)) ξ =
      h ^ l • iteratedFDeriv ℝ l f (h • ξ) := by
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (M₁ := E) (Units.mk0 h hh)
  have hcomp := L.iteratedFDerivWithin_comp_right f (s := univ) uniqueDiffOn_univ
    (x := ξ) (mem_univ _) l
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hcomp
  ext v
  have := congrArg (fun u => u v) hcomp
  simpa [L, Function.comp_def, ContinuousMultilinearMap.map_smul_univ (c := fun _ => h)]
    using this

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
private theorem cutoffAngularRemainder_scale
    (a : P → E → V) (b : ℕ → P → E → V) (χ : E → ℝ) (N : ℕ)
    (p : P) (ξ : E) {h : ℝ} (hh : 0 < h) (hχ : χ ξ = 1)
    (hb : ∀ k, b k p (h • ξ) = homogeneousAngularCoefficient b k p (h • ξ)) :
    cutoffAngularRemainder a b χ N p ξ =
      h⁻¹ • normalizedAnnulusRemainder a b N h p (h • ξ) := by
  unfold cutoffAngularRemainder normalizedAnnulusRemainder
  rw [hχ, one_smul, smul_smul, inv_mul_cancel₀ hh.ne', one_smul, smul_sub,
    smul_smul, inv_mul_cancel₀ hh.ne', one_smul, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [hb, homogeneousAngularCoefficient_smul _ _ _ _ _ hh]
  simp only [smul_smul]
  rw [show h⁻¹ * (h ^ k * angularSymbolScale k h) = 1 by
    rw [angularSymbolScale, inv_pow]
    calc
      h⁻¹ * (h ^ k * (h * (h ^ k)⁻¹)) =
          (h⁻¹ * h) * (h ^ k * (h ^ k)⁻¹) := by ring
      _ = 1 := by simp [hh.ne']]
  rw [one_smul]

/-- At a large covector, freeze its reciprocal length before differentiating.
The derivative gain is the exact power contributed by the dilated covector. -/
theorem angularMixedJet_cutoffAngularRemainder
    (a : P → E → V) (b : ℕ → P → E → V) (χ : E → ℝ)
    {U : Set P} (hU : IsOpen U) {p : P} (hp : p ∈ U) (ξ : E)
    (hξ : 2 < ‖ξ‖) (hχ : ∀ η : E, 2 ≤ ‖η‖ → χ η = 1)
    (hb : ∀ q ∈ U, ∀ η : E, (1 / 2 : ℝ) ≤ ‖η‖ → ‖η‖ ≤ 2 →
      ∀ k, b k q η = homogeneousAngularCoefficient b k q η)
    (N j l : ℕ) :
    let h := ‖ξ‖⁻¹
    angularMixedJet j l (cutoffAngularRemainder a b χ N) p ξ =
      (h⁻¹ * h ^ l) • angularMixedJet j l (normalizedAnnulusRemainder a b N h) p (h • ξ) := by
  let h := ‖ξ‖⁻¹
  have hξ0 : 0 < ‖ξ‖ := by linarith
  have hh : 0 < h := inv_pos.mpr hξ0
  have hnorm : ‖h • ξ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact inv_mul_cancel₀ hξ0.ne'
  have hf : Continuous (fun η : E => ‖h • η‖) := (continuous_const.smul continuous_id).norm
  have hlarge : ∀ᶠ η : E in 𝓝 ξ, 2 < ‖η‖ :=
    continuous_norm.continuousAt.eventually (eventually_gt_nhds hξ)
  have hlo : ∀ᶠ η : E in 𝓝 ξ, (1 / 2 : ℝ) < ‖h • η‖ :=
    hf.continuousAt.eventually (eventually_gt_nhds (by
      change (1 / 2 : ℝ) < ‖h • ξ‖
      rw [hnorm]
      norm_num))
  have hhi : ∀ᶠ η : E in 𝓝 ξ, ‖h • η‖ < 2 :=
    hf.continuousAt.eventually (eventually_lt_nhds (by
      change ‖h • ξ‖ < 2
      rw [hnorm]
      norm_num))
  have hbase : (fun q => iteratedFDeriv ℝ l (cutoffAngularRemainder a b χ N q) ξ)
      =ᶠ[𝓝 p] (fun q => (h⁻¹ * h ^ l) •
        iteratedFDeriv ℝ l (normalizedAnnulusRemainder a b N h q) (h • ξ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    have hfreq : cutoffAngularRemainder a b χ N q =ᶠ[𝓝 ξ]
        (fun η => h⁻¹ • normalizedAnnulusRemainder a b N h q (h • η)) := by
      filter_upwards [hlarge, hlo, hhi] with η hη hηlo hηhi
      exact cutoffAngularRemainder_scale a b χ N q η hh (hχ _ hη.le)
        (hb q hq _ hηlo.le hηhi.le)
    rw [(hfreq.iteratedFDeriv ℝ l).eq_of_nhds,
      iteratedFDeriv_smul_left _ _ _ (inv_ne_zero hh.ne'),
      iteratedFDeriv_smul_right _ _ _ hh.ne', smul_smul]
  change angularMixedJet j l (cutoffAngularRemainder a b χ N) p ξ = _
  unfold angularMixedJet
  rw [(hbase.iteratedFDeriv ℝ j).eq_of_nhds,
    iteratedFDeriv_smul_left _ _ _ (mul_ne_zero (inv_ne_zero hh.ne') (pow_ne_zero _ hh.ne'))]

/-- The radial factor has the degree of the corresponding homogeneous term. -/
theorem angularSymbolScale_eq_rpow (k : ℕ) {r : ℝ} (hr : 0 < r) :
    angularSymbolScale k r = r ^ ((1 : ℝ) - k) := by
  rw [Real.rpow_sub hr, Real.rpow_one, Real.rpow_natCast, angularSymbolScale, inv_pow,
    div_eq_mul_inv]

theorem angularMixedJet_cutoffAngularRemainder_bound
    (a : P → E → V) (b : ℕ → P → E → V) (χ : E → ℝ)
    {U : Set P} (hU : IsOpen U) {p : P} (hp : p ∈ U) (ξ : E)
    (hξ : 2 < ‖ξ‖) (hχ : ∀ η : E, 2 ≤ ‖η‖ → χ η = 1)
    (hb : ∀ q ∈ U, ∀ η : E, (1 / 2 : ℝ) ≤ ‖η‖ → ‖η‖ ≤ 2 →
      ∀ k, b k q η = homogeneousAngularCoefficient b k q η)
    (N j l : ℕ) (C : ℝ)
    (hbound : ∀ h ∈ Ioc (0 : ℝ) 1, ∀ η : E, ‖η‖ = 1 →
      ‖angularMixedJet j l (normalizedAnnulusRemainder a b N h) p η‖ ≤ C * h ^ N) :
    ‖angularMixedJet j l (cutoffAngularRemainder a b χ N) p ξ‖ ≤
      C * ‖ξ‖ ^ ((1 : ℝ) - N - l) := by
  let h := ‖ξ‖⁻¹
  have hξ0 : 0 < ‖ξ‖ := by linarith
  have hh : 0 < h := inv_pos.mpr hξ0
  have hh1 : h ≤ 1 := (inv_le_one₀ hξ0).mpr (by linarith)
  have hnorm : ‖h • ξ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact inv_mul_cancel₀ hξ0.ne'
  rw [angularMixedJet_cutoffAngularRemainder a b χ hU hp ξ hξ hχ hb N j l]
  change ‖(h⁻¹ * h ^ l) •
    angularMixedJet j l (normalizedAnnulusRemainder a b N h) p (h • ξ)‖ ≤ _
  have hpos : 0 < h⁻¹ * h ^ l := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
  refine (mul_le_mul_of_nonneg_left (hbound h ⟨hh, hh1⟩ _ hnorm) hpos.le).trans_eq ?_
  rw [show (1 : ℝ) - N - l = 1 - ((N + l : ℕ) : ℝ) by push_cast; ring,
    ← angularSymbolScale_eq_rpow (N + l) hξ0, angularSymbolScale, pow_add]
  have h_inv : h⁻¹ = ‖ξ‖ := inv_inv _
  rw [← h_inv, inv_inv]
  ring

/-- Differentiating in the second variable preserves joint smoothness. -/
theorem contDiffAt_iteratedFDeriv_snd {A B W : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : A → B → W} {q : A × B}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) q) (l : ℕ) :
    ContDiffAt ℝ ∞ (fun z : A × B => iteratedFDeriv ℝ l (f z.1) z.2) q := by
  induction l with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact hf.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ B W).symm : W →L[ℝ] B [×0]→L[ℝ] W)
  | succ l ih =>
    let F (z : A × B) (w : B) := iteratedFDeriv ℝ l (f z.1) w
    have hF : ContDiffAt ℝ ∞ (Function.uncurry F) (q, q.2) :=
      ih.comp (q, q.2) (by
        change ContDiffAt ℝ ∞ (fun z : (A × B) × B => (z.1.1, z.2)) (q, q.2)
        fun_prop)
    have hD := hF.fderiv (g := Prod.snd) contDiffAt_snd (m := ∞) (by simp)
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (l + 1) => B) W).symm
    have hL := hD.continuousLinearMap_comp (L : _ →L[ℝ] B [×(l + 1)]→L[ℝ] W)
    convert hL using 1
    funext z
    rw [iteratedFDeriv_succ_eq_comp_left]
    rfl

/-- A jointly smooth family has jointly continuous mixed jets. -/
theorem contDiffAt_angularMixedJet
    {f : P → E → V} {q : P × E}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) q) (j l : ℕ) :
    ContDiffAt ℝ ∞ (Function.uncurry (angularMixedJet j l f)) q := by
  have hinner := contDiffAt_iteratedFDeriv_snd hf l
  have hswap : ContDiffAt ℝ ∞
      (Function.uncurry (fun (ξ : E) (p : P) => iteratedFDeriv ℝ l (f p) ξ)) q.swap := by
    have hs : ContDiffAt ℝ ∞ (fun s : E × P => (s.2, s.1)) q.swap := by fun_prop
    have hz := hinner.comp q.swap hs
    convert hz using 1
    funext z
    rfl
  have houter := contDiffAt_iteratedFDeriv_snd hswap j
  have hs : ContDiffAt ℝ ∞ (fun s : P × E => (s.2, s.1)) q := by fun_prop
  have hz := houter.comp q hs
  convert hz using 1
  funext z
  rfl

end CalderonPaper
