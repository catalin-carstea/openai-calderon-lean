module

public import Proof.CalderonN.DifferentiatedFlux

import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

public section

/- The smooth local estimate used for Sobolev representatives. The three
   dimensional H² estimate in the release is replaced by the compact
   point bound with one derivative per coordinate. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff ENNReal

namespace CalderonN
open Elliptic
variable {n : ℕ}

theorem wordDeriv_eq_iteratedFDeriv (w : List (I n)) {f : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : X n) :
    wordDeriv w f x = iteratedFDeriv ℝ w.length f x (fun j => axis (w.get j)) := by
  induction w generalizing x with
  | nil => simp [wordDeriv, iteratedFDeriv_zero_apply]
  | cons i w ih =>
      have hsmooth : ContDiff ℝ ∞ (iteratedFDeriv ℝ w.length f) :=
        hf.iteratedFDeriv_right (by simp)
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length f) x :=
        (hsmooth.differentiable (by simp)) x
      change wordDeriv (i :: w) f x = iteratedFDeriv ℝ (w.length + 1) f x
        (fun j : Fin (w.length + 1) => axis ((i :: w).get j))
      have hargs :
          (fun j : Fin (w.length + 1) => axis ((i :: w).get j)) =
            Fin.cons (axis i) (fun j => axis (w.get j)) := by
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · simp only [Fin.cons_succ, List.get_cons_succ']
      rw [hargs, hdiff.iteratedFDeriv_succ_apply_left', Fin.tail_cons, Fin.cons_zero]
      have hfun : wordDeriv w f =
          fun y => iteratedFDeriv ℝ w.length f y (fun j => axis (w.get j)) := funext ih
      rw [wordDeriv, hfun]
      rfl

theorem abs_wordDeriv_le_norm_iteratedFDeriv (w : List (I n)) {f : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : X n) :
    |wordDeriv w f x| ≤ ‖iteratedFDeriv ℝ w.length f x‖ := by
  rw [wordDeriv_eq_iteratedFDeriv w hf, ← Real.norm_eq_abs]
  simpa [axis, EuclideanSpace.single] using
    (iteratedFDeriv ℝ w.length f x).le_opNorm (fun j => axis (w.get j))

set_option maxHeartbeats 1300000 in
/-- A uniform point bound from squared L² estimates through order n on a
    Euclidean ball. The same constant works for real normed codomains. -/
theorem exists_norm_le_ball_L2_of_iterated_bounds (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
        (f : X n → F), ContDiff ℝ ∞ f → ∀ (y : X n) (M : ℝ), 0 ≤ M →
        (∀ j ≤ n, (∫ z in ball y r, ‖iteratedFDeriv ℝ j f z‖ ^ 2) ≤ M ^ 2) →
        ‖f y‖ ≤ C * M := by
  let B := ball (0 : X n) r
  obtain ⟨χ,hχ,hχK,hχB,hχ0⟩ := exists_plateau_cutoff (isOpen_ball : IsOpen B)
    (isCompact_singleton (x := (0 : X n))) (singleton_subset_iff.mpr (mem_ball_self hr))
  let K := tsupport χ
  let w := fullCoordinateWord n
  obtain ⟨A,hA,hCut⟩ := exists_cutoff_word_energy_constant hχK hχ w
  have hw : w.length = n := by simp [w, fullCoordinateWord]
  refine ⟨Real.sqrt ((volume : Measure (X n)).real K) * Real.sqrt A, by positivity,
    fun {F} _ _ f hf y M hM hJets => ?_⟩
  by_cases hfy : ‖f y‖ = 0
  · rw [hfy]
    positivity
  obtain ⟨ℓ,hℓ,hval⟩ := exists_dual_vector ℝ (f y) hfy
  let F₀ (z : X n) := f (y + z)
  let g (z : X n) := ℓ (F₀ z)
  have hF₀ : ContDiff ℝ ∞ F₀ := hf.comp (contDiff_const.add contDiff_id)
  have hg : ContDiff ℝ ∞ g := ℓ.contDiff.comp hF₀
  have hnorm (v : List (I n)) (z : X n) :
      |wordDeriv v g z| ≤ ‖iteratedFDeriv ℝ v.length f (y+z)‖ := by
    refine (abs_wordDeriv_le_norm_iteratedFDeriv v hg z).trans ?_
    have hh := ℓ.norm_iteratedFDeriv_comp_left (n := v.length) (x := z) hF₀.contDiffAt (by simp)
    rw [hℓ, one_mul] at hh
    change ‖iteratedFDeriv ℝ v.length g z‖ ≤ _ at hh
    rw [show iteratedFDeriv ℝ v.length F₀ z = iteratedFDeriv ℝ v.length f (y+z) from
      iteratedFDeriv_comp_add_left v.length y z] at hh
    exact hh
  have hE (v : List (I n)) (hv : v.length ≤ w.length) :
      (∫ z in K, wordDeriv v g z ^ 2) ≤ M ^ 2 := by
    let Fv (z : X n) := ‖iteratedFDeriv ℝ v.length f (y+z)‖ ^ 2
    have hFv : Continuous Fv := ((hf.continuous_iteratedFDeriv (by simp)).comp
      (continuous_const.add continuous_id)).norm.pow 2
    have hFB : IntegrableOn Fv B := (hFv.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : X n) r)).mono_set ball_subset_closedBall
    calc
      _ ≤ ∫ z in K, Fv z := by
        apply integral_mono
          (((contDiff_wordDeriv v hg).continuous.pow 2).continuousOn.integrableOn_compact hχK)
          (hFB.mono_set hχB)
        intro z
        change wordDeriv v g z ^ 2 ≤ ‖iteratedFDeriv ℝ v.length f (y+z)‖ ^ 2
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hnorm v z) 2
      _ ≤ ∫ z in B, Fv z := setIntegral_mono_set hFB (ae_of_all _ fun z => sq_nonneg _) hχB.eventuallyLE
      _ = ∫ z in ball y r, ‖iteratedFDeriv ℝ v.length f z‖ ^ 2 := by
        have ht := (measurePreserving_add_left (volume : Measure (X n)) y).setIntegral_preimage_emb
          (Homeomorph.addLeft y).measurableEmbedding
          (fun z => ‖iteratedFDeriv ℝ v.length f z‖ ^ 2) (ball y r)
        have he : (fun z : X n => y+z) ⁻¹' ball y r = B := by
          ext z
          simp [B, mem_ball, dist_eq_norm]
        rwa [he] at ht
      _ ≤ M ^ 2 := hJets v.length (hv.trans_eq hw)
  let t (z : X n) := χ z * g z
  have ht : ContDiff ℝ ∞ t := hχ.mul hg
  have hts : tsupport t ⊆ K := tsupport_mul_subset_left
  have hp := abs_apply_le_volume_sqrt_word ht hχK hts (0 : X n)
  have hCut' := hCut g (M ^ 2) hg hE
  have hzero : χ (0 : X n) = 1 := (hχ0 0 (mem_singleton 0)).eq_of_nhds
  have ht0 : t 0 = ‖f y‖ := by simpa [t, g, F₀, hzero] using hval
  rw [ht0, abs_of_nonneg (norm_nonneg _)] at hp
  refine hp.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCut') (Real.sqrt_nonneg _)).trans_eq ?_)
  rw [Real.sqrt_mul hA, Real.sqrt_sq hM, mul_assoc]

end CalderonN
