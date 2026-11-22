module

public import Proof.Manuscript.AnnulusJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators

namespace CalderonPaper

variable {A B E V : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem iteratedFDeriv_comp_right_at {X W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : X →L[ℝ] A) {f : A → W} (x : X) (l : ℕ)
    (hf : ContDiffAt ℝ ∞ f (g x)) :
    iteratedFDeriv ℝ l (f ∘ g) x =
      (iteratedFDeriv ℝ l f (g x)).compContinuousLinearMap (fun _ => g) := by
  have hf_l := hf.of_le (show (l : ℕ∞ω) ≤ ∞ by simp)
  obtain ⟨U, hU, hx, hdiff⟩ := hf_l.contDiffOn' le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ (g x)), univ_inter] at hdiff
  have hpre := hU.preimage g.continuous
  have hcomp := g.iteratedFDerivWithin_comp_right hdiff hU.uniqueDiffOn (x := x)
    hpre.uniqueDiffOn hx (le_rfl : (l : ℕ∞ω) ≤ l)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn
      (hf_l.comp x g.contDiff.contDiffAt) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hf_l hx] at hcomp
  exact hcomp

private theorem iteratedFDeriv_horizontal_slice {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : A × B → W} {a : A} {b : B}
    (hg : ContDiffAt ℝ ∞ g (a, b)) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y : A => g (y, b)) a =
      (iteratedFDeriv ℝ k g (a, b)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ A B) := by
  let L := ContinuousLinearMap.inl ℝ A B
  let h (z : A × B) := g (z + (0, b))
  have hL : ContDiffAt ℝ ∞ h (L a) := by
    have hd : (L a) + ((0 : A), b) = (a, b) := by simp [L]
    rw [← hd] at hg
    exact hg.comp (L a) (by fun_prop)
  have he := iteratedFDeriv_comp_right_at L a k hL
  rw [show iteratedFDeriv ℝ k h (L a) = iteratedFDeriv ℝ k g (a, b) by
    unfold h
    rw [iteratedFDeriv_comp_add_right]
    simp [L]] at he
  rw [show (fun y : A => g (y, b)) = h ∘ ⇑L by funext y; simp [L, h]]
  exact he

private theorem iteratedFDeriv_vertical_slice {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : A × B → W} {a : A} {b : B}
    (hg : ContDiffAt ℝ ∞ g (a, b)) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y : B => g (a, y)) b =
      (iteratedFDeriv ℝ k g (a, b)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ A B) := by
  let L := ContinuousLinearMap.inr ℝ A B
  let h (z : A × B) := g (z + (a, 0))
  have hL : ContDiffAt ℝ ∞ h (L b) := by
    have hd : (L b) + (a, (0 : B)) = (a, b) := by simp [L]
    rw [← hd] at hg
    exact hg.comp (L b) (by fun_prop)
  have he := iteratedFDeriv_comp_right_at L b k hL
  rw [show iteratedFDeriv ℝ k h (L b) = iteratedFDeriv ℝ k g (a, b) by
    unfold h
    rw [iteratedFDeriv_comp_add_right]
    simp [L]] at he
  rw [show (fun y : B => g (a, y)) = h ∘ ⇑L by funext y; simp [L, h]]
  exact he

/-- The inner and outer arguments of a nested derivative form one list
of directions. The first direction of the outer derivative is prepended. -/
private def mixedDirections {X : Type*} (k : ℕ) (u : Fin k → X) :
    (j : ℕ) → (Fin j → X) → Fin (k+j) → X
  | 0, _ => u
  | j+1, v => Fin.cons (v 0) (mixedDirections k u j (Fin.tail v))

private theorem mixedDirections_prod {X : Type*} [NormedAddCommGroup X]
    (k : ℕ) (u : Fin k → X) (j : ℕ) (v : Fin j → X) :
    (∏ i, ‖mixedDirections k u j v i‖) = (∏ i, ‖v i‖) * (∏ i, ‖u i‖) := by
  induction j with
  | zero => simp [mixedDirections]
  | succ j ih =>
    change (∏ i : Fin (k+j+1), ‖(@Fin.cons (k+j) (fun _ => X) (v 0)
        (mixedDirections k u j (Fin.tail v))) i‖) =
      (∏ i : Fin (j+1), ‖v i‖) * (∏ i, ‖u i‖)
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,ih,mul_assoc,Fin.tail]

private theorem iteratedFDeriv_iterated_apply_at
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → F} (k : ℕ) (u : Fin k → X)
    (j : ℕ) (x : X) (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y) (v : Fin j → X) :
    (iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f) x v) u =
      iteratedFDeriv ℝ (k+j) f x (mixedDirections k u j v) := by
  induction j generalizing x with
  | zero => simp [mixedDirections,iteratedFDeriv_zero_apply]
  | succ j ih =>
    have hF : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ k f) x :=
      hf.self_of_nhds.iteratedFDeriv_right (by simp)
    have hJ : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f)) x :=
      hF.iteratedFDeriv_right (by simp)
    have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f)) x :=
      hJ.differentiableAt (by simp)
    rw [hD.iteratedFDeriv_succ_apply_left']
    have hE : DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ j
        (iteratedFDeriv ℝ k f) y (Fin.tail v)) x :=
      hD.continuousMultilinear_apply_const _
    rw [← fderiv_continuousMultilinear_apply_const_apply hE u (v 0)]
    have hEq : (fun y => (iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f) y (Fin.tail v)) u) =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv ℝ (k+j) f y (mixedDirections k u j (Fin.tail v))) := by
      filter_upwards [eventually_eventually_nhds.mpr hf] with y hy
      exact ih y hy (Fin.tail v)
    rw [hEq.fderiv_eq]
    have hK : DifferentiableAt ℝ (iteratedFDeriv ℝ (k+j) f) x :=
      (hf.self_of_nhds.iteratedFDeriv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hS := hK.iteratedFDeriv_succ_apply_left' (n := k+j)
      (m := @Fin.cons (k+j) (fun _ => X) (v 0) (mixedDirections k u j (Fin.tail v)))
    simpa only [mixedDirections,Fin.tail_cons,Fin.cons_zero,Nat.add_succ] using hS.symm

/-- A higher derivative of the iterated Fréchet derivative is bounded by
the single Fréchet derivative of the sum of the two orders. -/
private theorem norm_iteratedFDeriv_of_iteratedFDeriv_le_at (j k : ℕ)
    {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → F} (x : X)
    (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y) :
    ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f) x‖ ≤ ‖iteratedFDeriv ℝ (j+k) f x‖ := by
  rw [Nat.add_comm j k]
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) ?_
  intro v
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _))) ?_
  intro u
  rw [iteratedFDeriv_iterated_apply_at k u j x hf v,mul_assoc,← mixedDirections_prod]
  exact (iteratedFDeriv ℝ (k+j) f x).le_opNorm _

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting consecutive groups of arguments to the base and angular
coordinate subspaces can only decrease the mixed operator norm. -/
theorem separatedAngularJets_le_joint {f : A × B → E → V} {a : A} {b : B} {ξ : E}
    (hf : ∀ᶠ q : A × B in 𝓝 (a, b),
      ContDiffAt ℝ ∞ (Function.uncurry f) (q, ξ))
    (j k l : ℕ) :
    ‖iteratedFDeriv ℝ j (fun a' => iteratedFDeriv ℝ k
        (fun b' => iteratedFDeriv ℝ l (f (a', b')) ξ) b) a‖ ≤
      ‖angularMixedJet (j + k) l f (a, b) ξ‖ := by
  let g (q : A × B) := iteratedFDeriv ℝ l (f q) ξ
  have hgs : ∀ᶠ q : A × B in 𝓝 (a, b), ContDiffAt ℝ ∞ g q := by
    filter_upwards [hf] with q hq
    have hz : ContDiffAt ℝ ∞ (fun z : (A × B) × E =>
        iteratedFDeriv ℝ l (f z.1) z.2) (q, ξ) :=
      contDiffAt_iteratedFDeriv_snd hq l
    have hs : ContDiffAt ℝ ∞ (fun s : A × B => (s, ξ)) q := by fun_prop
    exact hz.comp q hs
  let R : ((A × B) [×k]→L[ℝ] (E [×l]→L[ℝ] V)) →L[ℝ] (B [×k]→L[ℝ] (E [×l]→L[ℝ] V)) :=
    ContinuousMultilinearMap.compContinuousLinearMapL
    (F := E [×l]→L[ℝ] V) (fun _ : Fin k => ContinuousLinearMap.inr ℝ A B)
  have hR (D : (A × B) [×k]→L[ℝ] (E [×l]→L[ℝ] V)) : ‖R D‖ ≤ ‖D‖ := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le D _).trans ?_
    have hprod : (∏ _ : Fin k, ‖ContinuousLinearMap.inr ℝ A B‖) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ A B)
    exact mul_le_of_le_one_right (norm_nonneg _) hprod
  have hbase : ∀ᶠ y : A in 𝓝 a, (fun y => iteratedFDeriv ℝ k (fun z => g (y, z)) b) y =
      R (iteratedFDeriv ℝ k g (y, b)) := by
    have hnear := (show Continuous (fun y : A => (y, b)) by fun_prop).continuousAt.eventually hgs
    filter_upwards [hnear] with y hy
    exact iteratedFDeriv_vertical_slice hy k
  have hG : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ k g) (a, b) :=
    hgs.self_of_nhds.iteratedFDeriv_right (by simp)
  have hslice := iteratedFDeriv_horizontal_slice hG j
  have hgn : ‖iteratedFDeriv ℝ j (fun y => iteratedFDeriv ℝ k g (y, b)) a‖ ≤
      ‖iteratedFDeriv ℝ (j + k) g (a, b)‖ := by
    rw [hslice]
    apply le_trans _ (norm_iteratedFDeriv_of_iteratedFDeriv_le_at j k (a,b) hgs)
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : (∏ _ : Fin j, ‖ContinuousLinearMap.inl ℝ A B‖) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ A B)
    exact mul_le_of_le_one_right (norm_nonneg _) hprod
  change ‖iteratedFDeriv ℝ j (fun y => iteratedFDeriv ℝ k (fun z => g (y, z)) b) a‖ ≤ _
  have hebase : (fun y => iteratedFDeriv ℝ k (fun z => g (y, z)) b) =ᶠ[𝓝 a]
      (fun y => R (iteratedFDeriv ℝ k g (y, b))) := hbase
  rw [(hebase.iteratedFDeriv ℝ j).eq_of_nhds]
  have hC : ContDiffAt ℝ ↑j (fun y => iteratedFDeriv ℝ k g (y, b)) a :=
    (hG.comp a (by fun_prop)).of_le (by simp)
  have hder := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ) (E := A)
    (F := (A × B) [×k]→L[ℝ] (E [×l]→L[ℝ] V)) (G := B [×k]→L[ℝ] (E [×l]→L[ℝ] V))
    R hC (le_rfl : (j : ℕ∞ω) ≤ j)
  change ‖iteratedFDeriv ℝ j (R ∘ (fun y => iteratedFDeriv ℝ k g (y, b))) a‖ ≤ _
  rw [hder]
  refine (ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) (fun w => ?_)).trans hgn
  exact (hR _).trans (ContinuousMultilinearMap.le_opNorm _ _)

/-- Rescaling the base while preserving the angular variables recovers
one power of the base scale for each base derivative. -/
theorem separatedAngularJets_le_recentered_joint {f : A × B → E → V} {a : A} {b : B} {ξ : E}
    {β : ℝ} (hβ : 0 < β) (j k l : ℕ)
    (hSmooth : ∀ᶠ q : A × B in 𝓝 ((0 : A), b),
      ContDiffAt ℝ ∞ (fun r : (A × B) × E => f (a + β⁻¹ • r.1.1, r.1.2) r.2) (q, ξ)) :
    ‖iteratedFDeriv ℝ j (fun a' => iteratedFDeriv ℝ k
        (fun b' => iteratedFDeriv ℝ l (f (a', b')) ξ) b) a‖ ≤
      β^j * ‖angularMixedJet (j+k) l (fun q => f (a + β⁻¹ • q.1, q.2)) (0,b) ξ‖ := by
  let F (x : A) := iteratedFDeriv ℝ k (fun z => iteratedFDeriv ℝ l (f (x,z)) ξ) b
  let G (x : A) := F (x+a)
  let L : A ≃L[ℝ] A := ContinuousLinearEquiv.smulLeft (M₁ := A) (Units.mk0 β⁻¹ (inv_ne_zero hβ.ne'))
  have hEq : (fun x => F (a+β⁻¹ • x)) = G ∘ L := by
    funext x
    simp [L,G,Function.comp_def,add_comm a]
  have hJet := L.iteratedFDerivWithin_comp_right G (s := univ) uniqueDiffOn_univ
    (x := (0 : A)) (mem_univ _) j
  simp only [preimage_univ,iteratedFDerivWithin_univ,map_zero] at hJet
  have hScale : iteratedFDeriv ℝ j (fun x => F (a+β⁻¹ • x)) 0 =
      (β⁻¹)^j • iteratedFDeriv ℝ j F a := by
    rw [hEq,hJet, show iteratedFDeriv ℝ j G 0 = iteratedFDeriv ℝ j F a by
      unfold G
      rw [iteratedFDeriv_comp_add_right,zero_add]]
    ext m
    simp [L,ContinuousMultilinearMap.map_smul_univ (c := fun _ => β⁻¹)]
  have hJoint := separatedAngularJets_le_joint (f := fun q => f (a+β⁻¹ • q.1,q.2))
    (a := (0 : A)) (b := b) (ξ := ξ) hSmooth j k l
  change ‖iteratedFDeriv ℝ j (fun x => F (a+β⁻¹ • x)) 0‖ ≤ _ at hJoint
  rw [hScale,norm_smul,Real.norm_of_nonneg (by positivity)] at hJoint
  change ‖iteratedFDeriv ℝ j F a‖ ≤ _
  calc
    _ = β^j * ((β⁻¹)^j * ‖iteratedFDeriv ℝ j F a‖) := by
      rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ hβ.ne',one_pow,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hJoint (pow_nonneg hβ.le _)

end CalderonPaper
