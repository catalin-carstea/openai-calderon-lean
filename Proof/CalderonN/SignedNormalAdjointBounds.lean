module

public import Proof.CalderonN.SignedNormalAdjoint

import Mathlib.Tactic

/-! Adapted from `SignedNormalAdjointBounds` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1800000

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

variable {γ g : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}

/-- At any compact family of admissible signed parameters, the first
adjoint and the second-order remainder have common first-derivative bounds. -/
theorem exists_uniform_signedNormalAdjoint_bounds
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => γ p.1 p.2 i j))
    (hγPos : ∀ lam y, (γ lam y).PosDef)
    (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => g p.1 p.2 i j))
    (hgPos : ∀ lam y, (g lam y).PosDef)
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i))
    {C : Set (SignedNormalParameter dim)} (hC : IsCompact C)
    (hAdmissible : C ×ˢ closedBall (0 : (X dim)) 1 ⊆ signedNormalNondegenerate E e) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ j, smoothNear (signedNormalFirstAdjoint γ g E e j) (C ×ˢ (standardSphere dim))) ∧
      (∀ i j, smoothNear (signedNormalAdjointRemainder γ g E e i j) (C ×ˢ (standardSphere dim))) ∧
      ∀ q ∈ C ×ˢ (standardSphere dim), ∀ i j,
        ‖signedNormalFirstAdjoint γ g E e j q‖ ≤ B ∧
        ‖fderiv ℝ (signedNormalFirstAdjoint γ g E e j) q‖ ≤ B ∧
        ‖signedNormalAdjointRemainder γ g E e i j q‖ ≤ B ∧
        ‖fderiv ℝ (signedNormalAdjointRemainder γ g E e i j) q‖ ≤ B := by
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  let K := C ×ˢ (standardSphere dim)
  let a := signedNormalFirstAdjoint γ g E e
  let d := signedNormalAdjointRemainder γ g E e
  have hN : IsOpen N := isClosed_singleton.isOpen_compl
  have hSN : (standardSphere dim) ⊆ N := by
    intro w hw
    change w ≠ 0
    intro hzero
    have hn := mem_sphere_zero_iff_norm.mp hw
    simp [hzero] at hn
  have hPatch (q : (SignedNormalParameter dim) × (X dim)) (hq : q ∈ K) (i j : (I dim)) :
      ∃ W : Set ((SignedNormalParameter dim) × (X dim)), IsOpen W ∧ q ∈ W ∧
        ContDiffOn ℝ ∞ (a j) W ∧ ContDiffOn ℝ ∞ (d i j) W := by
    have hp : {q.1} ×ˢ closedBall (0 : (X dim)) 1 ⊆ signedNormalNondegenerate E e := by
      intro z hz
      exact hAdmissible ⟨mem_singleton_iff.mp hz.1 ▸ hq.1,hz.2⟩
    obtain ⟨W,hW,hqW,ha,hd⟩ := exists_smooth_signedNormalAdjoints hγ hγPos hg hgPos hE he q.1 hp i j
    exact ⟨W ×ˢ N,hW.prod hN,⟨hqW,hSN hq.2⟩,ha,hd⟩
  have ha (j : (I dim)) : smoothNear (a j) K :=
    smoothNear_of_open_cover fun q hq => by
      obtain ⟨W,hW,hqW,ha,_⟩ := hPatch q hq 0 j
      exact ⟨W,hW,hqW,ha⟩
  have hd (i j : (I dim)) : smoothNear (d i j) K :=
    smoothNear_of_open_cover fun q hq => by
      obtain ⟨W,hW,hqW,_,hd⟩ := hPatch q hq i j
      exact ⟨W,hW,hqW,hd⟩
  have hNorm {f : (SignedNormalParameter dim) × (X dim) → ℝ} (hf : smoothNear f K) :
      ContinuousOn (fun q => ‖f q‖) K ∧ ContinuousOn (fun q => ‖fderiv ℝ f q‖) K := by
    obtain ⟨W,hW,hKW,hf⟩ := hf
    exact ⟨hf.continuousOn.norm.mono hKW,
      ((hf.fderiv_of_isOpen (m := ∞) hW (by simp)).continuousOn.norm).mono hKW⟩
  let H (q : (SignedNormalParameter dim) × (X dim)) (i j : (I dim)) :=
    ‖a j q‖ + ‖fderiv ℝ (a j) q‖ + ‖d i j q‖ + ‖fderiv ℝ (d i j) q‖
  let F (q : (SignedNormalParameter dim) × (X dim)) := ∑ i : (I dim), ∑ j : (I dim), H q i j
  have hF : ContinuousOn F K :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((((hNorm (ha j)).1.add (hNorm (ha j)).2).add (hNorm (hd i j)).1).add (hNorm (hd i j)).2)
  obtain ⟨B,hB⟩ := (hC.prod (isCompact_sphere (0 : (X dim)) 1)).exists_bound_of_continuousOn hF
  have hH (q : (SignedNormalParameter dim) × (X dim)) (i j : (I dim)) : 0 ≤ H q i j := by dsimp only [H]; positivity
  refine ⟨max 0 B,le_max_left _ _,ha,hd,?_⟩
  intro q hq i j
  have hj : H q i j ≤ ∑ k, H q i k :=
    Finset.single_le_sum (fun k _ => hH q i k) (Finset.mem_univ j)
  have hi : (∑ k, H q i k) ≤ F q :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun k _ => hH q l k) (Finset.mem_univ i)
  have h := hj.trans (hi.trans ((le_abs_self _).trans
    (((hB q hq).trans (le_max_right 0 B)) : ‖F q‖ ≤ max 0 B)))
  dsimp only [H] at h
  have h₁ := norm_nonneg (a j q)
  have h₂ := norm_nonneg (fderiv ℝ (a j) q)
  have h₃ := norm_nonneg (d i j q)
  have h₄ := norm_nonneg (fderiv ℝ (d i j) q)
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- A first-derivative bound along the signed-radius segment gives the
required linear error at any fixed center, radius gradient and angle. -/
theorem signedNormal_radius_difference_le {f : (SignedNormalParameter dim) × (X dim) → ℝ}
    {lam : ℝ} {y : (X dim)} {b : (I dim) → ℝ} {w : (X dim)} {s B : ℝ} (hs : 0 ≤ s)
    (hf : ∀ t ∈ Icc 0 s, DifferentiableAt ℝ f ((lam,(y,(t,b))),w))
    (hB : ∀ t ∈ Icc 0 s, ‖fderiv ℝ f ((lam,(y,(t,b))),w)‖ ≤ B) :
    ‖f ((lam,(y,(s,b))),w) - f ((lam,(y,(0,b))),w)‖ ≤ B*s := by
  let j (t : ℝ) : (SignedNormalParameter dim) × (X dim) := ((lam,(y,(t,b))),w)
  let v : (SignedNormalParameter dim) × (X dim) := ((0,(0,(1,0))),0)
  have hJ (t : ℝ) : HasDerivAt j v t :=
    hasDerivAt_const t _ |>.prodMk
      ((hasDerivAt_const t _).prodMk (((hasDerivAt_id t).prodMk (hasDerivAt_const t _)))) |>.prodMk
        (hasDerivAt_const t _)
  have hv : ‖v‖ = 1 := by simp [v,Prod.norm_def]
  have hF (t : ℝ) (ht : t ∈ Icc 0 s) : HasDerivAt (f ∘ j) (fderiv ℝ f (j t) v) t :=
    (hf t ht).hasFDerivAt.comp_hasDerivAt t (hJ t)
  have hG : ∀ t ∈ Icc 0 s, ‖fderiv ℝ (f ∘ j) t‖ ≤ B := by
    intro t ht
    have hd := (hF t ht).hasFDerivAt.fderiv
    rw [hd]
    change ‖(ContinuousLinearMap.id ℝ ℝ).smulRight ((fderiv ℝ f (j t)) v)‖ ≤ B
    rw [ContinuousLinearMap.norm_smulRight_apply,ContinuousLinearMap.norm_id,one_mul]
    exact ((fderiv ℝ f (j t)).le_opNorm v).trans (by rw [hv,mul_one]; exact hB t ht)
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun t ht => (hF t ht).differentiableAt) hG (convex_Icc (0 : ℝ) s)
    ⟨le_rfl,hs⟩ ⟨hs,le_rfl⟩
  simpa only [Function.comp_apply,j,sub_zero,Real.norm_eq_abs,abs_of_nonneg hs] using h

end CalderonN
