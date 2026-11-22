module

public import Proof.CalderonN.ParametricBallConormal
public import Proof.CalderonN.MixedSliceJets

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Adapted from `UniformConormalCalculus` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 7800000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

@[expose] def radialBallConormal (g : P × (X dim) → (Mat dim)) (b : P → (X dim) → ℝ) (q : P × (X dim)) : ℝ :=
  ballConormal (fun z => g (q.1,z)) (b q.1) (sphereNormalize q.2)

theorem norm_iteratedFDeriv_clm_apply_le_of_finite_bounds
    {P Q F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : P → Q →L[ℝ] F} {g : P → Q}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : P) {n k : ℕ} (hk : k ≤ n)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hG : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun x => f x (g x)) x‖ ≤ (2:ℝ)^n*(A*B) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (k-i) g x‖ := norm_iteratedFDeriv_clm_apply hf hg x (by simp)
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*(A*B) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hF _ (by have := Finset.mem_range.mp hi; omega))
          (hG _ (by omega)) (norm_nonneg _) hA) (by positivity)
    _ = (2:ℝ)^k*(A*B) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (mul_nonneg hA hB)

theorem norm_fderiv_slice_gradient_parameter_le {b : P → (X dim) → ℝ}
    {p : P} {z : (X dim)} (h : DifferentiableAt ℝ (fun q => iteratedFDeriv ℝ 1 (b q) z) p) (v : P) :
    ‖fderiv ℝ (fun q => fderiv ℝ (b q) z) p v‖ ≤
      ‖fderiv ℝ (fun q => iteratedFDeriv ℝ 1 (b q) z) p v‖ := by
  let L := (continuousMultilinearCurryFin1 ℝ (X dim) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let f (q : P) := iteratedFDeriv ℝ 1 (b q) z
  have he : (fun q => fderiv ℝ (b q) z) = L ∘ f := by
    funext q
    ext w
    exact (iteratedFDeriv_one_apply (f := b q) (x := z) (fun _ => w)).symm
  rw [he,(L.hasFDerivAt.comp p h.hasFDerivAt).fderiv]
  change ‖(continuousMultilinearCurryFin1 ℝ (X dim) ℝ) (fderiv ℝ f p v)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]

theorem differentiableAt_slice_gradient_parameter {b : P → (X dim) → ℝ} {p : P} {z : (X dim)}
    (h : DifferentiableAt ℝ (fun q => iteratedFDeriv ℝ 1 (b q) z) p) :
    DifferentiableAt ℝ (fun q => fderiv ℝ (b q) z) p := by
  let L := (continuousMultilinearCurryFin1 ℝ (X dim) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have he : (fun q => fderiv ℝ (b q) z) =
      L ∘ (fun q => iteratedFDeriv ℝ 1 (b q) z) := by
    funext q
    ext w
    exact (iteratedFDeriv_one_apply (f := b q) (x := z) (fun _ => w)).symm
  rw [he]
  exact L.differentiableAt.comp p h

/-- On a compact metric family, conormal angular jets are bounded by
one additional spatial derivative. The first parameter derivative at
fixed sphere point uses only the parameter derivative of the gradient. -/
theorem exists_uniform_radialBallConormal_bounds
    (n : ℕ) {U : Set (P × (X dim))} (hU : IsOpen U) {J : Set P} (hJ : IsCompact J)
    (hJU : J ×ˢ (standardSphere dim) ⊆ U)
    {g : P × (X dim) → (Mat dim)} (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : P → (X dim) → ℝ) (p : P), p ∈ J →
      ContDiff ℝ ∞ (b p) → ∀ w ∈ (standardSphere dim),
      (∀ M : ℝ, 0 ≤ M → (∀ j ≤ n+1, ‖iteratedFDeriv ℝ j (b p) w‖ ≤ M) →
        ∀ k ≤ n, ‖iteratedFDeriv ℝ k (fun z => radialBallConormal g b (p,z)) w‖ ≤ C*M) ∧
      (DifferentiableAt ℝ (fun q => iteratedFDeriv ℝ 1 (b q) w) p → ∀ v : P,
        ‖fderiv ℝ (fun q => radialBallConormal g b (q,w)) p v‖ ≤
          C * (‖fderiv ℝ (fun q => iteratedFDeriv ℝ 1 (b q) w) p v‖ +
            ‖iteratedFDeriv ℝ 1 (b p) w‖*‖v‖)) := by
  let S := (standardSphere dim)
  have hS : IsCompact S := isCompact_sphere _ _
  let V (q : P × (X dim)) := ballConormalVector (fun z => g (q.1,z)) q.2
  have hV : ContDiffOn ℝ ∞ V U := contDiffOn_product_ballConormalVector hg hPos
  obtain ⟨A,hA,_,O,hO,hJO,_,hEq⟩ := exists_contDiff_extension_near_compact hU (hJ.prod hS) hJU hV
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  have hSN : S ⊆ N := by
    intro w hw
    show w ≠ 0
    intro h
    have hnorm := mem_sphere_zero_iff_norm.mp hw
    simp [h] at hnorm
  obtain ⟨N₀,hN₀,_,W,hW,hSW,_,hEqN⟩ := exists_contDiff_extension_near_compact
    (isClosed_singleton.isOpen_compl : IsOpen N) hS hSN contDiffOn_sphereNormalize
  let B (q : P × (X dim)) := A (q.1,N₀ q.2)
  have hB : ContDiff ℝ ∞ B := hA.comp (contDiff_fst.prodMk (hN₀.comp contDiff_snd))
  obtain ⟨D,hD,hBd⟩ := exists_uniform_finite_jet_bound (hJ.prod hS) hB n
  obtain ⟨T,hT,hTd⟩ := exists_uniform_finite_jet_bound hS hN₀ n
  obtain ⟨A₀,hA₀,hAd⟩ := exists_uniform_finite_jet_bound (hJ.prod hS) hA 1
  let C₀ := (2:ℝ)^n*(n.factorial*T^n*D)
  let C := max A₀ C₀
  have hC : 0 ≤ C := le_max_of_le_left (zero_le_one.trans hA₀)
  refine ⟨C,hC,?_⟩
  intro b p hp hb w hw
  have hNw : N₀ w = w := (hEqN (hSW hw)).trans (sphereNormalize_eq_of_sphere hw)
  constructor
  · intro M hM hJet k hk
    let a (z : (X dim)) := B (p,z)
    let f := fderiv ℝ (b p)
    have ha : ContDiff ℝ ∞ a := hB.comp (contDiff_const.prodMk contDiff_id)
    have hf : ContDiff ℝ ∞ f := hb.fderiv_right (by simp)
    have hAjet (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i a w‖ ≤ D :=
      (norm_iteratedFDeriv_slice_right_le hB p w i).trans (hBd (p,w) ⟨hp,hw⟩ i hi)
    have hFjet (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i (f ∘ N₀) w‖ ≤ n.factorial*M*T^n :=
      norm_iteratedFDeriv_comp_le_of_finite_bounds hf hN₀ w hi hM hT (fun j hj => by
        change ‖iteratedFDeriv ℝ j (fderiv ℝ (b p)) (N₀ w)‖ ≤ M
        rw [hNw,norm_iteratedFDeriv_fderiv]
        exact hJet _ (by omega)) (hTd _ hw)
    have he : (fun z => radialBallConormal g b (p,z)) =ᶠ[𝓝 w] (fun z => f (N₀ z) (a z)) := by
      have hno : ContinuousAt (fun z : (X dim) => (p,N₀ z)) w :=
        ((continuous_const : Continuous (fun _ : (X dim) => p)).prodMk hN₀.continuous).continuousAt
      filter_upwards [hW.mem_nhds (hSW hw),hno.preimage_mem_nhds
        (show O ∈ 𝓝 (p,N₀ w) by rw [hNw]; exact hO.mem_nhds (hJO ⟨hp,hw⟩))] with z hz hzO
      rw [radialBallConormal,ballConormal_eq_fderiv_conormalVector]
      change f (sphereNormalize z) (V (p,sphereNormalize z)) = f (N₀ z) (A (p,N₀ z))
      change (p,N₀ z) ∈ O at hzO
      rw [hEq hzO,hEqN hz]
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ he k).eq_of_nhds]
    refine (norm_iteratedFDeriv_clm_apply_le_of_finite_bounds (hf.comp hN₀) ha w hk
      (by positivity) (zero_le_one.trans hD) hFjet hAjet).trans ?_
    rw [show (2:ℝ)^n*(n.factorial*M*T^n*D) = C₀*M from by dsimp only [C₀]; ring]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hM
  · intro hbDiff v
    let a (q : P) := A (q,w)
    let F (q : P) := fderiv ℝ (b q) w
    have ha : ContDiff ℝ ∞ a := hA.comp (contDiff_id.prodMk contDiff_const)
    have hF := differentiableAt_slice_gradient_parameter hbDiff
    have he : (fun q => radialBallConormal g b (q,w)) =ᶠ[𝓝 p] (fun q => F q (a q)) := by
      have hm : ContinuousAt (fun q : P => (q,w)) p := (continuous_id.prodMk continuous_const).continuousAt
      filter_upwards [hm.preimage_mem_nhds (hO.mem_nhds (hJO (show (p,w) ∈ J ×ˢ S from ⟨hp,hw⟩)))] with q hq
      rw [radialBallConormal,sphereNormalize_eq_of_sphere hw,ballConormal_eq_fderiv_conormalVector]
      change F q (V (q,w)) = F q (A (q,w))
      rw [hEq hq]
    have haB : ‖a p‖ ≤ A₀ := by
      simpa only [norm_iteratedFDeriv_zero] using hAd (p,w) ⟨hp,hw⟩ 0 (by omega)
    have haD : ‖fderiv ℝ a p‖ ≤ A₀ := by
      rw [← norm_iteratedFDeriv_one]
      have hslice := norm_iteratedFDeriv_slice_left_le hA p w 1
      exact hslice.trans (hAd (p,w) ⟨hp,hw⟩ 1 le_rfl)
    rw [he.fderiv_eq,fderiv_clm_apply hF (ha.differentiable (by simp) p)]
    simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
    have hFval : ‖F p‖ = ‖iteratedFDeriv ℝ 1 (b p) w‖ := (norm_iteratedFDeriv_one (b p)).symm
    calc
      _ ≤ ‖_‖+‖_‖ := norm_add_le _ _
      _ ≤ ‖F p‖*(A₀*‖v‖) + ‖fderiv ℝ F p v‖*A₀ := add_le_add
        (((F p).le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (((fderiv ℝ a p).le_opNorm _).trans (mul_le_mul_of_nonneg_right haD (norm_nonneg _))) (norm_nonneg _)))
        (((fderiv ℝ F p v).le_opNorm _).trans (mul_le_mul_of_nonneg_left haB (norm_nonneg _)))
      _ ≤ C*(‖fderiv ℝ (fun q => iteratedFDeriv ℝ 1 (b q) w) p v‖ +
            ‖iteratedFDeriv ℝ 1 (b p) w‖*‖v‖) := by
        rw [hFval]
        have hFD := norm_fderiv_slice_gradient_parameter_le hbDiff v
        calc
          _ = A₀*(‖fderiv ℝ F p v‖ + ‖iteratedFDeriv ℝ 1 (b p) w‖*‖v‖) := by ring
          _ ≤ _ := mul_le_mul (le_max_left _ _) (add_le_add hFD le_rfl) (by positivity) hC

end CalderonN
