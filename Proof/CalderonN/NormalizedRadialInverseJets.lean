module

public import Proof.CalderonN.SupportedSphereMultiplierBounds

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! The inverse radial weight and its first Taylor difference have
joint normalized jets bounded without negative powers of the radius. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem LocalSmoothJetBudget.congr_germ
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {x : E} {N : ℕ} {C : ℝ}
    (h : LocalSmoothJetBudget f x N C) (he : g =ᶠ[𝓝 x] f) :
    LocalSmoothJetBudget g x N C :=
  ⟨h.smooth.congr_of_eventuallyEq he,fun n hn => by
    rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
    exact h.bound n hn⟩

theorem LocalSmoothJetBudget.real_mul {f g : E → ℝ} {x : E} {N : ℕ} {C D : ℝ}
    (h : LocalSmoothJetBudget f x N C) (h' : LocalSmoothJetBudget g x N D) :
    LocalSmoothJetBudget (fun x => f x*g x) x N
      ((2:ℝ)^N*‖ContinuousLinearMap.mul ℝ ℝ‖*C*D) :=
  h.bilinear h' (ContinuousLinearMap.mul ℝ ℝ)

theorem uniform_normalized_radial_inverse_germs [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z]
    (K : Set Z) (hK : IsCompact K) (N : ℕ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : E → ℝ) (hr : ContDiff ℝ ∞ r)
      (a : E × Z → ℝ) (ha : ContDiff ℝ ∞ a) (x : E) (β : ℝ),
      |r x| * D ≤ 1/2 →
      (∀ z ∈ K,LocalSmoothJetBudget (fun q : E × Z => r (x+β⁻¹ • q.1)) 0 N C ∧
        LocalSmoothJetBudget (fun q : E × Z => a (x+β⁻¹ • q.1,z+q.2)) 0 N D) →
      ∃ (V : Set (E × Z)) (p p₁ : E × Z → ℝ), IsOpen V ∧ ({x} ×ˢ K) ⊆ V ∧
        ContDiff ℝ ∞ p ∧ ContDiff ℝ ∞ p₁ ∧
        (∀ q ∈ V,p q = (1+r q.1*a q)⁻¹ ∧ p₁ q = -(a q)*p q ∧ 0 < 1+r q.1*a q) ∧
        ∀ z ∈ K,LocalSmoothJetBudget (fun q : E × Z => p (x+β⁻¹ • q.1,z+q.2)) 0 N B ∧
          LocalSmoothJetBudget (fun q : E × Z => p₁ (x+β⁻¹ • q.1,z+q.2)) 0 N B := by
  let S := (2:ℝ)^N*‖ContinuousLinearMap.mul ℝ ℝ‖
  let C₁ := 1+S*C*D
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hC₁ : 1 ≤ C₁ := le_add_of_nonneg_right (mul_nonneg (mul_nonneg hS hC) hD)
  have hInv (t : ℝ) (ht : t ∈ Icc (1/2:ℝ) (3/2)) : ContDiffAt ℝ ∞ Inv.inv t := by
    have ht' : (1/2:ℝ) ≤ t := ht.1
    exact contDiffAt_inv ℝ (ne_of_gt (by linarith))
  obtain ⟨D₁,hD₁,hInvJets⟩ := exists_uniform_local_finite_jet_bound isCompact_Icc hInv N
  let B₀ := (N.factorial:ℝ)*D₁*C₁^N
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  let B := B₀+S*D*B₀
  refine ⟨B,by dsimp only [B]; positivity,?_⟩
  intro r hr a ha x β hε hJet
  let w (q : E × Z) := 1+r q.1*a q
  have hw : ContDiff ℝ ∞ w := contDiff_const.add ((hr.comp contDiff_fst).mul ha)
  have hPoint (z : Z) (hz : z ∈ K) : w (x,z) ∈ Icc (1/2:ℝ) (3/2) := by
    have hA := (hJet z hz).2.value_norm_le
    have hAbs : |r x*a (x,z)| ≤ 1/2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left
        (by simpa only [Prod.fst_zero,Prod.snd_zero,smul_zero,add_zero,Real.norm_eq_abs] using hA) (abs_nonneg _)).trans hε
    have h := abs_le.mp hAbs
    change 1/2 ≤ 1+r x*a (x,z) ∧ 1+r x*a (x,z) ≤ 3/2
    constructor <;> linarith [h.1,h.2]
  let U := w ⁻¹' Ioi 0
  have hU : IsOpen U := isOpen_Ioi.preimage hw.continuous
  let K₀ := ({x} : Set E) ×ˢ K
  have hKC : IsCompact K₀ := isCompact_singleton.prod hK
  have hKU : K₀ ⊆ U := by
    intro q hq
    have hx : q.1 = x := hq.1
    change 0 < w q
    have hq' := (hPoint q.2 hq.2).1
    rw [show q = (x,q.2) from Prod.ext hx rfl]
    linarith
  obtain ⟨p,hp,_,V,hV,hKV,hVU,hEq⟩ := exists_contDiff_extension_near_compact hU hKC hKU
    (f:=fun q => (w q)⁻¹) (hw.contDiffOn.inv (fun q hq => (show 0 < w q from hq).ne'))
  let p₁ (q : E × Z) := -(a q)*p q
  refine ⟨V,p,p₁,hV,hKV,hp,ha.neg.mul hp,fun q hq => ⟨hEq hq,rfl,hVU hq⟩,?_⟩
  intro z hz
  let f (q : E × Z) := (x+β⁻¹ • q.1,z+q.2)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_const.add (contDiff_fst.const_smul _)).prodMk (contDiff_const.add contDiff_snd)
  have hf₀ : f 0 = (x,z) := by simp [f]
  obtain ⟨hR,hA⟩ := hJet z hz
  have hW : LocalSmoothJetBudget (w ∘ f) 0 N C₁ := by
    have hh := (LocalSmoothJetBudget.const (P:=E × Z) (x:=0) (N:=N) (1:ℝ)).add (hR.real_mul hA)
    have he : w ∘ f = fun q : E × Z => 1+r (x+β⁻¹ • q.1)*a (x+β⁻¹ • q.1,z+q.2) := rfl
    rw [he]
    simpa only [C₁,S,norm_one] using hh
  have hI : LocalSmoothJetBudget Inv.inv ((w ∘ f) 0) N D₁ := by
    rw [Function.comp_apply,hf₀]
    exact ⟨hInv _ (hPoint z hz),hInvJets _ (hPoint z hz)⟩
  have hEq' : p ∘ f =ᶠ[𝓝 (0:E × Z)] Inv.inv ∘ w ∘ f := by
    have hfv : f 0 ∈ V := by rw [hf₀]; exact hKV ⟨mem_singleton _,hz⟩
    filter_upwards [hf.continuous.continuousAt.eventually (hV.mem_nhds hfv)] with t ht
    exact hEq ht
  have hP := (hW.comp hI hC₁).congr_germ hEq'
  refine ⟨hP.enlarge (le_add_of_nonneg_right (by positivity)),?_⟩
  have hA' : LocalSmoothJetBudget (fun q => -(a (f q))) 0 N D := by
    refine ⟨hA.smooth.neg,fun n hn => ?_⟩
    change ‖iteratedFDeriv ℝ n (-(a ∘ f)) 0‖ ≤ D
    rw [iteratedFDeriv_neg,Pi.neg_apply,norm_neg]
    exact hA.bound n hn
  exact (hA'.real_mul hP).enlarge (by dsimp only [B,S]; linarith)

end CalderonN
