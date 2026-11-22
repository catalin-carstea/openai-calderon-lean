module

public import Proof.CalderonPatch.CapGeometry
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith

public section

noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace CalderonPatch

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- In the pushed-in realization of a cap, the original seam is the
graph of the nonnegative bump. -/
@[expose] def pushedCap (b : Z → ℝ) : Set (Z × ℝ) := {p | 0 < p.2 ∧ p.2 < b p.1}

theorem isOpen_pushedCap {b : Z → ℝ} (hb : Continuous b) : IsOpen (pushedCap b) :=
  (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd (hb.comp continuous_fst))

theorem isConnected_pushedCap {b : Z → ℝ} (hb : Continuous b) (h : IsConnected {x | 0 < b x}) :
    IsConnected (pushedCap b) := by
  let r : Z × ℝ → Z × ℝ := fun p => (p.1, -p.2)
  have hR : Continuous r := continuous_fst.prodMk continuous_snd.neg
  have heq : r '' exteriorCap b = pushedCap b := by
    ext p
    constructor
    · rintro ⟨⟨z,t⟩, ⟨hlo, hhi⟩, rfl⟩
      exact ⟨neg_pos.mpr hhi, neg_lt.mp hlo⟩
    · rintro ⟨hlo, hhi⟩
      refine ⟨(p.1,-p.2), ⟨neg_lt_neg hhi, neg_lt_zero.mpr hlo⟩, ?_⟩
      exact Prod.ext rfl (neg_neg p.2)
  rw [← heq]
  exact (isConnected_exteriorCap hb h).image r hR.continuousOn

/-- Removing the closed cap from the extended interior leaves precisely
the interior on the original side of the shifted seam. The equality
holds even at the flat edge of the bump. -/
theorem positiveHalfSpace_sdiff_closure_pushedCap {b : Z → ℝ} (hb : Continuous b)
    (hB : ∀ z, 0 ≤ b z) :
    (univ ×ˢ Ioi (0 : ℝ)) \ closure (pushedCap b) = {p | b p.1 < p.2} := by
  have hcl : closure (pushedCap b) ⊆ {p | p.2 ≤ b p.1} :=
    closure_minimal (fun _ hx => hx.2.le) (isClosed_le continuous_snd (hb.comp continuous_fst))
  ext p
  constructor
  · rintro ⟨hp, hn⟩
    change b p.1 < p.2
    apply lt_of_not_ge
    intro h
    apply hn
    have hpos : 0 < p.2 := hp.2
    have hbp : 0 < b p.1 := hpos.trans_le h
    have hI : p.2 ∈ closure (Ioo 0 (b p.1)) := by rw [closure_Ioo hbp.ne]; exact ⟨hpos.le, h⟩
    have hc : Continuous (fun t : ℝ => (p.1, t)) := continuous_const.prodMk continuous_id
    have hsub : (fun t : ℝ => (p.1, t)) '' Ioo 0 (b p.1) ⊆ pushedCap b := by
      rintro _ ⟨t, ht, rfl⟩
      exact ht
    exact closure_mono hsub (image_closure_subset_closure_image hc (mem_image_of_mem _ hI))
  · intro h
    change b p.1 < p.2 at h
    exact ⟨⟨mem_univ _, (hB p.1).trans_lt h⟩, fun hp => (not_le_of_gt h) (show p.2 ≤ b p.1 from hcl hp)⟩

private theorem verticalFiber_surjective {b : Z → ℝ} {η : ℝ → ℝ} (hη : Continuous η)
    {R : ℝ} (hR : 0 < R) (hOutside : ∀ t, R ≤ |t| → η t = 0) (z : Z) :
    Function.Surjective (fun t : ℝ => t + b z * η t) := by
  intro y
  let d := R + |y| + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hRd : R ≤ d := by dsimp [d]; linarith [abs_nonneg y]
  have hηm : η (-d) = 0 := hOutside (-d) (by simpa [abs_of_pos hd] using hRd)
  have hηp : η d = 0 := hOutside d (by rwa [abs_of_pos hd])
  let f : ℝ → ℝ := fun t => t + b z * η t
  have hf : Continuous f := continuous_id.add (continuous_const.mul hη)
  have hy : y ∈ Icc (f (-d)) (f d) := by
    change -d + b z * η (-d) ≤ y ∧ y ≤ d + b z * η d
    rw [hηm, hηp, mul_zero, add_zero, add_zero]
    exact ⟨by dsimp [d]; linarith [neg_abs_le y], by dsimp [d]; linarith [le_abs_self y]⟩
  obtain ⟨t, _, hey⟩ := intermediate_value_Icc (by linarith : -d ≤ d) hf.continuousOn hy
  exact ⟨t, hey⟩

/-- A smooth vertical change of coordinates pushes the original half
space inward where the bump is positive. Its inverse is smooth and the
map is the identity where the bump or vertical cutoff vanishes. -/
theorem exists_vertical_cap_diffeomorph [FiniteDimensional ℝ Z] {b : Z → ℝ} {η : ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (hη : ContDiff ℝ ∞ η) (hη0 : η 0 = 1)
    {R : ℝ} (hR : 0 < R) (hOutside : ∀ t, R ≤ |t| → η t = 0)
    (hPos : ∀ z t, 0 < 1 + b z * deriv η t) :
    ∃ e : (Z × ℝ) ≃ (Z × ℝ),
      (∀ p, e p = (p.1, p.2 + b p.1 * η p.2)) ∧ ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      e '' (univ ×ˢ Ici (0 : ℝ)) = {p | b p.1 ≤ p.2} ∧
      e '' (univ ×ˢ Ioi (0 : ℝ)) = {p | b p.1 < p.2} := by
  let ψ : Z × ℝ → ℝ := fun p => p.2 + b p.1 * η p.2
  let f : Z × ℝ → Z × ℝ := fun p => (p.1, ψ p)
  have hψ : ContDiff ℝ ∞ ψ := contDiff_snd.add ((hb.comp contDiff_fst).mul (hη.comp contDiff_snd))
  have hf : ContDiff ℝ ∞ f := contDiff_fst.prodMk hψ
  have hMass (z : Z) (t : ℝ) : HasDerivAt (fun s : ℝ => ψ (z, s)) (1 + b z * deriv η t) t :=
    (hasDerivAt_id t).add ((hη.differentiable (by simp) t).hasDerivAt.const_mul (b z))
  have hStrict (z : Z) : StrictMono (fun t : ℝ => ψ (z, t)) := strictMono_of_deriv_pos fun t => by
    rw [(hMass z t).deriv]
    exact hPos z t
  have hBij : Function.Bijective f := by
    constructor
    · rintro ⟨x, a⟩ ⟨y, b⟩ h
      have hxy := congrArg Prod.fst h
      change x = y at hxy
      subst y
      exact Prod.ext rfl ((hStrict x).injective (congrArg Prod.snd h))
    · rintro ⟨z, t⟩
      obtain ⟨v, hv⟩ := verticalFiber_surjective (b := b) hη.continuous hR hOutside z t
      exact ⟨(z,v), Prod.ext rfl hv⟩
  let e : (Z × ℝ) ≃ (Z × ℝ) := Equiv.ofBijective f hBij
  have hSmoothInv : ContDiff ℝ ∞ e.symm := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    let p := e.symm y
    let D := fderiv ℝ ψ p
    let A := (ContinuousLinearMap.fst ℝ Z ℝ).prod D
    have hFD : HasFDerivAt f A p := (ContinuousLinearMap.fst ℝ Z ℝ).hasFDerivAt.prodMk
      ((hψ.differentiable (by simp) p).hasFDerivAt)
    have hV : D (0,1) = 1 + b p.1 * deriv η p.2 := by
      have ht : HasDerivAt (fun t : ℝ => (p.1,t)) (0,1) p.2 :=
        (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
      have hD : HasFDerivAt ψ D (p.1, p.2) := (hψ.differentiable (by simp) p).hasFDerivAt
      exact (hD.comp_hasDerivAt _ ht).unique (hMass p.1 p.2)
    have hinj : Function.Injective A := (injective_iff_map_eq_zero A).mpr (fun v hv => by
      have hv₁ := congrArg Prod.fst hv
      have hv₂ := congrArg Prod.snd hv
      change v.1 = 0 at hv₁
      change D v = 0 at hv₂
      have hvl : v = v.2 • ((0,1) : Z × ℝ) := Prod.ext (by simpa using hv₁) (by simp)
      have hh : D v = v.2 * D (0,1) := by conv_lhs => rw [hvl, map_smul, smul_eq_mul]
      have hV₂ := (mul_eq_zero.mp (hh.symm.trans hv₂)).resolve_right (hV ▸ (hPos p.1 p.2).ne')
      exact Prod.ext hv₁ hV₂)
    have hsurj : Function.Surjective A := LinearMap.injective_iff_surjective.mp hinj
    let B := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
    have hFD' : HasFDerivAt f (B : Z × ℝ →L[ℝ] Z × ℝ) p := hFD
    let k := hf.contDiffAt.toOpenPartialHomeomorph f hFD' (by simp)
    have hk : (k : Z × ℝ → Z × ℝ) = f := rfl
    have hfy : f p = y := e.apply_symm_apply y
    have hy : y ∈ k.target := hfy ▸ hf.contDiffAt.image_mem_toOpenPartialHomeomorph_target hFD' (by simp)
    have hp' : k.symm y = p := hBij.1 ((show f (k.symm y) = y by rw [← hk]; exact k.right_inv hy).trans hfy.symm)
    have hInv := k.contDiffAt_symm hy (by rw [hk, hp']; exact hFD') (by rw [hk]; exact hf.contDiffAt)
    apply hInv.congr_of_eventuallyEq
    filter_upwards [k.open_target.mem_nhds hy] with x hx
    exact hBij.1 ((show f (e.symm x) = x from e.apply_symm_apply x).trans
      (show f (k.symm x) = x by rw [← hk]; exact k.right_inv hx).symm)
  refine ⟨e, fun _ => rfl, hf, hSmoothInv, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨⟨z,t⟩, ht, rfl⟩
      simpa [e, f, ψ, hη0] using (hStrict z).monotone ht.2
    · intro hp
      let a := e.symm p
      have heq : f a = p := e.apply_symm_apply p
      have hfirst : a.1 = p.1 := show (f a).1 = p.1 from congrArg (fun q : Z × ℝ => q.1) heq
      have hsnd : ψ a = p.2 := show (f a).2 = p.2 from congrArg (fun q : Z × ℝ => q.2) heq
      have hh : ψ (a.1,0) ≤ ψ (a.1,a.2) := by
        change (0 : ℝ) + b a.1 * η 0 ≤ ψ a
        rw [hsnd, hfirst, hη0, mul_one, zero_add]
        exact hp
      exact ⟨a, ⟨mem_univ _, (hStrict a.1).le_iff_le.mp hh⟩, e.apply_symm_apply p⟩
  · ext p
    constructor
    · rintro ⟨⟨z,t⟩, ht, rfl⟩
      simpa [e, f, ψ, hη0] using hStrict z ht.2
    · intro hp
      let a := e.symm p
      have heq : f a = p := e.apply_symm_apply p
      have hfirst : a.1 = p.1 := show (f a).1 = p.1 from congrArg (fun q : Z × ℝ => q.1) heq
      have hsnd : ψ a = p.2 := show (f a).2 = p.2 from congrArg (fun q : Z × ℝ => q.2) heq
      have hh : ψ (a.1,0) < ψ (a.1,a.2) := by
        change (0 : ℝ) + b a.1 * η 0 < ψ a
        rw [hsnd, hfirst, hη0, mul_one, zero_add]
        exact hp
      exact ⟨a, ⟨mem_univ _, (hStrict a.1).lt_iff_lt.mp hh⟩, e.apply_symm_apply p⟩

end CalderonPatch
