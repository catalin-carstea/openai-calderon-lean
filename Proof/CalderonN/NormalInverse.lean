module

public import Proof.CalderonN.NormalCoordinates
public import Proof.CalderonN.Chart

import Proof.CalderonN.MetricPair
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ}

theorem exists_smooth_inverse_on_image {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {D : Set E} (hD : IsOpen D) {f : E → E} (hf : ContDiffOn ℝ ∞ f D)
    (hi : InjOn f D) (hder : ∀ x ∈ D, Function.Bijective (fderiv ℝ f x)) :
    IsOpen (f '' D) ∧ ∃ v : E → E, ContDiffOn ℝ ∞ v (f '' D) ∧
      LeftInvOn v f D ∧ MapsTo v (f '' D) D ∧ RightInvOn v f (f '' D) := by
  classical
  let v (y : E) := if h : ∃ x ∈ D, f x = y then h.choose else 0
  have hv (y : E) (hy : y ∈ f '' D) : v y ∈ D ∧ f (v y) = y := by
    have h : ∃ x ∈ D, f x = y := hy
    simp only [v,dite_eq_left h]
    exact h.choose_spec
  have hl : LeftInvOn v f D := fun x hx => hi (hv _ ⟨x,hx,rfl⟩).1 hx (hv _ ⟨x,hx,rfl⟩).2
  have hloc : ∀ y ∈ f '' D, (f '' D) ∈ 𝓝 y ∧ ContDiffAt ℝ ∞ v y := by
    rintro y ⟨x,hx,rfl⟩
    let J := fderiv ℝ f x
    let A := ContinuousLinearEquiv.ofBijective J
      (LinearMap.ker_eq_bot.mpr (hder x hx).1) (LinearMap.range_eq_top.mpr (hder x hx).2)
    have hs := hf.contDiffAt (hD.mem_nhds hx)
    have hA : HasFDerivAt f (A : E →L[ℝ] E) x :=
      (hs.differentiableAt (by simp)).hasFDerivAt
    let e := hs.toOpenPartialHomeomorph f hA (by simp)
    have he : (e : E → E) = f := hs.toOpenPartialHomeomorph_coe hA (by simp)
    have hxE : x ∈ e.source := hs.mem_toOpenPartialHomeomorph_source hA (by simp)
    have hyE : f x ∈ e.target := hs.image_mem_toOpenPartialHomeomorph_target hA (by simp)
    have hyv : e.symm (f x) = x := by rw [← he]; exact e.left_inv hxE
    have hDgerm : ∀ᶠ z in 𝓝 (f x), e.symm z ∈ D := by
      have hm : D ∈ 𝓝 (e.symm (f x)) := hyv.symm ▸ hD.mem_nhds hx
      exact (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hyE)) hm
    have hBoth := hDgerm.and (e.open_target.mem_nhds hyE : ∀ᶠ z in 𝓝 (f x), z ∈ e.target)
    refine ⟨hBoth.mono (fun z hz => ⟨e.symm z,hz.1,by rw [← he,e.right_inv hz.2]⟩), ?_⟩
    have heDiff : ContDiffAt ℝ ∞ e.symm (f x) := by
      apply e.contDiffAt_symm (f₀' := A) hyE
      · rw [hyv,he]
        exact hA
      · rw [hyv,he]
        exact hs
    refine heDiff.congr_of_eventuallyEq (hBoth.mono fun z hz => ?_)
    have hz' : f (e.symm z) = z := by rw [← he,e.right_inv hz.2]
    exact hi (hv z ⟨e.symm z,hz.1,hz'⟩).1 hz.1 ((hv z ⟨e.symm z,hz.1,hz'⟩).2.trans hz'.symm)
  exact ⟨isOpen_iff_mem_nhds.mpr (fun y hy => (hloc y hy).1),
    v,fun y hy => (hloc y hy).2.contDiffWithinAt, hl,
    fun y hy => (hv y hy).1, fun y hy => (hv y hy).2⟩

/-- The interior of the normal velocity disks, with the same radius as
the protected normal-coordinate witness. -/
@[expose] def normalVelocityDomain (Y : Set (X dim)) (γ : (MetricField dim)) (R : ℝ) : Set ((X dim) × (X dim)) :=
  {p | p.1 ∈ Y ∧ metricPair γ p.1 p.2 p.2 < R^2}

/-- The physical pair has the center in the second factor. -/
@[expose] def normalPairMap (expMap : (X dim) × (X dim) → (X dim)) (p : (X dim) × (X dim)) : (X dim) × (X dim) :=
  (expMap p,p.1)

@[expose] def normalPairDomain (Y : Set (X dim)) (γ : (MetricField dim)) (R : ℝ)
    (expMap : (X dim) × (X dim) → (X dim)) : Set ((X dim) × (X dim)) :=
  normalPairMap expMap '' normalVelocityDomain Y γ R

private theorem normalVelocityDomain_isOpen {Y : Set (X dim)} (hY : IsOpen Y)
    {γ : (MetricField dim)} (hγ : SmoothMetric Y γ) (R : ℝ) :
    IsOpen (normalVelocityDomain Y γ R) := by
  have hy : IsOpen (Prod.fst ⁻¹' Y : Set ((X dim) × (X dim))) := hY.preimage (continuous_fst : Continuous (Prod.fst : (X dim) × (X dim) → (X dim)))
  have h : ContinuousOn (fun p : (X dim) × (X dim) => metricPair γ p.1 p.2 p.2) (Prod.fst ⁻¹' Y) := by
    unfold metricPair
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    have h1 : ContinuousOn (fun p : (X dim) × (X dim) => γ p.1 i j) (Prod.fst ⁻¹' Y) :=
      (hγ.1 i j).continuousOn.comp continuous_fst.continuousOn
        (fun p (hp : p ∈ Prod.fst ⁻¹' Y) => hp)
    have h2 (k : (I dim)) : ContinuousOn (fun p : (X dim) × (X dim) => p.2 k) (Prod.fst ⁻¹' Y) :=
      ((EuclideanSpace.proj k : (X dim) →L[ℝ] ℝ).continuous.comp continuous_snd).continuousOn
    exact (h1.mul (h2 i)).mul (h2 j)
  exact h.isOpen_inter_preimage hy (t := Iio (R^2)) isOpen_Iio

/-- The normal endpoint map gives a jointly smooth local inverse velocity on
the full open physical tube. It uses the exact injectivity and derivative
from the same normal-coordinate witness. -/
theorem exists_normal_inverse_velocity
    {Y Ω : Set (X dim)} (hY : IsOpen Y) {γ : (MetricField dim)} (hγ : SmoothMetric Y γ)
    {R : ℝ} {expMap : (X dim) × (X dim) → (X dim)}
    (hN : NormalCoordinates Y Ω γ expMap (fun _ => R)) :
    let D := normalPairDomain Y γ R expMap
    IsOpen D ∧ D ⊆ Ω ×ˢ Y ∧
      ∃ V : (X dim) × (X dim) → (X dim), ContDiffOn ℝ ∞ V D ∧
        (∀ p ∈ normalVelocityDomain Y γ R, V (expMap p,p.1) = p.2) ∧
        ∀ q ∈ D, (q.2,V q) ∈ normalVelocityDomain Y γ R ∧ expMap (q.2,V q) = q.1 := by
  let U := normalVelocityDomain Y γ R
  let f := normalPairMap expMap
  have hU : IsOpen U := normalVelocityDomain_isOpen hY hγ R
  have hclose (p : (X dim) × (X dim)) (hp : p ∈ U) : p.2 ∈ disk γ p.1 R := hp.2.le
  obtain ⟨W,_,hUW,hE⟩ := hN.1
  have hEu : ContDiffOn ℝ ∞ expMap U := hE.mono (fun p hp => hUW ⟨hp.1,hclose p hp⟩)
  have hf : ContDiffOn ℝ ∞ f U := hEu.prodMk contDiff_fst.contDiffOn
  have hinj : InjOn f U := by
    rintro ⟨y,v⟩ hp ⟨y',v'⟩ hp' hEq
    have h := congrArg Prod.snd hEq
    change y = y' at h
    subst y'
    exact Prod.ext rfl ((hN.2 y hp.1).2.1 (hclose (y,v) hp) (hclose (y,v') hp') (congrArg Prod.fst hEq))
  have hder (p : (X dim) × (X dim)) (hp : p ∈ U) : Function.Bijective (fderiv ℝ f p) := by
    let A := fderiv ℝ expMap p
    let P := ContinuousLinearMap.fst ℝ (X dim) (X dim)
    let B := fderiv ℝ (fun w => expMap (p.1,w)) p.2
    have hED := ((hEu.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
    have hJ : fderiv ℝ f p = A.prod P := (hED.prodMk P.hasFDerivAt).fderiv
    have hB (w : (X dim)) : A (0,w) = B w := by
      have hJ : HasFDerivAt (fun w : (X dim) => (p.1,w)) (ContinuousLinearMap.inr ℝ (X dim) (X dim)) p.2 :=
        hasFDerivAt_prodMk_right p.1 p.2
      have h := (hED.comp p.2 hJ).fderiv
      exact congrArg (fun Q : (X dim) →L[ℝ] (X dim) => Q w) h.symm
    have hBinj : Function.Injective B := ((hN.2 p.1 hp.1).2.2 p.2 (hclose p hp)).2.1.1
    rw [hJ]
    have hI : Function.Injective (A.prod P) := by
      intro v w hw
      have hp1 : v.1 = w.1 := congrArg Prod.snd hw
      have hpA : A v = A w := congrArg Prod.fst hw
      have hp0 : A (v-w) = 0 := by rw [map_sub,hpA,sub_self]
      have hz : v-w = (0,v.2-w.2) := Prod.ext (sub_eq_zero.mpr hp1) rfl
      rw [hz,hB] at hp0
      exact Prod.ext hp1 (sub_eq_zero.mp (hBinj (hp0.trans (map_zero _).symm)))
    exact ⟨hI,(LinearMap.injective_iff_surjective (f := (A.prod P).toLinearMap)).mp hI⟩
  obtain ⟨ho,v,hv,hl,hm,hr⟩ := exists_smooth_inverse_on_image hU hf hinj hder
  refine ⟨ho,?_,(fun q => (v q).2),contDiff_snd.contDiffOn.comp hv (fun _ _ => mem_univ _),?_,?_⟩
  · rintro _ ⟨p,hp,rfl⟩
    exact ⟨((hN.2 p.1 hp.1).2.2 p.2 (hclose p hp)).1,hp.1⟩
  · intro p hp
    exact congrArg Prod.snd (hl hp)
  · intro q hq
    have h := hr hq
    have h₁ : expMap (v q) = q.1 := congrArg Prod.fst h
    have h₂ : (v q).1 = q.2 := congrArg Prod.snd h
    have hvq : (q.2,(v q).2) = v q := Prod.ext h₂.symm rfl
    exact ⟨hvq.symm ▸ hm hq,hvq.symm ▸ h₁⟩

end CalderonN
