module

public import Proof.CalderonN.NormalInverse

import Proof.CalderonN.MetricPair
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ}

theorem NormalCoordinates.center_mono {Y Y' Ω : Set (X dim)} (hsub : Y' ⊆ Y)
    {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω γ E r) : NormalCoordinates Y' Ω γ E r := by
  obtain ⟨W,hWo,hW,hE⟩ := hN.1
  exact ⟨⟨W,hWo,fun p hp => hW ⟨hsub hp.1,hp.2⟩,hE⟩,fun y hy => hN.2 y (hsub hy)⟩

/-- The defining phase of the actual moving normal spheres. -/
@[expose] def normalPhase (γ : (MetricField dim)) (V : (X dim) × (X dim) → (X dim)) (r : (X dim) → ℝ) (p : (X dim) × (X dim)) : ℝ :=
  (metricPair γ p.2 (V p) (V p) - (r p.2)^2)/2

theorem contDiffOn_normalPhase {D : Set ((X dim) × (X dim))} {Y : Set (X dim)} {γ : (MetricField dim)}
    {V : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ} (hg : SmoothMetric Y γ) (hD : MapsTo Prod.snd D Y)
    (hV : ContDiffOn ℝ ∞ V D) (hr : ContDiffOn ℝ ∞ r Y) :
    ContDiffOn ℝ ∞ (normalPhase γ V r) D := by
  have hv (i : (I dim)) : ContDiffOn ℝ ∞ (fun p : (X dim) × (X dim) => V p i) D :=
    (EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hpair : ContDiffOn ℝ ∞ (fun p : (X dim) × (X dim) => metricPair γ p.2 (V p) (V p)) D := by
    unfold metricPair
    refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
    exact (((hg.1 i j).comp contDiff_snd.contDiffOn hD).mul (hv i)).mul (hv j)
  exact (hpair.sub (((hr.comp contDiff_snd.contDiffOn hD).pow 2))).div_const 2

private theorem scaled_sphere_mem_normalVelocityDomain {Y : Set (X dim)} {γ : (MetricField dim)}
    {y w : (X dim)} (hy : y ∈ Y) (hw : w ∈ sphereAt γ y) {s R : ℝ} (hs : s ∈ Ioo 0 R) :
    (y,s • w) ∈ normalVelocityDomain Y γ R := by
  refine ⟨hy,?_⟩
  change metricPair γ y (s • w) (s • w) < R^2
  have he : metricPair γ y w w = 1 := hw
  rw [metricPair_smul_same,he,mul_one]
  exact pow_lt_pow_left₀ hs.2 hs.1.le two_ne_zero

/-- The phase equals half the difference of squared radii along the actual
radial rays, so its positive side is exactly the outside of the sphere. -/
theorem normalPhase_radial {Y : Set (X dim)} {γ : (MetricField dim)} {R : ℝ}
    {E V : (X dim) × (X dim) → (X dim)} (hInv : ∀ p ∈ normalVelocityDomain Y γ R, V (E p,p.1) = p.2)
    {y w : (X dim)} (hy : y ∈ Y) (hw : w ∈ sphereAt γ y) {s : ℝ} (hs : s ∈ Ioo 0 R)
    (r : (X dim) → ℝ) :
    normalPhase γ V r (E (y,s • w),y) = (s^2-(r y)^2)/2 := by
  have hV := hInv (y,s • w) (scaled_sphere_mem_normalVelocityDomain hy hw hs)
  unfold normalPhase
  change (metricPair γ y (V (E (y,s • w),y)) (V (E (y,s • w),y)) - (r y)^2)/2 = _
  rw [show V (E (y,s • w),y) = s • w from hV,metricPair_smul_same,show metricPair γ y w w = 1 from hw,mul_one]

theorem normalPhase_pos_iff_radial {Y : Set (X dim)} {γ : (MetricField dim)} {R : ℝ}
    {E V : (X dim) × (X dim) → (X dim)} (hInv : ∀ p ∈ normalVelocityDomain Y γ R, V (E p,p.1) = p.2)
    {y w : (X dim)} (hy : y ∈ Y) (hw : w ∈ sphereAt γ y) {s : ℝ} (hs : s ∈ Ioo 0 R)
    (r : (X dim) → ℝ) (hr : 0 ≤ r y) :
    0 < normalPhase γ V r (E (y,s • w),y) ↔ r y < s := by
  rw [normalPhase_radial hInv hy hw hs,div_pos_iff_of_pos_right (by norm_num),sub_pos]
  exact pow_lt_pow_iff_left₀ hr hs.1.le two_ne_zero

/-- The first partial differential is nonzero at every positive radius:
its value on the radial velocity is exactly that radius. -/
theorem normalPhase_fderiv_radial
    {Y Ω : Set (X dim)} {γ : (MetricField dim)} {E V : (X dim) × (X dim) → (X dim)} {R : ℝ}
    (hN : NormalCoordinates Y Ω γ E (fun _ => R))
    (hInv : ∀ p ∈ normalVelocityDomain Y γ R, V (E p,p.1) = p.2)
    {y w : (X dim)} (hy : y ∈ Y) (hw : w ∈ sphereAt γ y) {s : ℝ} (hs : s ∈ Ioo 0 R)
    (r : (X dim) → ℝ)
    (hρ : DifferentiableAt ℝ (normalPhase γ V r) (E (y,s • w),y)) :
    fderiv ℝ (normalPhase γ V r) (E (y,s • w),y)
      (fderiv ℝ E (y,s • w) (0,w),0) = s := by
  let p : (X dim) × (X dim) := (y,s • w)
  let A (t : ℝ) := (y,t • w)
  let C (t : ℝ) := (E (A t),y)
  have hD : metricPair γ y (s • w) (s • w) < R^2 :=
    (scaled_sphere_mem_normalVelocityDomain hy hw hs).2
  obtain ⟨W,hWo,hSub,hSm⟩ := hN.1
  have hpW : p ∈ W := hSub ⟨hy,hD.le⟩
  have hE := ((hSm.contDiffAt (hWo.mem_nhds hpW)).differentiableAt (by simp)).hasFDerivAt
  have hA : HasDerivAt A (0,w) s :=
    (hasDerivAt_const s y).prodMk (by simpa only [id_eq,one_smul] using (hasDerivAt_id s).smul_const w)
  have hC : HasDerivAt C (fderiv ℝ E p (0,w),0) s :=
    (hE.comp_hasDerivAt s hA).prodMk (hasDerivAt_const s y)
  have h0 := hρ.hasFDerivAt.comp_hasDerivAt s hC
  have hEq : (normalPhase γ V r ∘ C) =ᶠ[𝓝 s] fun t => (t^2-(r y)^2)/2 := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact normalPhase_radial hInv hy hw ht r
  have h1 : HasDerivAt (fun t : ℝ => (t^2-(r y)^2)/2) s s := by
    have ht : HasDerivAt (fun t : ℝ => t^2-(r y)^2) (2*s) s := by
      convert ((hasDerivAt_pow 2 s).fun_sub (hasDerivAt_const s ((r y)^2))) using 1 <;> norm_num
    convert ht.div_const (2 : ℝ) using 1 <;> ring
  exact (h1.congr_of_eventuallyEq hEq).unique h0 |> Eq.symm

end CalderonN
