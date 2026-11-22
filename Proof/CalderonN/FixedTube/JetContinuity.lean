module

public import Proof.CalderonN.FixedTube.Phase

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Filter Set
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN.FixedTube

variable {dim : ℕ} {normal : I dim}

theorem contDiff_tubeHeight (M e0 : ℝ) : ContDiff ℝ ∞ (tubeHeight normal M e0) := by
  unfold tubeHeight transversePair
  have h (i : (I dim)) : ContDiff ℝ ∞ (fun y : (X dim) => y i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).contDiff
  exact ((contDiff_const.add (h normal)).add
    (contDiff_const.mul (ContDiff.sum fun i _ => (h i).mul (h i))))

theorem contDiffAt_tubePhase {M e0 a σ : ℝ} {z : (X dim) × (X dim)}
    (ht : 0 < tubeHeight normal M e0 z.2) : ContDiffAt ℝ ∞ (tubePhase normal M e0 a σ) z := by
  have h₁ := (contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd :
    ContDiff ℝ ∞ (fun w : (X dim) × (X dim) => w.1 - w.2))
  have hh := (contDiff_tubeHeight (normal := normal) M e0).comp (contDiff_snd :
    ContDiff ℝ ∞ (Prod.snd : (X dim) × (X dim) → (X dim)))
  have hpow : ContDiffAt ℝ ∞ (fun h : ℝ => h ^ (1 + σ)) (tubeHeight normal M e0 z.2) :=
    Real.contDiffAt_rpow_const_of_ne ht.ne'
  have hj := hpow.comp (f := tubeHeight normal M e0 ∘ Prod.snd) z hh.contDiffAt
  have h₂ : ContDiffAt ℝ ∞ (fun w : (X dim) × (X dim) => tubeRadius normal M e0 a σ w.2) z :=
    contDiffAt_const.mul (by simpa only [Function.comp_def] using hj)
  exact (h₁.contDiffAt.sub (h₂.pow 2)).div_const 2

private theorem continuousAt_tubeHeightDeriv_apply {D : Type*} [TopologicalSpace D]
    {p : D} {y u : D → (X dim)} (hy : ContinuousAt y p) (hu : ContinuousAt u p) (e0 : ℝ) :
    ContinuousAt (fun q => tubeHeightDeriv normal e0 (y q) (u q)) p := by
  simp only [tubeHeightDeriv_apply, transversePair]
  have cy (i : (I dim)) : ContinuousAt (fun q => y q i) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).continuous.continuousAt.comp hy
  have cu (i : (I dim)) : ContinuousAt (fun q => u q i) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).continuous.continuousAt.comp hu
  exact (cu normal).add (continuousAt_const.mul
    (tendsto_finsetSum _ fun i _ => (cy i).mul (cu i)))

private theorem continuousAt_tubeHeight_rpow {D : Type*} [TopologicalSpace D]
    {p : D} {y : D → (X dim)} (hy : ContinuousAt y p) {M e0 s : ℝ}
    (ht : 0 < tubeHeight normal M e0 (y p)) :
    ContinuousAt (fun q => tubeHeight normal M e0 (y q) ^ s) p := by
  have h : ContinuousAt (fun q => tubeHeight normal M e0 (y q)) p :=
    (contDiff_tubeHeight (normal := normal) M e0).continuous.continuousAt.comp hy
  exact (Real.continuousAt_rpow_const (tubeHeight normal M e0 (y p)) s (Or.inl ht.ne')).comp
    (f := fun q : D => tubeHeight normal M e0 (y q)) h

theorem continuousAt_tubePhase_fderiv_apply {D : Type*} [TopologicalSpace D]
    {p : D} {a : D → ℝ} {z v : D → (X dim) × (X dim)} {M e0 σ : ℝ}
    (ha : ContinuousAt a p) (hz : ContinuousAt z p) (hv : ContinuousAt v p)
    (ht : 0 < tubeHeight normal M e0 (z p).2) :
    ContinuousAt (fun q => fderiv ℝ (tubePhase normal M e0 (a q) σ) (z q) (v q)) p := by
  have hpos := ((contDiff_tubeHeight (normal := normal) M e0).continuous.continuousAt.comp hz.snd).preimage_mem_nhds
    (Ioi_mem_nhds ht)
  let F (q : D) := ⟪(z q).1 - (z q).2, (v q).1 - (v q).2⟫_ℝ -
    tubeRadius normal M e0 (a q) σ (z q).2 *
      (a q * (1 + σ) * tubeHeight normal M e0 (z q).2 ^ σ * tubeHeightDeriv normal e0 (z q).2 (v q).2)
  have hE : (fun q => fderiv ℝ (tubePhase normal M e0 (a q) σ) (z q) (v q)) =ᶠ[𝓝 p] F := by
    filter_upwards [hpos] with q hq
    exact (tube_phase_fderiv_apply (normal := normal) M e0 (a q) σ hq).2 (v q)
  apply ContinuousAt.congr_of_eventuallyEq _ hE
  have hr : ContinuousAt (fun q => tubeRadius normal M e0 (a q) σ (z q).2) p :=
    ha.mul (continuousAt_tubeHeight_rpow hz.snd ht)
  have hs : ContinuousAt (fun q => tubeHeight normal M e0 (z q).2 ^ σ) p :=
    continuousAt_tubeHeight_rpow hz.snd ht
  have hd := continuousAt_tubeHeightDeriv_apply (normal := normal) hz.snd hv.snd e0
  unfold F
  fun_prop

theorem continuousAt_tubePhase_second_apply {D : Type*} [TopologicalSpace D]
    {p : D} {a : D → ℝ} {z v w : D → (X dim) × (X dim)} {M e0 σ : ℝ}
    (ha : ContinuousAt a p) (hz : ContinuousAt z p) (hv : ContinuousAt v p)
    (hw : ContinuousAt w p) (ht : 0 < tubeHeight normal M e0 (z p).2) :
    ContinuousAt (fun q => fderiv ℝ (fderiv ℝ (tubePhase normal M e0 (a q) σ)) (z q) (v q) (w q)) p := by
  have hpos := ((contDiff_tubeHeight (normal := normal) M e0).continuous.continuousAt.comp hz.snd).preimage_mem_nhds
    (Ioi_mem_nhds ht)
  let k (q : D) := a q * (1 + σ) * tubeHeight normal M e0 (z q).2 ^ σ
  let s (q : D) := a q * (1 + σ) * σ * tubeHeight normal M e0 (z q).2 ^ (σ - 1)
  let dv (q : D) := tubeHeightDeriv normal e0 (z q).2 (v q).2
  let dw (q : D) := tubeHeightDeriv normal e0 (z q).2 (w q).2
  let F (q : D) := ⟪(v q).1 - (v q).2, (w q).1 - (w q).2⟫_ℝ -
    (k q * dv q) * (k q * dw q) -
    tubeRadius normal M e0 (a q) σ (z q).2 * (s q * dv q * dw q +
      k q * (2 * e0 * transversePair normal (v q).2 (w q).2))
  have hE : (fun q => fderiv ℝ (fderiv ℝ (tubePhase normal M e0 (a q) σ)) (z q) (v q) (w q)) =ᶠ[𝓝 p] F := by
    filter_upwards [hpos] with q hq
    obtain ⟨A,hA,hAe⟩ := tube_phase_second_jet (normal := normal) M e0 (a q) σ hq
    rw [hA.fderiv]
    exact hAe (v q) (w q)
  apply ContinuousAt.congr_of_eventuallyEq _ hE
  have hr : ContinuousAt (fun q => tubeRadius normal M e0 (a q) σ (z q).2) p :=
    ha.mul (continuousAt_tubeHeight_rpow hz.snd ht)
  have hk : ContinuousAt k p := (ha.mul continuousAt_const).mul
    (continuousAt_tubeHeight_rpow hz.snd ht)
  have hs : ContinuousAt s p := ((ha.mul continuousAt_const).mul continuousAt_const).mul
    (continuousAt_tubeHeight_rpow hz.snd ht)
  have hdv : ContinuousAt dv p := continuousAt_tubeHeightDeriv_apply (normal := normal) hz.snd hv.snd e0
  have hdw : ContinuousAt dw p := continuousAt_tubeHeightDeriv_apply (normal := normal) hz.snd hw.snd e0
  have cv (i : (I dim)) : ContinuousAt (fun q => (v q).2 i) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).continuous.continuousAt.comp hv.snd
  have cw (i : (I dim)) : ContinuousAt (fun q => (w q).2 i) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).continuous.continuousAt.comp hw.snd
  have hTransverse : ContinuousAt (fun q => transversePair normal (v q).2 (w q).2) p :=
    tendsto_finsetSum _ fun i _ => (cv i).mul (cw i)
  unfold F
  fun_prop

end CalderonN.FixedTube
