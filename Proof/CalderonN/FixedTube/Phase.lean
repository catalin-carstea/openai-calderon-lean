module

public import Proof.CalderonN.FixedTube.Flat

import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
Adapted from `Calderon/MixedKernelConstruction/MixedKernelClosedTubeConstruction.lean`
in `anisotropic-calderon-lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc.
These are the fixed-separation tube calculations used in Theorem 3.1.
-/

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped InnerProductSpace Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} {normal : I dim}

/-- Pairing of the coordinates perpendicular to the selected normal axis. -/
def transversePair (normal : I dim) (u v : X dim) : ℝ :=
  ∑ i ∈ Finset.univ.erase normal, u i * v i

private theorem transversePair_self (normal : I dim) (v : X dim) :
    transversePair normal v v = ∑ i ∈ Finset.univ.erase normal, v i ^ 2 := by
  simp only [transversePair, pow_two]

theorem transversePair_nonneg (normal : I dim) (v : X dim) :
    0 ≤ transversePair normal v v := by
  rw [transversePair_self]
  exact Finset.sum_nonneg fun i _ => sq_nonneg (v i)

theorem norm_sq_eq_transversePair (normal : I dim) (v : X dim) :
    ‖v‖^2 = transversePair normal v v + v normal ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, transversePair_self,
    Finset.sum_erase_add _ _ (Finset.mem_univ normal)]

theorem transversePair_le_norm_sq (normal : I dim) (v : X dim) :
    transversePair normal v v ≤ ‖v‖^2 := by
  rw [norm_sq_eq_transversePair normal]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem norm_eq_transversePair (normal : I dim) (v : X dim) :
    ‖v‖ = Real.sqrt (transversePair normal v v + v normal ^ 2) := by
  rw [← norm_sq_eq_transversePair normal, Real.sqrt_sq (norm_nonneg _)]

theorem transversePair_smul_same (normal : I dim) (c : ℝ) (v : X dim) :
    transversePair normal (c • v) (c • v) = c^2 * transversePair normal v v := by
  simp only [transversePair, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem transversePair_neg_same (normal : I dim) (v : X dim) :
    transversePair normal (-v) (-v) = transversePair normal v v := by
  simp [transversePair, PiLp.neg_apply]

/-- The tube height uses the squared norm of the transverse coordinates. -/
def tubeHeight (normal : I dim) (M e0 : ℝ) (Y : X dim) : ℝ :=
  M + Y normal + e0 * transversePair normal Y Y

def tubeRadius (normal : I dim) (M e0 a σ : ℝ) (Y : X dim) : ℝ :=
  a * tubeHeight normal M e0 Y ^ (1 + σ)

def tubePhase (normal : I dim) (M e0 a σ : ℝ) (z : X dim × X dim) : ℝ :=
  (‖z.1 - z.2‖ ^ 2 - tubeRadius normal M e0 a σ z.2 ^ 2) / 2

/-- The ordinary differential of the fixed tube height. -/
def tubeHeightDeriv (normal : I dim) (e0 : ℝ) (Y : X dim) : X dim →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) normal +
    ∑ i ∈ Finset.univ.erase normal, (2 * e0 * Y i) • EuclideanSpace.proj (𝕜 := ℝ) i

theorem tubeHeightDeriv_apply (e0 : ℝ) (Y U : X dim) :
    tubeHeightDeriv normal e0 Y U = U normal + 2 * e0 * transversePair normal Y U := by
  simp only [tubeHeightDeriv, transversePair, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    PiLp.proj_apply, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem tube_height_hasFDerivAt (M e0 : ℝ) (Y : X dim) :
    HasFDerivAt (tubeHeight normal M e0) (tubeHeightDeriv normal e0 Y) Y := by
  let p (i : I dim) : X dim →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) i
  have hs := HasFDerivAt.sum (u := Finset.univ.erase normal) (fun i _ =>
    (((p i).hasFDerivAt (x := Y)).pow 2).const_mul e0)
  have hb := ((p normal).hasFDerivAt (x := Y)).const_add M
  have ht := hb.add hs
  have hf : ((fun x : X dim => M + p normal x) +
      ∑ i ∈ Finset.univ.erase normal, fun x => e0 * p i x ^ 2) = tubeHeight normal M e0 := by
    funext x
    simp only [Pi.add_apply, Finset.sum_apply, tubeHeight, transversePair_self, Finset.mul_sum,
      p, PiLp.proj_apply]
  rw [hf] at ht
  refine ht.congr_fderiv (ContinuousLinearMap.ext fun U => ?_)
  rw [tubeHeightDeriv_apply]
  simp only [p, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, PiLp.proj_apply, pow_one, Finset.mul_sum,
    transversePair]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- on `t > 0`, `Dr = a (1+σ) t^σ dt`. -/
theorem tube_radius_hasFDerivAt (M e0 a σ : ℝ) {Y : (X dim)} (ht : 0 < tubeHeight normal M e0 Y) :
    HasFDerivAt (tubeRadius normal M e0 a σ)
      ((a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightDeriv normal e0 Y) Y := by
  have h := ((tube_height_hasFDerivAt (normal := normal) M e0 Y).rpow_const (p := 1 + σ)
    (Or.inl ht.ne')).const_mul a
  have hs : (1 + σ - 1) = σ := by ring
  rw [hs, smul_smul] at h
  have hc : a * ((1 + σ) * tubeHeight normal M e0 Y ^ σ) = a * (1 + σ) * tubeHeight normal M e0 Y ^ σ := by
    ring
  rw [hc] at h
  exact h

/-- on `t(Y) > 0`, `Dρ((X dim),Y)(W₁,W₂) = ⟪(X dim)-Y, W₁-W₂⟫ - r Dr(W₂)`. -/
theorem tube_phase_fderiv_apply (M e0 a σ : ℝ) {x Y : (X dim)} (ht : 0 < tubeHeight normal M e0 Y) :
    DifferentiableAt ℝ (tubePhase normal M e0 a σ) (x, Y) ∧ ∀ W : (X dim) × (X dim),
      fderiv ℝ (tubePhase normal M e0 a σ) (x, Y) W = ⟪x - Y, W.1 - W.2⟫_ℝ -
        tubeRadius normal M e0 a σ Y *
          (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * tubeHeightDeriv normal e0 Y W.2) := by
  have hd : HasFDerivAt (fun z : (X dim) × (X dim) => z.1 - z.2)
      (ContinuousLinearMap.fst ℝ (X dim) (X dim) - ContinuousLinearMap.snd ℝ (X dim) (X dim)) (x, Y) :=
    hasFDerivAt_fst.sub hasFDerivAt_snd
  have hn := hd.norm_sq
  have hs : HasFDerivAt (Prod.snd : (X dim) × (X dim) → (X dim)) (ContinuousLinearMap.snd ℝ (X dim) (X dim)) (x, Y) :=
    hasFDerivAt_snd
  have hr0 : HasFDerivAt (tubeRadius normal M e0 a σ)
      ((a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightDeriv normal e0 Y) (Prod.snd (x, Y)) :=
    tube_radius_hasFDerivAt (normal := normal) M e0 a σ ht
  have hr : HasFDerivAt (fun z : (X dim) × (X dim) => tubeRadius normal M e0 a σ z.2)
      (((a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightDeriv normal e0 Y).comp
        (ContinuousLinearMap.snd ℝ (X dim) (X dim))) (x, Y) :=
    hr0.comp (x, Y) hs
  have h := (hn.sub (hr.pow 2)).const_mul (1 / 2 : ℝ)
  have hf : tubePhase normal M e0 a σ = fun z : (X dim) × (X dim) =>
      (1 / 2 : ℝ) * (‖z.1 - z.2‖ ^ 2 - tubeRadius normal M e0 a σ z.2 ^ 2) := by
    funext z
    simp only [tubePhase]
    ring
  rw [hf]
  refine ⟨h.differentiableAt, fun W => ?_⟩
  have hD : fderiv ℝ (fun z : (X dim) × (X dim) =>
      (1 / 2 : ℝ) * (‖z.1 - z.2‖ ^ 2 - tubeRadius normal M e0 a σ z.2 ^ 2)) (x, Y) = _ := h.fderiv
  rw [hD]
  simp [inner_sub_left, inner_sub_right]
  ring

/-- The Hessian of the tube height is twice the transverse pairing times e₀. -/
theorem tube_height_deriv_hasFDerivAt (e0 : ℝ) (Y : X dim) :
    ∃ D : X dim →L[ℝ] X dim →L[ℝ] ℝ, HasFDerivAt (tubeHeightDeriv normal e0) D Y ∧
      ∀ V U : X dim, D V U = 2 * e0 * transversePair normal V U := by
  let p (i : I dim) : X dim →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) i
  have hs := HasFDerivAt.sum (u := Finset.univ.erase normal) (fun i _ =>
    (((p i).hasFDerivAt (x := Y)).const_mul (2 * e0)).smul_const (p i))
  have ht := (hasFDerivAt_const (p normal) Y).add hs
  have hf : ((fun _ : X dim => p normal) +
      ∑ i ∈ Finset.univ.erase normal, fun x => (2 * e0 * p i x) • p i) =
        tubeHeightDeriv normal e0 := by
    funext x
    simp only [Pi.add_apply, Finset.sum_apply, tubeHeightDeriv, p, PiLp.proj_apply]
  rw [hf] at ht
  refine ⟨_, ht, fun V U => ?_⟩
  simp only [p, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.zero_apply, zero_apply, zero_add, PiLp.proj_apply, transversePair, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- on `t > 0`, the true derivative of `Y ↦ Dr_Y = a(1+σ) t^σ dt_Y` is
`D²r(V)(U) = a(1+σ) σ t^(σ-1) dt(V) dt(U) + a(1+σ) t^σ D²t(V)(U)`. -/
theorem tube_radius_deriv_hasFDerivAt (M e0 a σ : ℝ) {Y : (X dim)} (ht : 0 < tubeHeight normal M e0 Y) :
    ∃ D : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ,
      HasFDerivAt (fun Y' : (X dim) => (a * (1 + σ) * tubeHeight normal M e0 Y' ^ σ) • tubeHeightDeriv normal e0 Y')
        D Y ∧
      ∀ V U : (X dim), D V U = a * (1 + σ) * σ * tubeHeight normal M e0 Y ^ (σ - 1) *
          tubeHeightDeriv normal e0 Y V * tubeHeightDeriv normal e0 Y U +
        a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * (2 * e0 * transversePair normal V U) := by
  obtain ⟨D2, hD2, hD2e⟩ := tube_height_deriv_hasFDerivAt (normal := normal) e0 Y
  have hk := ((tube_height_hasFDerivAt (normal := normal) M e0 Y).rpow_const (p := σ) (Or.inl ht.ne')).const_mul
    (a * (1 + σ))
  refine ⟨_, hk.smul hD2, fun V U => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hD2e]
  ring

open scoped Topology in
/-- J6(a,b): on a neighborhood of `((X dim),Y)` with `t(Y) > 0`, the pair phase has the explicit first jet
`G z = ⟪z₁-z₂, ·₁-·₂⟫ - r(z₂) k(z₂) dt_{z₂}(·₂)`, `k = a(1+σ) t^σ`. -/
theorem tube_phase_hasFDerivAt_eventually (M e0 a σ : ℝ) {x Y : (X dim)}
    (ht : 0 < tubeHeight normal M e0 Y) :
    ∀ᶠ z in 𝓝 (x, Y), HasFDerivAt (tubePhase normal M e0 a σ)
      ((innerSL ℝ (z.1 - z.2)).comp
          (ContinuousLinearMap.fst ℝ (X dim) (X dim) - ContinuousLinearMap.snd ℝ (X dim) (X dim)) -
        (tubeRadius normal M e0 a σ z.2 * (a * (1 + σ) * tubeHeight normal M e0 z.2 ^ σ)) •
          (tubeHeightDeriv normal e0 z.2).comp (ContinuousLinearMap.snd ℝ (X dim) (X dim))) z := by
  have hcont : ContinuousAt (fun z : (X dim) × (X dim) => tubeHeight normal M e0 z.2) (x, Y) :=
    ContinuousAt.comp (f := Prod.snd) (x := (x, Y))
      (tube_height_hasFDerivAt (normal := normal) M e0 Y).continuousAt continuousAt_snd
  have hev : ∀ᶠ z in 𝓝 (x, Y), 0 < tubeHeight normal M e0 z.2 := hcont.eventually (lt_mem_nhds ht)
  refine hev.mono fun z hz => ?_
  have hd : HasFDerivAt (fun w : (X dim) × (X dim) => w.1 - w.2)
      (ContinuousLinearMap.fst ℝ (X dim) (X dim) - ContinuousLinearMap.snd ℝ (X dim) (X dim)) z :=
    hasFDerivAt_fst.sub hasFDerivAt_snd
  have hn := hd.norm_sq
  have hs : HasFDerivAt (Prod.snd : (X dim) × (X dim) → (X dim)) (ContinuousLinearMap.snd ℝ (X dim) (X dim)) z :=
    hasFDerivAt_snd
  have hr0 : HasFDerivAt (tubeRadius normal M e0 a σ)
      ((a * (1 + σ) * tubeHeight normal M e0 z.2 ^ σ) • tubeHeightDeriv normal e0 z.2) (Prod.snd z) :=
    tube_radius_hasFDerivAt (normal := normal) M e0 a σ hz
  have hr : HasFDerivAt (fun w : (X dim) × (X dim) => tubeRadius normal M e0 a σ w.2)
      (((a * (1 + σ) * tubeHeight normal M e0 z.2 ^ σ) • tubeHeightDeriv normal e0 z.2).comp
        (ContinuousLinearMap.snd ℝ (X dim) (X dim))) z :=
    hr0.comp z hs
  have h := (hn.sub (hr.pow 2)).const_mul (1 / 2 : ℝ)
  have hf : tubePhase normal M e0 a σ = fun w : (X dim) × (X dim) =>
      (1 / 2 : ℝ) * (‖w.1 - w.2‖ ^ 2 - tubeRadius normal M e0 a σ w.2 ^ 2) := by
    funext w
    simp only [tubePhase]
    ring
  rw [hf]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun W => ?_)
  simp [inner_sub_left, inner_sub_right]
  ring

open scoped Topology in
/-- J6(c,d): the true second jet of the actual pair phase on `t(Y) > 0`:
`D²ρ(W,V) = ⟪W₁-W₂,V₁-V₂⟫ - Dr(W₂)Dr(V₂) - r D²r(W₂,V₂)`. -/
theorem tube_phase_second_jet (M e0 a σ : ℝ) {x Y : (X dim)} (ht : 0 < tubeHeight normal M e0 Y) :
    ∃ D : (X dim) × (X dim) →L[ℝ] (X dim) × (X dim) →L[ℝ] ℝ,
      HasFDerivAt (fderiv ℝ (tubePhase normal M e0 a σ)) D (x, Y) ∧ ∀ W V : (X dim) × (X dim),
        D W V = ⟪W.1 - W.2, V.1 - V.2⟫_ℝ -
          (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * tubeHeightDeriv normal e0 Y W.2) *
            (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * tubeHeightDeriv normal e0 Y V.2) -
          tubeRadius normal M e0 a σ Y * (a * (1 + σ) * σ * tubeHeight normal M e0 Y ^ (σ - 1) *
              tubeHeightDeriv normal e0 Y W.2 * tubeHeightDeriv normal e0 Y V.2 +
            a * (1 + σ) * tubeHeight normal M e0 Y ^ σ *
              (2 * e0 * transversePair normal W.2 V.2)) := by
  have hEv := (tube_phase_hasFDerivAt_eventually (normal := normal) M e0 a σ (x := x) ht).mono
    fun z hz => hz.fderiv
  have hd : HasFDerivAt (fun z : (X dim) × (X dim) => z.1 - z.2)
      (ContinuousLinearMap.fst ℝ (X dim) (X dim) - ContinuousLinearMap.snd ℝ (X dim) (X dim)) (x, Y) :=
    hasFDerivAt_fst.sub hasFDerivAt_snd
  have hI0 : HasFDerivAt (fun v : (X dim) => (innerSL ℝ v : (X dim) →L[ℝ] ℝ))
      (innerSL ℝ : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ) ((fun z : (X dim) × (X dim) => z.1 - z.2) (x, Y)) :=
    (innerSL ℝ : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ).hasFDerivAt
  have hI := hI0.comp (x, Y) hd
  have hA := hI.clm_comp (hasFDerivAt_const
    (ContinuousLinearMap.fst ℝ (X dim) (X dim) - ContinuousLinearMap.snd ℝ (X dim) (X dim)) (x, Y))
  have hs : HasFDerivAt (Prod.snd : (X dim) × (X dim) → (X dim)) (ContinuousLinearMap.snd ℝ (X dim) (X dim)) (x, Y) :=
    hasFDerivAt_snd
  have hr0 : HasFDerivAt (tubeRadius normal M e0 a σ)
      ((a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightDeriv normal e0 Y) (Prod.snd (x, Y)) :=
    tube_radius_hasFDerivAt (normal := normal) M e0 a σ ht
  have hk0 : HasFDerivAt (fun Y' : (X dim) => a * (1 + σ) * tubeHeight normal M e0 Y' ^ σ)
      ((a * (1 + σ)) • ((σ * tubeHeight normal M e0 Y ^ (σ - 1)) • tubeHeightDeriv normal e0 Y))
      (Prod.snd (x, Y)) :=
    ((tube_height_hasFDerivAt (normal := normal) M e0 Y).rpow_const (p := σ) (Or.inl ht.ne')).const_mul
      (a * (1 + σ))
  obtain ⟨D2, hD2, hD2e⟩ := tube_height_deriv_hasFDerivAt (normal := normal) e0 Y
  have hD20 : HasFDerivAt (tubeHeightDeriv normal e0) D2 (Prod.snd (x, Y)) := hD2
  have hc := (hr0.comp (x, Y) hs).mul (hk0.comp (x, Y) hs)
  have hT := (hD20.comp (x, Y) hs).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.snd ℝ (X dim) (X dim)) (x, Y))
  have hG := hA.sub (hc.smul hT)
  have hi : ∀ u w : (X dim), (innerSL ℝ : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ) u w = ⟪u, w⟫_ℝ := fun u w => rfl
  refine ⟨_, hG.congr_of_eventuallyEq hEv, fun W V => ?_⟩
  simp [hD2e, hi, inner_sub_left, inner_sub_right] <;> ring

/-- Coordinate gradient of the tube height. -/
def tubeHeightGrad (normal : I dim) (e0 : ℝ) (Y : X dim) : X dim :=
  WithLp.toLp 2 fun i => if i = normal then 1 else 2 * e0 * Y i

theorem tubeHeightGrad_normal (e0 : ℝ) (Y : X dim) : tubeHeightGrad normal e0 Y normal = 1 := by
  simp [tubeHeightGrad]

theorem tubeHeightDeriv_eq_inner (e0 : ℝ) (Y U : X dim) :
    tubeHeightDeriv normal e0 Y U = ⟪tubeHeightGrad normal e0 Y, U⟫_ℝ := by
  rw [tubeHeightDeriv_apply, PiLp.inner_apply]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ normal)]
  simp only [tubeHeightGrad, PiLp.toLp_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    if_true, mul_one, one_mul, transversePair, Finset.mul_sum]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by
    rw [if_neg (Finset.ne_of_mem_erase hi)]
    ring

/-- at `(X dim) = Y + r ω` the two partial first jets are `r⟪ω,·⟫` and `-r⟪ω + b,·⟫`, `b = k g_Y`. -/
theorem tube_phase_partial_jets (M e0 a σ : ℝ) {Y ω : (X dim)} (ht : 0 < tubeHeight normal M e0 Y)
    (W1 W2 : (X dim)) :
    fderiv ℝ (tubePhase normal M e0 a σ) (Y + tubeRadius normal M e0 a σ Y • ω, Y) (W1, 0) =
        tubeRadius normal M e0 a σ Y * ⟪ω, W1⟫_ℝ ∧
      fderiv ℝ (tubePhase normal M e0 a σ) (Y + tubeRadius normal M e0 a σ Y • ω, Y) (0, W2) =
        -(tubeRadius normal M e0 a σ Y *
          ⟪ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y, W2⟫_ℝ) := by
  obtain ⟨-, hJ⟩ := tube_phase_fderiv_apply (normal := normal) M e0 a σ (x := Y + tubeRadius normal M e0 a σ Y • ω) ht
  refine ⟨?_, ?_⟩
  · rw [hJ]
    simp [inner_smul_left]
  · rw [hJ, tubeHeightDeriv_eq_inner]
    simp [inner_smul_left, inner_add_left, inner_neg_right]
    ring

/-- the Hessian sum at `(P,-Q)` and `(V₁,V₂)` for the J6 second-jet formula. -/
theorem tube_phase_hessian_sum {D : (X dim) × (X dim) →L[ℝ] (X dim) × (X dim) →L[ℝ] ℝ} {d : (X dim) →L[ℝ] ℝ}
    {k s rr e0 : ℝ}
    (hD : ∀ W V : (X dim) × (X dim), D W V = ⟪W.1 - W.2, V.1 - V.2⟫_ℝ - (k * d W.2) * (k * d V.2) -
      rr * (s * d W.2 * d V.2 + k * (2 * e0 * transversePair normal W.2 V.2)))
    (P Q V1 V2 : (X dim)) :
    D (P, -Q) (P, -Q) + D (V1, V2) (V1, V2) =
      ⟪P + Q, P + Q⟫_ℝ + ⟪V1 - V2, V1 - V2⟫_ℝ - (k * d Q) ^ 2 - (k * d V2) ^ 2 -
        rr * (s * d Q ^ 2 + k * (2 * e0 * transversePair normal Q Q) +
          s * d V2 ^ 2 + k * (2 * e0 * transversePair normal V2 V2)) := by
  rw [hD, hD]
  have hneg : transversePair normal (-Q) (-Q) = transversePair normal Q Q := by
    simp [transversePair, PiLp.neg_apply]
  simp only [map_neg, sub_neg_eq_add, hneg]
  ring

theorem tube_horizontal_sq_le (normal : I dim) (Q : X dim) :
    transversePair normal Q Q ≤ 2 * ‖Q‖ ^ 2 := by
  rw [transversePair_self, EuclideanSpace.real_norm_sq_eq]
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset normal (Finset.univ : Finset (I dim)))
    (f := fun i : I dim => Q i ^ 2) (fun i _ _ => sq_nonneg (Q i))
  linarith [Finset.sum_nonneg (s := (Finset.univ : Finset (I dim))) (fun i _ => sq_nonneg (Q i))]

/-- `|dt_Y(U)| ≤ ‖g_Y‖ ‖U‖`. -/
theorem tube_height_deriv_abs_le (e0 : ℝ) (Y U : (X dim)) :
    |tubeHeightDeriv normal e0 Y U| ≤ ‖tubeHeightGrad normal e0 Y‖ * ‖U‖ := by
  rw [tubeHeightDeriv_eq_inner]
  exact abs_real_inner_le_norm _ _

end CalderonN.FixedTube
