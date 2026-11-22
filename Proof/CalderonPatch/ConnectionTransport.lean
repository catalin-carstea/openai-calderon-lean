module

public import Proof.CalderonN.MetricCompatibility

import Proof.CalderonN.MetricConnection
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

public section

noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (X MetricField metricPair metricBilinear metricBilinear_apply connection)

variable {n : ℕ} [NeZero n]

/-- The Christoffel transformation law for the same coordinate
connection used in the checked geodesic flow. -/
theorem connection_transport {g h : MetricField n} {U V : Set (X n)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hg : CalderonN.SmoothMetric U g) (hh : CalderonN.SmoothMetric V h)
    {f : X n → X n} (hf : ContDiffOn ℝ ∞ f U) (hUV : MapsTo f U V)
    {x : X n} (hx : x ∈ U) (hSurj : Function.Surjective (fderiv ℝ f x))
    (hMetric : ∀ y ∈ U, ∀ u v, metricPair g y u v =
      metricPair h (f y) (fderiv ℝ f y u) (fderiv ℝ f y v)) (u v : X n) :
    fderiv ℝ (fderiv ℝ f) x u v + connection h (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) =
      fderiv ℝ f x (connection g x u v) := by
  let D := fderiv ℝ f
  let A := fderiv ℝ D x
  let B (a b : X n) : X n := (A a b + connection h (f x) (D x a) (D x b)) -
    D x (connection g x a b)
  have hfc := hf.contDiffAt (hU.mem_nhds hx)
  have hD : HasFDerivAt D A x :=
    ((hfc.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero).hasFDerivAt
  have hSym (a b : X n) : B a b = B b a := by
    have ha : A a b = A b a := hfc.isSymmSndFDerivAt (by simp) a b
    unfold B
    rw [ha, CalderonN.connection_comm hU hg hx a b,
      CalderonN.connection_comm hV hh (hUV hx) (D x a) (D x b)]
  have hSkew (a b c : X n) :
      metricPair h (f x) (B a b) (D x c) + metricPair h (f x) (D x b) (B a c) = 0 := by
    let q : ℝ → X n := fun t => x + t • a
    have hq : HasDerivAt q a 0 := by
      simpa only [id_eq, zero_add, one_smul] using
        HasDerivAt.fun_add (hasDerivAt_const (0 : ℝ) x) ((hasDerivAt_id (0 : ℝ)).smul_const a)
    have hq₀ : q 0 = x := by simp [q]
    have hd : HasFDerivAt f (D x) (q 0) :=
      hq₀.symm ▸ (hfc.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasFDerivAt
    have hF : HasDerivAt (f ∘ q) (D x a) 0 := hd.comp_hasDerivAt 0 hq
    have hDA : HasFDerivAt D A (q 0) := hq₀.symm ▸ hD
    have hW (d : X n) : HasDerivAt (fun t => D (q t) d) (A a d) 0 :=
      (ContinuousLinearMap.apply ℝ (X n) d).hasFDerivAt.comp_hasDerivAt _
        (hDA.comp_hasDerivAt 0 hq)
    have hg' := CalderonN.hasDerivAt_metricPair hU hg (hq₀.symm ▸ hx) hq
      (hasDerivAt_const (0 : ℝ) b) (hasDerivAt_const (0 : ℝ) c)
    have hh' := CalderonN.hasDerivAt_metricPair hV hh (hUV (hq₀.symm ▸ hx)) hF (hW b) (hW c)
    have hEq :
        (fun t => metricPair g (q t) b c) =ᶠ[𝓝 (0 : ℝ)]
          (fun t => metricPair h (f (q t)) (D (q t) b) (D (q t) c)) := by
      filter_upwards [hq.continuousAt.eventually_mem (hq₀.symm ▸ hU.mem_nhds hx)] with t ht
      exact hMetric _ ht b c
    have he := (hg'.congr_of_eventuallyEq hEq.symm).unique hh'
    simp only [hq₀, zero_add, Function.comp_apply] at he
    rw [hMetric _ hx (connection g x a b) c, hMetric _ hx b (connection g x a c)] at he
    simp only [B, ← metricBilinear_apply, map_sub, sub_apply] at he ⊢
    linarith only [he]
  have hZero (b c d : X n) : metricPair h (f x) (B b c) (D x d) = 0 := by
    have h₁ := hSkew b c d
    have h₂ := hSkew c d b
    have h₃ := hSkew d b c
    have hp := hh.2 _ (hUV hx)
    rw [CalderonN.metricPair_comm hp (D x c), hSym b d] at h₁
    rw [CalderonN.metricPair_comm hp (D x d), hSym c b] at h₂
    rw [CalderonN.metricPair_comm hp (D x b), hSym d c] at h₃
    linarith only [h₁,h₂,h₃]
  apply sub_eq_zero.mp
  change B u v = 0
  by_contra hn
  obtain ⟨w, hw⟩ := hSurj (B u v)
  have he := hZero u v w
  change D x w = B u v at hw
  rw [hw] at he
  exact (CalderonN.metricPair_pos_of_posDef (hh.2 _ (hUV hx)) hn).ne' he

/-- A coordinate metric isometry transports the classical geodesic
equation at interior times. -/
theorem hasDerivAt_transported_geodesic_velocity {g h : MetricField n} {U V : Set (X n)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hg : CalderonN.SmoothMetric U g) (hh : CalderonN.SmoothMetric V h)
    {f : X n → X n} (hf : ContDiffOn ℝ ∞ f U) (hUV : MapsTo f U V)
    (hSurj : ∀ x ∈ U, Function.Surjective (fderiv ℝ f x))
    (hMetric : ∀ y ∈ U, ∀ u v, metricPair g y u v =
      metricPair h (f y) (fderiv ℝ f y u) (fderiv ℝ f y v))
    {q v : ℝ → X n} {t : ℝ} (hqt : q t ∈ U)
    (hq : HasDerivAt q (v t) t)
    (hv : HasDerivAt v (-connection g (q t) (v t) (v t)) t) :
    HasDerivAt (fun s => fderiv ℝ f (q s) (v s))
      (-connection h (f (q t)) (fderiv ℝ f (q t) (v t)) (fderiv ℝ f (q t) (v t))) t := by
  have hfc := hf.contDiffAt (hU.mem_nhds hqt)
  have hD := (hfc.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  have h := (hD.hasFDerivAt.comp_hasDerivAt t hq).clm_apply hv
  have hc := connection_transport hU hV hg hh hf hUV hqt (hSurj _ hqt) hMetric (v t) (v t)
  apply h.congr_deriv
  simp only [Function.comp_apply, map_neg]
  rw [← hc]
  abel

end CalderonPatch
