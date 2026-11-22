module

public import Proof.Manuscript.GeometryClassicalRestriction

import Proof.CalderonN.CenterJetCalculus
import Proof.CalderonN.FischerIntegration
import Proof.CalderonN.LocalSmoothJetBudget
import Mathlib.Tactic

public section

noncomputable section
open CalderonN Set
open scoped ContDiff

namespace CalderonPaper

abbrev MovingSymbolGeometry (dim : ℕ) := (ℝ × (X dim × ℝ)) × ℝ

abbrev MovingSymbolFixedGeometry (dim : ℕ) := (ℝ × X dim) × ℝ

/-- Reorder the parameters so the independent radius can vary while the
geometry and the slope are fixed. The product norm is preserved. -/
@[expose] def movingSymbolSignedRadiusEquiv (dim : ℕ) :
    MovingSymbolFixedGeometry dim × ℝ ≃ₗᵢ[ℝ] MovingSymbolGeometry dim where
  toFun q := ((q.1.1.1,(q.1.1.2,q.2)),q.1.2)
  invFun q := (((q.1.1,q.1.2.1),q.2),q.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' q := by
    change ‖((q.1.1.1,(q.1.1.2,q.2)),q.1.2)‖ = ‖q‖
    simp only [Prod.norm_def]
    ac_rfl

theorem movingSymbolSignedRadiusEquiv_apply {dim : ℕ}
    (p : MovingSymbolFixedGeometry dim) (r : ℝ) :
    movingSymbolSignedRadiusEquiv dim (p,r) = ((p.1.1,(p.1.2,r)),p.2) := rfl


/-- Independent geometry variables are the metric parameter, center,
radius, and the single component of the ordinary radius derivative. -/
@[expose] def movingSymbolGeometryInput {dim : ℕ}
    (lam : ℝ) (r : X dim → ℝ) (i : I dim) (y : X dim) :
    MovingSymbolGeometry dim :=
  ((lam,(y,r y)),coordDeriv i r y)

@[expose] def movingSymbolGeometryCompact {dim : ℕ}
    (Y : Set (X dim)) (ρ B : ℝ) : Set (MovingSymbolGeometry dim) :=
  (Icc 0 1 ×ˢ (closure Y ×ˢ Icc 0 ρ)) ×ˢ Icc (-B) B

theorem isCompact_movingSymbolGeometryCompact {dim : ℕ} {Y : Set (X dim)}
    (hY : IsCompact (closure Y)) (ρ B : ℝ) :
    IsCompact (movingSymbolGeometryCompact Y ρ B) :=
  (isCompact_Icc.prod (hY.prod isCompact_Icc)).prod isCompact_Icc

theorem contDiff_movingSymbolGeometryInput {dim : ℕ} (lam : ℝ) (i : I dim)
    {r : X dim → ℝ} (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (movingSymbolGeometryInput lam r i) :=
  (contDiff_const.prodMk (contDiff_id.prodMk hr)).prodMk (contDiff_coordDeriv i r hr)

/-- Convert the established weighted radius and slope bounds into bounds for
the full geometry map, including its value and all six weighted jets. -/
theorem exists_movingSymbolGeometryInput_envelope {T : Type} {dim : ℕ}
    {Y : Set (X dim)} (hComp : IsCompact (closure Y)) (ρ : ℝ)
    (lam : T → ℝ) (r : T → X dim → ℝ) (β : T → X dim → ℝ)
    (hlam : ∀ t, lam t ∈ Icc 0 1) (hr : ∀ t, ContDiff ℝ ∞ (r t))
    (hR : ∀ t y, y ∈ Y → r t y ∈ Icc 0 ρ)
    (hβ : ∀ t y, y ∈ Y → 1 ≤ β t y)
    {B : ℝ} (hB : 1 ≤ B)
    (hRadius : ∀ t y, y ∈ Y →
      (∀ n ≤ 6, ‖iteratedFDeriv ℝ n (r t) y‖ ≤ B*(β t y)^n) ∧
      ∀ i n, n ≤ 6 → ‖iteratedFDeriv ℝ n (coordDeriv i (r t)) y‖ ≤ B*(β t y)^n) :
    ∃ D ≥ (1:ℝ), ∀ i : I dim,
      (∀ t, ContDiff ℝ ∞ (movingSymbolGeometryInput (lam t) (r t) i)) ∧
      (∀ t, MapsTo (movingSymbolGeometryInput (lam t) (r t) i) Y
        (movingSymbolGeometryCompact Y ρ B)) ∧
      ∀ t y, y ∈ Y → ∀ n ≤ 6,
        ‖iteratedFDeriv ℝ n (movingSymbolGeometryInput (lam t) (r t) i) y‖ ≤ D*(β t y)^n := by
  obtain ⟨A,hA⟩ := hComp.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (id : X dim → X dim) (closure Y))
  let D := max B A
  have hD : 1 ≤ D := hB.trans (le_max_left _ _)
  refine ⟨D,hD,fun i => ⟨fun t => contDiff_movingSymbolGeometryInput _ _ (hr t),?_,?_⟩⟩
  · intro t y hy
    have hSlope := (hRadius t y hy).2 i 0 (by omega)
    rw [norm_iteratedFDeriv_zero,pow_zero,mul_one,Real.norm_eq_abs] at hSlope
    exact ⟨⟨hlam t,⟨subset_closure hy,hR t y hy⟩⟩,
      ⟨(abs_le.mp hSlope).1,(abs_le.mp hSlope).2⟩⟩
  · intro t y hy n hn
    have hPower : 1 ≤ (β t y)^n := one_le_pow₀ (hβ t y hy)
    have hD₀ : 0 ≤ D := zero_le_one.trans hD
    have hDb : D ≤ D*(β t y)^n := le_mul_of_one_le_right hD₀ hPower
    have hLam : ‖iteratedFDeriv ℝ n (fun _ : X dim => lam t) y‖ ≤ D*(β t y)^n := by
      have hLt : ‖lam t‖ ≤ D := by
        rw [Real.norm_eq_abs,abs_of_nonneg (hlam t).1]
        exact (hlam t).2.trans hD
      have h := (LocalSmoothJetBudget.const (P := X dim) (x := y) (N := n) (lam t)).bound n le_rfl
      exact h.trans (hLt.trans hDb)
    have hY : ‖iteratedFDeriv ℝ n (fun z : X dim => z) y‖ ≤ D*(β t y)^n := by
      let L := ContinuousLinearMap.id ℝ (X dim)
      have h := norm_iteratedFDeriv_affine_envelope_at L 0 y n D hD₀
        (by
          rw [zero_add]
          exact (hA y (subset_closure hy)).trans (show A ≤ D from le_max_right B A))
        (ContinuousLinearMap.norm_id_le.trans hD)
      exact (show ‖iteratedFDeriv ℝ n (fun z : X dim => z) y‖ ≤ D from by simpa only [L,ContinuousLinearMap.id_apply,zero_add] using h).trans hDb
    have hRadius' := hRadius t y hy
    have hBD : B*(β t y)^n ≤ D*(β t y)^n :=
      mul_le_mul_of_nonneg_right (show B ≤ D from le_max_left B A)
        (pow_nonneg (zero_le_one.trans (hβ t y hy)) _)
    have hXr : ‖iteratedFDeriv ℝ n (fun z => (z,r t z)) y‖ ≤ D*(β t y)^n := by
      have h := norm_iteratedFDeriv_prod_envelope_at (fun z : X dim => z) (r t) y n
        contDiffAt_id (hr t).contDiffAt
        hY ((hRadius'.1 n hn).trans hBD)
      simpa only [max_self] using h
    have hXrSmooth : ContDiffAt ℝ ∞ (fun z => (z,r t z)) y := contDiffAt_id.prodMk (hr t).contDiffAt
    have hGeo : ‖iteratedFDeriv ℝ n (fun z => (lam t,(z,r t z))) y‖ ≤ D*(β t y)^n := by
      have h := norm_iteratedFDeriv_prod_envelope_at _ _ _ _ contDiffAt_const hXrSmooth hLam hXr
      simpa only [max_self] using h
    have hGeoSmooth : ContDiffAt ℝ ∞ (fun z => (lam t,(z,r t z))) y :=
      contDiffAt_const.prodMk hXrSmooth
    have hS := norm_iteratedFDeriv_prod_envelope_at _ _ _ _ hGeoSmooth
      (contDiff_coordDeriv i _ (hr t)).contDiffAt hGeo ((hRadius'.2 i n hn).trans hBD)
    change ‖iteratedFDeriv ℝ n (fun z => ((lam t,(z,r t z)),coordDeriv i (r t) z)) y‖ ≤ _
    simpa only [max_self] using hS

end CalderonPaper
