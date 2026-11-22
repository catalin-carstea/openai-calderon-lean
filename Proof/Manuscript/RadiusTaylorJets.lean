module

public import Proof.CalderonN.LocalJetIntegral
public import Proof.CalderonN.LocalMixedParameterJetCalculus

import Proof.CalderonN.FiniteJetBoundCalculus
import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter MeasureTheory Set
open scoped ContDiff Topology

namespace CalderonPaper

variable {P V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Second derivative in the independent radius with all other arguments fixed. -/
@[expose] def radiusSecondDerivative (a : P × ℝ → V) : P × ℝ → V :=
  radialFirstDerivative (radialFirstDerivative a)

/-- The literal second-order Taylor remainder in the independent radius. -/
@[expose] def radiusTaylorRemainder (a : P × ℝ → V) (q : P × ℝ) : V :=
  ∫ t in (0:ℝ)..1, (1 - t) • radiusSecondDerivative a (q.1, t * q.2)

@[expose] def radiusSegment (O : Set (P × ℝ)) : Set (P × ℝ) :=
  {q | ∀ t ∈ Icc (0:ℝ) 1, (q.1, t * q.2) ∈ O}

/-- Taylor in the independent radius, including equality at the degenerate radius. -/
theorem radius_taylor_eq {O : Set (P × ℝ)} (hO : IsOpen O)
    [CompleteSpace V] {a : P × ℝ → V} (ha : ContDiffOn ℝ ∞ a O)
    {q : P × ℝ} (hq : q ∈ radiusSegment O) :
    a q = a (q.1, 0) + q.2 • radialFirstDerivative a (q.1, 0) +
      q.2 ^ 2 • radiusTaylorRemainder a q := by
  have hLine (t : ℝ) : ((q.1, (0:ℝ)) : P × ℝ) + (t * q.2) • (0, 1) = (q.1, t * q.2) := by
    simp
  have hTaylor := affineLine_second_taylor_integral_unit hO ha (p := (q.1, 0))
    (w := ((0:P), (1:ℝ))) q.2 (fun t ht => (hLine t).symm ▸ hq t ht)
  have hEnd : ((q.1, (0:ℝ)) : P × ℝ) + q.2 • (0, 1) = q := by
    rw [← one_mul q.2, hLine 1, one_mul]
  rw [hEnd] at hTaylor
  have hR : (∫ t in (0:ℝ)..1, (1-t) •
        fderiv ℝ (fderiv ℝ a) (q.1,t*q.2) (0,1) (0,1)) = radiusTaylorRemainder a q := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hDiff := (ha.fderiv_of_isOpen (m:=∞) hO (by simp)).differentiableOn (by simp)
      (q.1,t*q.2) (hq t ht)
    have hDiff' := hDiff.differentiableAt (hO.mem_nhds (hq t ht))
    change (1-t) • _ = (1-t) • radiusSecondDerivative a (q.1,t*q.2)
    apply congrArg ((1-t) • ·)
    change _ = fderiv ℝ (fun z => fderiv ℝ a z ((0:P),(1:ℝ))) (q.1,t*q.2) (0,1)
    rw [fderiv_clm_apply hDiff' (differentiableAt_const _)]
    simp
  simpa only [hLine, hR, radialFirstDerivative] using hTaylor

theorem contDiffOn_radialFirstDerivative {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} (ha : ContDiffOn ℝ ∞ a O) :
    ContDiffOn ℝ ∞ (radialFirstDerivative a) O :=
  (ha.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_radiusSecondDerivative {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} (ha : ContDiffOn ℝ ∞ a O) :
    ContDiffOn ℝ ∞ (radiusSecondDerivative a) O :=
  contDiffOn_radialFirstDerivative hO (contDiffOn_radialFirstDerivative hO ha)

theorem norm_iteratedFDeriv_radialFirstDerivative_le
    {a : P × ℝ → V} {q : P × ℝ} (ha : ContDiffAt ℝ ∞ a q) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (radialFirstDerivative a) q‖ ≤ ‖iteratedFDeriv ℝ (j+1) a q‖ := by
  have h := norm_iteratedFDeriv_clm_apply_const (n := j) (c := ((0:P), (1:ℝ)))
    (ha.fderiv_right (m := ∞) (by simp)) (by simp)
  change ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ a y ((0:P), (1:ℝ))) q‖ ≤ _
  simpa only [norm_iteratedFDeriv_fderiv, Prod.norm_def, norm_zero, norm_one, zero_le_one,
    max_eq_right, one_mul, radialFirstDerivative] using h

theorem norm_iteratedFDeriv_radiusSecondDerivative_le
    {a : P × ℝ → V} {q : P × ℝ} (ha : ContDiffAt ℝ ∞ a q) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (radiusSecondDerivative a) q‖ ≤ ‖iteratedFDeriv ℝ (j+2) a q‖ := by
  have hSmooth : ContDiffAt ℝ ∞ (radialFirstDerivative a) q :=
    (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  exact (norm_iteratedFDeriv_radialFirstDerivative_le hSmooth j).trans
    (norm_iteratedFDeriv_radialFirstDerivative_le ha (j+1))

private def radiusDilation (t : ℝ) : (P × ℝ) →L[ℝ] (P × ℝ) :=
  (ContinuousLinearMap.fst ℝ P ℝ).prod (t • ContinuousLinearMap.snd ℝ P ℝ)

private theorem radiusDilation_apply (t : ℝ) (q : P × ℝ) :
    radiusDilation t q = (q.1, t*q.2) := rfl

private theorem radiusDilation_norm_le (t : ℝ) (ht : |t| ≤ 1) :
    ‖(radiusDilation t : (P × ℝ) →L[ℝ] (P × ℝ))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  rw [one_mul, radiusDilation_apply, Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, abs_mul]
  exact max_le (le_max_left _ _)
    ((mul_le_of_le_one_left (abs_nonneg _) ht).trans (le_max_right _ _))

private theorem norm_iteratedFDeriv_comp_contraction
    {P' : Type*} [NormedAddCommGroup P'] [NormedSpace ℝ P']
    (L : P' →L[ℝ] (P × ℝ)) (hL : ‖L‖ ≤ 1)
    {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} (ha : ContDiffOn ℝ ∞ a O) {q : P'} (hq : L q ∈ O) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (a ∘ L) q‖ ≤ ‖iteratedFDeriv ℝ j a (L q)‖ := by
  have hPre := hO.preimage L.continuous
  have hqPre : q ∈ L ⁻¹' O := hq
  rw [← iteratedFDerivWithin_of_isOpen (s := L ⁻¹' O) j hPre hqPre,
    ← iteratedFDerivWithin_of_isOpen (s := O) j hO hq,
    L.iteratedFDerivWithin_comp_right ha hO.uniqueDiffOn hPre.uniqueDiffOn hq (by simp)]
  exact ((iteratedFDerivWithin ℝ j a O (L q)).norm_compContinuousLinearMap_le
    (fun _ => L)).trans (mul_le_of_le_one_right (norm_nonneg _)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)))

theorem norm_iteratedFDeriv_radialFirstDerivative_at_zero_le
    {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} (ha : ContDiffOn ℝ ∞ a O) {p : P} (hp : (p,0) ∈ O) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun b => radialFirstDerivative a (b,0)) p‖ ≤
      ‖iteratedFDeriv ℝ (j+1) a (p,0)‖ := by
  let L := ContinuousLinearMap.inl ℝ P ℝ
  exact (norm_iteratedFDeriv_comp_contraction L
    (ContinuousLinearMap.norm_inl_le_one ℝ P ℝ) hO (contDiffOn_radialFirstDerivative hO ha) hp j).trans
      (norm_iteratedFDeriv_radialFirstDerivative_le (ha.contDiffAt (hO.mem_nhds hp)) j)

private def radiusTaylorInput (z : ℝ × (P × ℝ)) : P × ℝ :=
  (z.2.1,z.1*z.2.2)

private theorem contDiff_radiusTaylorInput : ContDiff ℝ ∞ (radiusTaylorInput (P := P)) :=
  contDiff_snd.fst.prodMk (contDiff_fst.mul contDiff_snd.snd)

private def radiusTaylorIntegrand (a : P × ℝ → V) (z : ℝ × (P × ℝ)) : V :=
  (1-z.1) • radiusSecondDerivative a (radiusTaylorInput z)

private theorem contDiffOn_radiusTaylorIntegrand {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} (ha : ContDiffOn ℝ ∞ a O) :
    ContDiffOn ℝ ∞ (radiusTaylorIntegrand a) (radiusTaylorInput ⁻¹' O) :=
  ((contDiff_const.sub contDiff_fst).contDiffOn).smul
    ((contDiffOn_radiusSecondDerivative hO ha).comp contDiff_radiusTaylorInput.contDiffOn
      (mapsTo_preimage _ _))

variable [ProperSpace P]

/-- The literal Taylor remainder is smooth on the open domain formed by the segments in the
original signed-radius domain, including their endpoints. -/
theorem radiusTaylorRemainder_contDiffOn {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} (ha : ContDiffOn ℝ ∞ a O) :
    IsOpen (radiusSegment O) ∧ ContDiffOn ℝ ∞ (radiusTaylorRemainder a) (radiusSegment O) := by
  have hSet : radiusSegment O = {q | Icc (0:ℝ) 1 ×ˢ {q} ⊆ radiusTaylorInput ⁻¹' O} := by
    ext q
    constructor
    · rintro h ⟨t,p⟩ ⟨ht,hp⟩
      have hp' : p = q := hp
      subst p
      exact h t ht
    · intro h t ht
      exact h (show (t,q) ∈ Icc (0:ℝ) 1 ×ˢ {q} from ⟨ht,rfl⟩)
  rw [hSet]
  exact contDiffOn_intervalIntegral_unit_of_tube (hO.preimage
    contDiff_radiusTaylorInput.continuous) (contDiffOn_radiusTaylorIntegrand hO ha)

/-- The Taylor remainder retains a common bound for the joint jets on
the segment, using two further derivatives of the original function. -/
theorem radiusTaylorRemainder_jet_le {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} (ha : ContDiffOn ℝ ∞ a O) {q : P × ℝ} (hq : q ∈ radiusSegment O)
    (j : ℕ) (C : ℝ)
    (hBound : ∀ t ∈ Icc (0:ℝ) 1, ∀ k ≤ j,
      ‖iteratedFDeriv ℝ (k+2) a (q.1,t*q.2)‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (radiusTaylorRemainder a) q‖ ≤ C := by
  have hTube : Icc (0:ℝ) 1 ×ˢ {q} ⊆ radiusTaylorInput ⁻¹' O := by
    rintro ⟨t,p⟩ ⟨ht,hp⟩
    have hp' : p = q := hp
    subst p
    exact hq t ht
  apply (localSmoothJetBudget_intervalIntegral_unit
    (hO.preimage contDiff_radiusTaylorInput.continuous)
    (contDiffOn_radiusTaylorIntegrand hO ha) hTube j C ?_).bound j le_rfl
  intro t ht k hk
  let L : (P × ℝ) →L[ℝ] (P × ℝ) := radiusDilation t
  have hPoint : L q ∈ O := hq t ht
  have hC : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have hD : ‖(1-t) • (ContinuousLinearMap.id ℝ V)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    exact (mul_le_of_le_one_right hC ContinuousLinearMap.norm_id_le).trans (sub_le_self 1 ht.1)
  have hSmooth := (contDiffOn_radiusSecondDerivative hO ha).contDiffAt (hO.mem_nhds hPoint)
  have hL := radiusDilation_norm_le (P := P) t (by rw [abs_of_nonneg ht.1]; exact ht.2)
  let A : V →L[ℝ] V := (1-t) • ContinuousLinearMap.id ℝ V
  change ‖iteratedFDeriv ℝ k (A ∘ (radiusSecondDerivative a ∘ L)) q‖ ≤ C
  calc
    _ ≤ ‖A‖ * ‖iteratedFDeriv ℝ k (radiusSecondDerivative a ∘ L) q‖ :=
      A.norm_iteratedFDeriv_comp_left (hSmooth.comp q L.contDiff.contDiffAt) (by simp)
    _ ≤ ‖iteratedFDeriv ℝ k (radiusSecondDerivative a ∘ L) q‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hD
    _ ≤ ‖iteratedFDeriv ℝ k (radiusSecondDerivative a) (L q)‖ :=
      norm_iteratedFDeriv_comp_contraction L hL hO
        (contDiffOn_radiusSecondDerivative hO ha) hPoint k
    _ ≤ ‖iteratedFDeriv ℝ (k+2) a (L q)‖ :=
      norm_iteratedFDeriv_radiusSecondDerivative_le
        (ha.contDiffAt (hO.mem_nhds hPoint)) k
    _ ≤ C := hBound t ht k hk

end CalderonPaper
