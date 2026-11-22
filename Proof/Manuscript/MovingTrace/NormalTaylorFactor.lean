module

public import Proof.CalderonN.LocalJetIntegral
public import Proof.CalderonPatch.BoundaryLayerTaylor
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN CalderonPatch.BoundaryLayer Set MeasureTheory
open scoped ContDiff

namespace CalderonPaper

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Smooth coefficients have a smooth quotient after subtracting their
Taylor polynomial in signed normal depth. This retains derivatives in all
auxiliary geometry and direction parameters and is valid at depth zero. -/
theorem normalTaylor_has_smooth_remainder {O : Set (E × ℝ)} (hO : IsOpen O)
    {a : E × ℝ → F} (ha : ContDiffOn ℝ ∞ a O) (M : ℕ) :
    let U := {q : E × ℝ | ∀ s ∈ Icc (0 : ℝ) 1, (q.1, s * q.2) ∈ O}
    IsOpen U ∧ ∃ R : E × ℝ → F, ContDiffOn ℝ ∞ R U ∧
      ∀ q ∈ U, a q =
        (∑ j ∈ Finset.range (M + 1),
          (q.2 ^ j / (j.factorial : ℝ)) • iteratedDeriv j (fun t : ℝ => a (q.1,t)) 0) +
            q.2 ^ (M + 1) • R q := by
  let U : Set (E × ℝ) := {q | ∀ s ∈ Icc (0 : ℝ) 1, (q.1,s*q.2) ∈ O}
  let B : ℝ × (E × ℝ) → E × ℝ := fun q => (q.2.1,q.1*q.2.2)
  let f : ℝ × (E × ℝ) → F := fun q =>
    (1 - q.1) ^ M • iteratedFDeriv ℝ (M + 1) a (B q) (fun _ => ((0 : E), (1 : ℝ)))
  have hB : ContDiff ℝ ∞ B := contDiff_snd.fst.prodMk (contDiff_fst.mul contDiff_snd.snd)
  have hf : ContDiffOn ℝ ∞ f (B ⁻¹' O) :=
    ((contDiff_const.sub contDiff_fst).pow M).contDiffOn.smul
      ((contDiffOn_iteratedFDeriv_repeat hO ha _ _).comp hB.contDiffOn (mapsTo_preimage _ _))
  obtain ⟨hU,hIntegral⟩ := contDiffOn_intervalIntegral_unit_of_tube
    (hO.preimage hB.continuous) hf
  have hEqU : U = {p | Icc (0:ℝ) 1 ×ˢ {p} ⊆ B ⁻¹' O} := by
    ext p
    change (∀ s ∈ Icc (0:ℝ) 1, (p.1,s*p.2) ∈ O) ↔
      Icc (0:ℝ) 1 ×ˢ {p} ⊆ B ⁻¹' O
    constructor
    · rintro h ⟨s,q⟩ ⟨hs,rfl⟩
      exact h s hs
    · intro h s hs
      exact h (show (s,p) ∈ Icc (0:ℝ) 1 ×ˢ {p} from ⟨hs,mem_singleton p⟩)
  rw [← hEqU] at hU hIntegral
  change IsOpen U ∧ _
  refine ⟨hU, fun q => ((M.factorial : ℝ)⁻¹) • ∫ s in (0:ℝ)..1, f (s,q),
    hIntegral.const_smul _, ?_⟩
  intro q hq
  have hx : (q.1, (0 : ℝ)) ∈ O := by simpa using hq 0 (by norm_num)
  have hLine (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      (q.1,0) + s • ((0:E),q.2) = B (s,q) := by simp [B]
  have h := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := a) (x := (q.1,0)) (y := ((0:E),q.2)) (n := M)
    (fun s hs => by
      rw [hLine s hs]
      exact (ha.contDiffAt (hO.mem_nhds (hq s hs))).of_le (by simp))
  have hFace (j : ℕ) :
      iteratedFDeriv ℝ j a (q.1, 0) (fun _ => ((0:E),q.2)) =
        q.2 ^ j • iteratedDeriv j (fun t : ℝ => a (q.1,t)) 0 := by
    rw [iteratedDeriv_slice_eq_iteratedFDeriv hO ha hx]
    simp only [show ((0:E),q.2) = q.2 • ((0:E),(1:ℝ)) by simp,
      ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_fin]
  have hSum :
      (∑ j ∈ Finset.range (M + 1), ((j.factorial : ℝ)⁻¹) •
          iteratedFDeriv ℝ j a (q.1,0) (fun _ => ((0:E),q.2))) =
        ∑ j ∈ Finset.range (M + 1), (q.2 ^ j / (j.factorial : ℝ)) •
          iteratedDeriv j (fun t : ℝ => a (q.1,t)) 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hFace, smul_smul, mul_comm, div_eq_mul_inv]
  have hRes :
      (∫ s in (0:ℝ)..1, (1-s)^M •
        iteratedFDeriv ℝ (M+1) a ((q.1,0) + s • ((0:E),q.2)) (fun _ => ((0:E),q.2))) =
        q.2 ^ (M + 1) • ∫ s in (0:ℝ)..1, f (s,q) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [uIcc_of_le zero_le_one] at hs
    rw [hLine s hs]
    simp only [f, show ((0:E),q.2) = q.2 • ((0:E),(1:ℝ)) by simp,
      ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_fin, smul_smul]
    rw [mul_comm]
  simp only [Prod.mk_add_mk, add_zero, zero_add] at h
  rw [hSum, hRes, smul_comm ((M.factorial : ℝ)⁻¹) (q.2 ^ (M + 1))] at h
  exact h

end CalderonPaper
