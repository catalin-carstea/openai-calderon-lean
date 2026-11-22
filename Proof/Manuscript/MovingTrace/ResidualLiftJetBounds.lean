module

public import Proof.Manuscript.MovingTrace.ResidualExteriorCutIn
public import Proof.CalderonN.LocalJetEnvelopeBounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2900000

open CalderonN Set Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {P A Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Lift the signed residual to the ambient ball. The fixed spatial
support bounds all changes of variables. Below the last scaled exterior
depth the lifted forcing is identically zero in a neighborhood. -/
theorem exists_uniform_jet_bound_lifted_residual
    (e : OpenPartialHomeomorph (A × ℝ) Z)
    (he : ContDiffOn ℝ ∞ e.symm e.target)
    {J : Set P} (hJ : IsCompact J) {K : Set (A × ℝ)} (hK : IsCompact K)
    (hKe : K ⊆ e.source)
    (f : ℝ → (P × A) × ℝ → ℂ)
    {h₀ : ℝ} (hh₀ : h₀ ≤ 1)
    (hSupp : ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ p x, x ∉ K →
      residualCutIn (x.2/h) * f h ((p,x.1),x.2) = 0)
    (N : ℕ) (a : ℝ → ℝ) (ha : ∀ h : ℝ, 0 < h → h ≤ 1 → 0 ≤ a h)
    (hf : SmoothCollarContribution
      {q : (P × A) × ℝ | q.1.1 ∈ J ∧ (q.1.2,q.2) ∈ K} f N a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ), 0 < h → h ≤ h₀ → ∀ p ∈ J, ∀ z : Z, ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j
        (collarLift e (fun (q : P × (A × ℝ)) =>
          residualCutIn (q.2.2/h) * f h ((q.1,q.2.1),q.2.2))) (p,z)‖ ≤
        C * (h⁻¹^N * a h) := by
  let Γ : Set ((P × A) × ℝ) := {q | q.1.1 ∈ J ∧ (q.1.2,q.2) ∈ K}
  let T : Set (P × Z) := univ ×ˢ e.target
  have hT : IsOpen T := isOpen_univ.prod e.open_target
  let read (q : P × Z) : (P × A) × ℝ := ((q.1,(e.symm q.2).1),(e.symm q.2).2)
  have hRead : ContDiffOn ℝ ∞ read T := by
    have hm : MapsTo (Prod.snd : P × Z → Z) T e.target := fun q hq => hq.2
    have h := he.comp contDiffOn_snd hm
    exact (contDiffOn_fst.prodMk h.fst).prodMk h.snd
  let H := J ×ˢ (e '' K)
  have hH : IsCompact H := hJ.prod (hK.image_of_continuousOn (e.continuousOn.mono hKe))
  have hHT : H ⊆ T := by
    rintro ⟨p,z⟩ ⟨hp,⟨x,hx,rfl⟩⟩
    exact ⟨mem_univ _,e.map_source (hKe hx)⟩
  have hD (j : Fin (N+1)) : ContinuousOn (fun q => ‖iteratedFDeriv ℝ j.val read q‖) T :=
    fun q hq => ((hRead.contDiffAt (hT.mem_nhds hq)).continuousAt_iteratedFDeriv
      (by simp)).norm.continuousWithinAt
  have hB (j : Fin (N+1)) : ∃ C ≥ 0, ∀ q ∈ H, ‖iteratedFDeriv ℝ j.val read q‖ ≤ C := by
    obtain ⟨r,hr⟩ := hH.bddAbove_image ((hD j).mono hHT)
    exact ⟨max 0 r,le_max_left _ _,fun q hq => (hr ⟨q,hq,rfl⟩).trans (le_max_right _ _)⟩
  choose B hB hBound using hB
  let D := 1 + ∑ j : Fin (N+1), B j
  have hD₁ : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hB i)
  let v (h : ℝ) (q : (P × A) × ℝ) := residualCutIn (q.2/h) * f h q
  have hv : SmoothCollarContribution Γ v N (fun h => h⁻¹^N * a h) :=
    (SmoothCollarContribution.exteriorCutIn N).mul (fun h hh _ => by positivity) ha hf
  obtain ⟨C,hC,hV⟩ := hv.2
  let W (h : ℝ) := collarLift e (fun q : P × (A × ℝ) => v h ((q.1,q.2.1),q.2.2))
  have hCW (h : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1) : 0 ≤ C * (h⁻¹^N * a h) :=
    mul_nonneg hC (mul_nonneg (by positivity) (ha h hh hh₁))
  refine ⟨(N.factorial : ℝ) * C * D^N, by positivity, ?_⟩
  intro h hh hhh p hp z j hj
  have hh₁ := hhh.trans hh₀
  change ‖iteratedFDeriv ℝ j (W h) (p,z)‖ ≤ _
  have hP : 0 ≤ (N.factorial : ℝ) * C * D^N * (h⁻¹^N * a h) := by
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (ha h hh hh₁))
  have hZero (hZ : (W h) =ᶠ[𝓝 (p,z)] (fun _ => (0 : ℂ))) :
      ‖iteratedFDeriv ℝ j (W h) (p,z)‖ ≤ (N.factorial : ℝ) * C * D^N * (h⁻¹^N * a h) := by
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hZ j).eq_of_nhds]
    simp only [show (fun _ : P × Z => (0:ℂ)) = 0 from rfl,iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
    exact hP
  by_cases hz : z ∈ e '' K
  · have hq : (p,z) ∈ H := ⟨hp,hz⟩
    have ht := hHT hq
    have hReadΓ : read (p,z) ∈ Γ := by
      obtain ⟨x,hx,hxz⟩ := hz
      have heq : e.symm z = x := hxz ▸ e.left_inv (hKe hx)
      exact ⟨hp,by simpa only [read,heq,Prod.eta] using hx⟩
    have hr := hRead.contDiffAt (hT.mem_nhds ht)
    have hComp : W h =ᶠ[𝓝 (p,z)] (v h ∘ read) := by
      filter_upwards [hT.mem_nhds ht] with q hq
      exact ite_eq_left hq.2
    by_cases hd : -1 ≤ (read (p,z)).2/h
    · have hhD (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ j) :
          ‖iteratedFDeriv ℝ i read (p,z)‖ ≤ D^i := by
        let k : Fin (N+1) := ⟨i,Nat.lt_succ_of_le (hiN.trans hj)⟩
        have hC' := (hBound k (p,z) hq).trans
          ((Finset.single_le_sum (fun l _ => hB l) (Finset.mem_univ k)).trans (le_add_of_nonneg_left zero_le_one))
        exact hC'.trans (by simpa only [pow_one] using pow_le_pow_right₀ hD₁ hi)
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hComp j).eq_of_nhds]
      refine (norm_iteratedFDeriv_comp_at_le read (v h) (p,z) j hr
        (hv.1 _ hReadΓ h hh hh₁) (C * (h⁻¹^N * a h)) D
        (fun i hi => hV _ hReadΓ h hh hh₁ hd i (hi.trans hj)) hhD).trans ?_
      have hfact : (j.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hj
      calc
        _ ≤ (N.factorial : ℝ) * (C * (h⁻¹^N * a h)) * D^N :=
          mul_le_mul (mul_le_mul_of_nonneg_right hfact (hCW h hh hh₁))
            (pow_le_pow_right₀ hD₁ hj) (by positivity)
            (mul_nonneg (by positivity) (hCW h hh hh₁))
        _ = _ := by ring
    · apply hZero
      refine hComp.trans ?_
      have hOpen : IsOpen {q : (P × A) × ℝ | q.2/h < -1} :=
        isOpen_lt (continuous_snd.div_const h) continuous_const
      filter_upwards [(hr.continuousAt.preimage_mem_nhds
        (hOpen.mem_nhds (lt_of_not_ge hd)))] with q hq
      change (read q).2 / h < -1 at hq
      simp [v, residualCutIn_zero hq.le]
  · apply hZero
    have hClosed : IsClosed (e '' K) := (hK.image_of_continuousOn (e.continuousOn.mono hKe)).isClosed
    have hOut : IsOpen {q : P × Z | q.2 ∉ e '' K} := hClosed.isOpen_compl.preimage continuous_snd
    filter_upwards [hOut.mem_nhds (show (p,z) ∈ {q : P × Z | q.2 ∉ e '' K} from hz)] with q hq
    apply collarLift_zero_off_image e _ (K := K) _ q hq
    intro p x hx
    exact hSupp h hh hhh p x hx

end CalderonPaper
