module

public import Proof.CalderonN.UniformRadialLift

import Proof.CalderonN.MovingBallFamilies
import Mathlib.Tactic

/-! Adapted from `ScaledSphereDatumExtension` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

@[expose] def ScaledSphereDatumJets (n : ℕ) (f : P × (X dim) → ℝ) (p : P) (r M : ℝ) : Prop :=
  ∀ w ∈ (standardSphere dim), ∃ u : P × (X dim) → ℝ, ContDiff ℝ ∞ u ∧
    u =ᶠ[𝓝 (0,w)] (fun q => f (p+r • q.1,q.2)) ∧
    ∀ k ≤ n, ‖iteratedFDeriv ℝ k u (0,w)‖ ≤ M

@[expose] def WeightedSliceDatumJets (s : ℕ) (d : P × (X dim) → ℝ) (p : P) (r M : ℝ) (S : Set (X dim)) : Prop :=
  ∀ k ≤ s, ∀ z ∈ S,
    ‖iteratedFDeriv ℝ k (fun x => d (p,x)) z‖ ≤ M ∧
    ∀ v : P, ‖fderiv ℝ (fun q => iteratedFDeriv ℝ k (fun x => d (q,x)) z) p (r • v)‖ ≤ M*‖v‖

private theorem weightedSliceDatumJets_of_scaled (s : ℕ)
    {u : P × (X dim) → ℝ} (hu : ContDiff ℝ ∞ u) (p : P) {r : ℝ} (hr : r ≠ 0) (M : ℝ) {S : Set (X dim)}
    (h : ∀ z ∈ S, ∀ k ≤ s+1, ‖iteratedFDeriv ℝ k u (0,z)‖ ≤ M) :
    WeightedSliceDatumJets s (fun q => u (r⁻¹ • (q.1-p),q.2)) p r M S := by
  intro k hk z hz
  constructor
  · have he : (fun x => u (r⁻¹ • (p-p),x)) = fun x => u (0,x) := by simp
    rw [he]
    exact (norm_iteratedFDeriv_slice_right_le hu 0 z k).trans (h z hz k (by omega))
  · intro v
    let j (q : P) := iteratedFDeriv ℝ k (fun x => u (q,x)) z
    have hj : ContDiff ℝ ∞ j := (contDiff_iteratedFDeriv_slice_right hu k).comp
      (contDiff_id.prodMk contDiff_const)
    change ‖fderiv ℝ (fun q => j (r⁻¹ • (q-p))) p (r • v)‖ ≤ _
    rw [fderiv_scaled_parameter_eq (hj.differentiable (by simp) 0) hr]
    exact (norm_fderiv_iteratedFDeriv_slice_right_le hu 0 z k v).trans
      (mul_le_mul_of_nonneg_right (h z hz _ (by omega)) (norm_nonneg v))

/-- One smooth field agrees with the actual raw datum near the whole
sphere. Its radially lifted version has bounded spatial jets globally
and supplies the same Dirichlet data near the chosen parameter. -/
theorem exists_scaledSphereDatum_extensions (s : ℕ) :
    ∃ L : Set (X dim), IsCompact L ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : P × (X dim) → ℝ) (p : P) (r M : ℝ), r ≠ 0 → 0 ≤ M →
      ScaledSphereDatumJets (s+1) f p r M →
      ∃ d₀ d₁ : P × (X dim) → ℝ, ContDiff ℝ ∞ d₀ ∧ ContDiff ℝ ∞ d₁ ∧
        (∀ a z, z ∉ L → d₁ (a,z) = 0) ∧
        (∃ U : Set (P × (X dim)), IsOpen U ∧ {p} ×ˢ (standardSphere dim) ⊆ U ∧ EqOn d₀ f U) ∧
        EqOn d₁ d₀ (univ ×ˢ (standardSphere dim)) ∧
        WeightedSliceDatumJets s d₀ p r M (standardSphere dim) ∧
        WeightedSliceDatumJets s d₁ p r (C*M) univ := by
  obtain ⟨L,hL,C,hC,hLift⟩ := exists_uniform_radial_lift_jet_bounds (dim := dim) (P := P) (s+1)
  refine ⟨L,hL,C,hC,?_⟩
  intro f p r M hr hM hJets
  let a (q : P × (X dim)) := (p+r • q.1,q.2)
  let b (q : P × (X dim)) := (r⁻¹ • (q.1-p),q.2)
  have hb : ContDiff ℝ ∞ b :=
    ((contDiff_fst.sub contDiff_const).const_smul r⁻¹).prodMk contDiff_snd
  have hab (q : P × (X dim)) : a (b q) = q := by
    simp only [a,b,smul_inv_smul₀ hr,add_sub_cancel]
  let f' := f ∘ a
  let S := ({(0:P)} : Set P) ×ˢ (standardSphere dim)
  have hSmooth : smoothNear f' S := by
    apply smoothNear_of_open_cover
    intro q hq
    have he : q = (0,q.2) := Prod.ext (mem_singleton_iff.mp hq.1) rfl
    obtain ⟨u,hu,hue,_⟩ := hJets q.2 hq.2
    have hEq : u =ᶠ[𝓝 q] f' := he ▸ hue
    obtain ⟨U,hU,hEqU⟩ := eventuallyEq_iff_exists_mem.mp hEq
    obtain ⟨V,hVU,hV,hqV⟩ := _root_.mem_nhds_iff.mp hU
    exact ⟨V,hV,hqV,hu.contDiffOn.congr (fun t ht => (hEqU (hVU ht)).symm)⟩
  obtain ⟨U,hU,hSU,hu⟩ := hSmooth
  obtain ⟨u,hu',_,W,hW,hSW,_,hE⟩ := exists_contDiff_extension_near_compact hU
    (isCompact_singleton.prod (isCompact_sphere (0 : (X dim)) 1) : IsCompact S) hSU hu
  have hUjet (w : (X dim)) (hw : w ∈ (standardSphere dim)) (k : ℕ) (hk : k ≤ s+1) :
      ‖iteratedFDeriv ℝ k u (0,w)‖ ≤ M := by
    obtain ⟨u',_,huEq,huJ⟩ := hJets w hw
    have he : u =ᶠ[𝓝 (0,w)] f' := by
      filter_upwards [hW.mem_nhds (hSW ⟨mem_singleton _,hw⟩)] with q hq
      exact hE hq
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ (he.trans huEq.symm) k).eq_of_nhds]
    exact huJ k hk
  obtain ⟨v,hv,hSupp,hV,hB⟩ := hLift u hu'
  let d₀ := u ∘ b
  let d₁ := v ∘ b
  refine ⟨d₀,d₁,hu'.comp hb,hv.comp hb,fun a z hz => hSupp _ z hz,?_,
    fun q hq => hV ⟨mem_univ _,hq.2⟩,?_,?_⟩
  · refine ⟨b ⁻¹' W,hW.preimage hb.continuous,?_,?_⟩
    · rintro ⟨a,z⟩ ⟨ha,hz⟩
      change a = p at ha
      subst a
      apply hSW
      simpa only [b,mem_prod,sub_self,smul_zero,mem_singleton_iff,true_and] using hz
    · intro q hq
      change u (b q) = f q
      exact (hE hq).trans (congrArg f (hab q))
  · exact weightedSliceDatumJets_of_scaled s hu' p hr M hUjet
  · exact weightedSliceDatumJets_of_scaled s hv p hr (C*M) (fun z _ k hk => hB M hM hUjet z k hk)

end CalderonN
