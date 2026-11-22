module

public import Proof.CalderonN.Chart

import Proof.CalderonN.EllipticCalculus
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The closed annulus with these two radii, including its two boundary spheres. -/
@[expose] def closedAnnulus (c : (X dim)) (r s : ℝ) : Set (X dim) :=
  closedBall c s \ ball c r

theorem mem_closedAnnulus {c x : (X dim)} {r s : ℝ} :
    x ∈ closedAnnulus c r s ↔ r ≤ ‖x-c‖ ∧ ‖x-c‖ ≤ s := by
  simp only [closedAnnulus,Set.mem_sdiff,mem_closedBall,mem_ball,not_lt,dist_eq_norm]
  exact and_comm

theorem isCompact_closedAnnulus (c : (X dim)) (r s : ℝ) : IsCompact (closedAnnulus c r s) :=
  (isCompact_closedBall _ _).diff isOpen_ball

/-- The open annulus about a chart point. -/
@[expose] def openAnnulus (c : (X dim)) (r s : ℝ) : Set (X dim) :=
  {x | r < ‖x-c‖ ∧ ‖x-c‖ < s}

theorem isOpen_openAnnulus (c : (X dim)) (r s : ℝ) : IsOpen (openAnnulus c r s) :=
  (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)

/-- The annulus in dimension at least two is connected. The proof via the sphere
and an interval is adapted from `MixedKernelAnnulusGeometry.lean` at
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/
theorem isConnected_openAnnulus (p : (X dim)) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    IsConnected (openAnnulus p r R) := by
  have hdim : 1 < Module.rank ℝ (X dim) := by
    rw [← Module.finrank_eq_rank]
    have hn : 1 < dim := by simpa only [Fintype.card_fin] using Fintype.one_lt_card (α := Fin dim)
    exact_mod_cast (by simpa only [finrank_euclideanSpace, Fintype.card_fin] using hn :
      1 < Module.finrank ℝ (X dim))
  have hS : IsConnected (sphere (0 : (X dim)) 1) := isConnected_sphere hdim _ (by norm_num)
  have hI : IsConnected (Ioo r R) := isConnected_Ioo hrR
  let f : (X dim) × ℝ → (X dim) := fun z => p+z.2 • z.1
  have hcont : Continuous f := continuous_const.add (continuous_snd.smul continuous_fst)
  have himage : f '' (sphere (0 : (X dim)) 1 ×ˢ Ioo r R) =
      {y : (X dim) | r < ‖y-p‖ ∧ ‖y-p‖ < R} := by
    ext y
    constructor
    · rintro ⟨⟨v,t⟩,⟨hv,ht⟩,rfl⟩
      have hvn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
      have ht0 : 0 < t := hr.trans ht.1
      simpa only [mem_ofPred_eq,mem_Ioo,f,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos ht0,hvn,mul_one] using ht
    · intro hy
      have hn : 0 < ‖y-p‖ := hr.trans hy.1
      refine ⟨(‖y-p‖⁻¹ • (y-p),‖y-p‖),⟨?_,hy⟩,?_⟩
      · rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
      · dsimp [f]
        rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul,add_sub_cancel]
  rw [openAnnulus,← himage]
  exact (hS.prod hI).image f hcont.continuousOn

open Elliptic in
/-- A two-sided cutoff on the separated annulus. Only its two transition
collars can contribute to the residual of a harmonic function. -/
theorem exists_radialCollarCutoff (c : (X dim)) {a b u v : ℝ}
    (hab : a < b) (huv : u < v) :
    ∃ χ : (X dim) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ closedAnnulus c a v ∧
      (∀ x ∈ closedAnnulus c b u, χ x = 1) ∧
      ∀ x ∉ closedAnnulus c u v ∪ closedAnnulus c a b,
        (χ =ᶠ[𝓝 x] fun _ => (0 : ℝ)) ∨ χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  obtain ⟨η,hη,_,hηb,hηa⟩ := exists_plateau_cutoff (isOpen_ball : IsOpen (ball c b))
    (isCompact_closedBall c a) (closedBall_subset_ball hab)
  obtain ⟨ζ,hζ,hζc,hζv,hζu⟩ := exists_plateau_cutoff (isOpen_ball : IsOpen (ball c v))
    (isCompact_closedBall c u) (closedBall_subset_ball huv)
  let χ (x : (X dim)) := ζ x * (1-η x)
  have hχc : HasCompactSupport χ := hζc.mul_right
  have hZeroIn (x : (X dim)) (hx : x ∈ closedBall c a) :
      χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hηa x hx] with y hy
    simp [χ,hy]
  have hZeroOut (x : (X dim)) (hx : x ∉ ball c v) :
      χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    have hz : x ∉ tsupport ζ := fun h => hx (hζv h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
    change ζ y = 0 at hy
    simp [χ,hy]
  have hOne (x : (X dim)) (hb : x ∉ ball c b) (hu : x ∈ closedBall c u) :
      χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    have he : x ∉ tsupport η := fun h => hb (hηb h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp he,hζu x hu] with y hy hz
    change η y = 0 at hy
    simp [χ,hy,hz]
  refine ⟨χ,hζ.mul (contDiff_const.sub hη),hχc,?_,fun x hx => (hOne x hx.2 hx.1).eq_of_nhds,?_⟩
  · intro x hx
    refine ⟨ball_subset_closedBall (hζv (tsupport_mul_subset_left hx)),?_⟩
    intro ha
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hZeroIn x (ball_subset_closedBall ha))) hx
  · intro x hx
    by_cases ha : x ∈ closedBall c a
    · exact Or.inl (hZeroIn x ha)
    by_cases hv : x ∈ ball c v
    · have hb : x ∉ ball c b := fun hb =>
        hx (Or.inr ⟨ball_subset_closedBall hb,fun h => ha (ball_subset_closedBall h)⟩)
      have hu : x ∈ ball c u := by
        by_contra hn
        exact hx (Or.inl ⟨ball_subset_closedBall hv,hn⟩)
      exact Or.inr (hOne x hb (ball_subset_closedBall hu))
    · exact Or.inl (hZeroOut x hv)

end CalderonN.FixedTube
