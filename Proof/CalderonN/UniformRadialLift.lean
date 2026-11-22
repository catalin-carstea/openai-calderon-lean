module

public import Proof.CalderonN.ParametricBallConormal
public import Proof.CalderonN.MixedSliceJets

import Proof.CalderonN.MovingBallFamilies
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic

/-! Adapted from `UniformRadialLift` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2200000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Radial lifting and a fixed angular cutoff carry joint jet bounds
on the sphere to global bounds on a compactly supported datum. -/
theorem exists_uniform_radial_lift_jet_bounds (n : ℕ) :
    ∃ L : Set (X dim), IsCompact L ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : P × (X dim) → ℝ, ContDiff ℝ ∞ f →
      ∃ b : P × (X dim) → ℝ, ContDiff ℝ ∞ b ∧
        (∀ p z, z ∉ L → b (p,z) = 0) ∧ EqOn b f (univ ×ˢ (standardSphere dim)) ∧
        ∀ M, 0 ≤ M →
          (∀ w ∈ (standardSphere dim), ∀ k ≤ n, ‖iteratedFDeriv ℝ k f (0,w)‖ ≤ M) →
          ∀ z k, k ≤ n → ‖iteratedFDeriv ℝ k b (0,z)‖ ≤ C*M := by
  let U : Set (X dim) := ({0}ᶜ : Set (X dim))
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hS : IsCompact (standardSphere dim) := isCompact_sphere (0:(X dim)) 1
  have hSU : (standardSphere dim) ⊆ U := by
    intro z hz
    change z ≠ 0
    intro he
    have := mem_sphere_zero_iff_norm.mp hz
    simp [he] at this
  obtain ⟨W,hW,hSW,hWU,hL⟩ := exists_open_between_and_isCompact_closure hS hU hSU
  obtain ⟨V,hV,hSV,hVW,_⟩ := exists_open_between_and_isCompact_closure hS hW hSW
  obtain ⟨χ,hχ,_,hχsupp,hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_closure hVW
  obtain ⟨N,hN,_,T,hT,hLT,_,hEqN⟩ :=
    exists_contDiff_extension_near_compact hU hL hWU contDiffOn_sphereNormalize
  let D (q : P × (X dim)) := (q.1,N q.2)
  let α (q : P × (X dim)) := χ q.2
  have hD : ContDiff ℝ ∞ D := contDiff_fst.prodMk (hN.comp contDiff_snd)
  have hα : ContDiff ℝ ∞ α := hχ.comp contDiff_snd
  let J := ({(0:P)} : Set P) ×ˢ closure W
  have hJ : IsCompact J := isCompact_singleton.prod hL
  obtain ⟨A,hA,hBoundα⟩ := exists_uniform_finite_jet_bound hJ hα n
  obtain ⟨D₀,hD₀,hBoundD⟩ := exists_uniform_finite_jet_bound hJ hD n
  let C := (2:ℝ)^n*(A*(n.factorial*D₀^n))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨closure W,hL,C,hC,?_⟩
  intro f hf
  let b (q : P × (X dim)) := α q * f (D q)
  refine ⟨b,hα.mul (hf.comp hD),?_,?_,?_⟩
  · intro p z hz
    have hz' : χ z = 0 := by
      by_contra h
      exact hz (subset_closure (hχsupp ▸ (show z ∈ Function.support χ from h)))
    simp [b,α,hz']
  · intro q hq
    have hw := hq.2
    have hN' : N q.2 = q.2 := (hEqN (hLT (subset_closure (hSW hw)))).trans
      (sphereNormalize_eq_of_sphere hw)
    have h₁ := (hχone q.2).mp (subset_closure (hSV hw))
    simp [b,α,D,h₁,hN']
  · intro M hM hfJ z k hk
    by_cases hz : z ∈ closure W
    · have hND : N z ∈ (standardSphere dim) := by
        rw [hEqN (hLT hz)]
        exact sphereNormalize_mem_sphere (hWU hz)
      have hFD (i : ℕ) (hi : i ≤ n) :
          ‖iteratedFDeriv ℝ i (f ∘ D) (0,z)‖ ≤ n.factorial*M*D₀^n :=
        norm_iteratedFDeriv_comp_le_of_finite_bounds hf hD (0,z) hi hM hD₀
          (hfJ (N z) hND) (hBoundD (0,z) ⟨mem_singleton _,hz⟩)
      refine (norm_iteratedFDeriv_mul_le_of_finite_bounds hα (hf.comp hD) (0,z) hk
        (zero_le_one.trans hA) (by positivity) (hBoundα (0,z) ⟨mem_singleton _,hz⟩) hFD).trans_eq ?_
      dsimp only [C]
      ring
    · have hZ : b =ᶠ[𝓝 ((0:P),z)] (fun _ => 0) := by
        filter_upwards [(continuous_snd.continuousAt : ContinuousAt (Prod.snd : P × (X dim) → (X dim)) ((0:P),z)).preimage_mem_nhds
          (isClosed_closure.isOpen_compl.mem_nhds hz)] with q hq
        have hq' : χ q.2 = 0 := by
          by_contra h
          exact hq (subset_closure (hχsupp ▸ (show q.2 ∈ Function.support χ from h)))
        simp [b,α,hq']
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hZ k).eq_of_nhds]
      simpa using mul_nonneg hC hM

end CalderonN
