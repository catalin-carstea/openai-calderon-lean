module

public import Proof.CalderonN.ParametricMetricBallDirichlet
public import Proof.CalderonN.ClosedBallSmoothExtension

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.FixedBallMetricEllipticity
import Mathlib.Tactic

/-! A cutoff in the center parameter lets the existing closed-ball
extension preserve the full joint germ of the physical solution. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_joint_smooth_ballResponse
    {V : Set ℝ} (hV : IsOpen V) (h₀ : (0 : ℝ) ∈ V)
    (a : ℝ × X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ t z, z ∉ K → a (t,z) = 0)
    (u : ℝ × X dim → ℝ) (hu : ContDiff ℝ ∞ u)
    (lo hi : ℝ → ℝ)
    (hEll : ∀ t ∈ V, UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (fun z => a (t,z)) (lo t) (hi t)) :
    ∃ W : Set ℝ, IsOpen W ∧ (0 : ℝ) ∈ W ∧ W ⊆ V ∧
      ∃ b : ℝ × X dim → ℝ, ContDiff ℝ ∞ b ∧ ∀ t ∈ W,
        EqOn (fun z => b (t,z)) (fun z => u (t,z)) (standardSphere dim) ∧
        EqOn (negativeBallDivergence (fun z => a (t,z)) (fun z => b (t,z))) 0
          (ball (0 : X dim) 1) := by
  obtain ⟨f,hfs,hF,hFj,_⟩ := exists_parametric_classical_ballDirichlet hV a ha K hK hSupp u hu lo hi hEll
  obtain ⟨δ,hδ,hδV⟩ := Metric.isOpen_iff.mp hV 0 h₀
  let χ : ContDiffBump (0 : ℝ) :=
    { rIn := δ/4, rOut := δ/2, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let U : Set (ℝ × X dim) := (univ : Set ℝ) ×ˢ closedBall (0 : X dim) (1 : ℝ)
  let g (q : ℝ × X dim) : ℝ := χ q.1*f q.1 q.2
  have hχV : tsupport (χ : ℝ → ℝ) ⊆ V := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (show χ.rOut < δ by dsimp [χ]; linarith)).trans hδV
  have hG : ContDiffOn ℝ ∞ g U := by
    intro q hq
    by_cases hqV : q.1 ∈ V
    · have hNear : V ×ˢ closedBall (0 : X dim) 1 ∈ 𝓝[U] q := by
        have hh : Prod.fst ⁻¹' V ∈ 𝓝 q := (hV.preimage continuous_fst).mem_nhds hqV
        exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
          ⟨Prod.fst ⁻¹' V,hh,fun x hx => ⟨hx.1,hx.2.2⟩⟩
      exact (((χ.contDiff.comp contDiff_fst).contDiffWithinAt).mul (hFj q ⟨hqV,hq.2⟩)).mono_of_mem_nhdsWithin hNear
    · have hn : ∀ᶠ q' : ℝ × X dim in 𝓝 q, q'.1 ∉ tsupport (χ : ℝ → ℝ) :=
        continuous_fst.continuousAt.eventually
          ((isClosed_tsupport _).isOpen_compl.mem_nhds (fun h => hqV (hχV h)))
      have hZero : g =ᶠ[𝓝 q] 0 := by
        filter_upwards [hn] with q' hq'
        simp only [g,image_eq_zero_of_notMem_tsupport hq',zero_mul,Pi.zero_apply]
      exact (contDiffAt_const.congr_of_eventuallyEq hZero).contDiffWithinAt
  obtain ⟨b,hb,hEq⟩ := exists_smooth_extension_prod_closedUnitBall hG
    χ.hasCompactSupport.isCompact (fun t ht z => by
      simp only [g,image_eq_zero_of_notMem_tsupport ht,zero_mul])
  let W := ball (0 : ℝ) χ.rIn
  have hWV : W ⊆ V := (ball_subset_ball (show χ.rIn ≤ δ by dsimp [χ]; linarith)).trans hδV
  refine ⟨W,isOpen_ball,mem_ball_self χ.rIn_pos,hWV,b,hb,?_⟩
  intro t ht
  have he (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : b (t,z) = f t z := by
    rw [hEq (show (t,z) ∈ U from ⟨mem_univ _,hz⟩)]
    change χ t*f t z = f t z
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall ht),one_mul]
  refine ⟨fun z hz => (he z (sphere_subset_closedBall hz)).trans ((hF t (hWV ht)).1 hz),?_⟩
  intro z hz
  have hNear : (fun x => b (t,x)) =ᶠ[𝓝 z] f t := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx using he x (ball_subset_closedBall hx)
  rw [negativeBallDivergence_congr_germ EventuallyEq.rfl hNear]
  exact (hF t (hWV ht)).2 hz

/-- Local coefficient data near the reference closed ball suffice for the
jointly smooth solution family. -/
theorem exists_local_joint_smooth_ballResponse
    {U : Set (ℝ × X dim)} (hU : IsOpen U)
    (hClosed : {(0 : ℝ)} ×ˢ closedBall (0 : X dim) 1 ⊆ U)
    {a : ℝ × X dim → Mat dim} (ha : ContDiffOn ℝ ∞ a U)
    (hPos : ∀ p ∈ U, (a p).PosDef)
    (u : ℝ × X dim → ℝ) (hu : ContDiff ℝ ∞ u) :
    ∃ W : Set ℝ, IsOpen W ∧ (0 : ℝ) ∈ W ∧
      ∃ Z : Set (X dim), IsOpen Z ∧ closedBall (0 : X dim) 1 ⊆ Z ∧
      ∃ A : ℝ × X dim → Mat dim, ContDiff ℝ ∞ A ∧ EqOn A a (W ×ˢ Z) ∧
      ∃ b : ℝ × X dim → ℝ, ContDiff ℝ ∞ b ∧ ∀ t ∈ W,
        EqOn (fun z => b (t,z)) (fun z => u (t,z)) (standardSphere dim) ∧
        EqOn (negativeBallDivergence (fun z => A (t,z)) (fun z => b (t,z))) 0
          (ball (0 : X dim) 1) := by
  classical
  obtain ⟨A,hA,hAk,S,hS,hCS,hSU,hEq⟩ := exists_contDiff_extension_near_compact hU
    (isCompact_singleton.prod (isCompact_closedBall (0 : X dim) 1)) hClosed ha
  obtain ⟨V,Z,hV,hZ,h₀,hCZ,hVZ⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0:ℝ))) (isCompact_closedBall (0 : X dim) 1) hS hCS
  let K : Set (X dim) := Prod.snd '' tsupport A
  have hK := hAk.isCompact.image (continuous_snd : Continuous (Prod.snd : ℝ × X dim → X dim))
  have hSupp (t : ℝ) (z : X dim) (hz : z ∉ K) : A (t,z) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (mem_image_of_mem Prod.snd h))
  have hEll (t : ℝ) (ht : t ∈ V) : ∃ lo hi,
      UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (fun z => A (t,z)) lo hi :=
    exists_uniformEllipticOn_fixedBall _ (hA.continuous.comp (continuous_const.prodMk continuous_id))
      (fun z hz => by
        have hq := hVZ (show (t,z) ∈ V ×ˢ Z from ⟨ht,hCZ hz⟩)
        rw [hEq hq]
        exact hPos _ (hSU hq))
  choose l L hEL using hEll
  let lo (t : ℝ) := if ht : t ∈ V then l t ht else 1
  let hi (t : ℝ) := if ht : t ∈ V then L t ht else 1
  obtain ⟨W,hW,h₀W,hWV,b,hb,hB⟩ := exists_joint_smooth_ballResponse hV (h₀ (mem_singleton _))
    A hA K hK hSupp u hu lo hi (fun t ht => by simpa only [lo,hi,dite_eq_left ht] using hEL t ht)
  exact ⟨W,hW,h₀W,Z,hZ,hCZ,A,hA,
    (fun _ h => hEq (hVZ ⟨hWV h.1,h.2⟩)),b,hb,hB⟩

end CalderonN
