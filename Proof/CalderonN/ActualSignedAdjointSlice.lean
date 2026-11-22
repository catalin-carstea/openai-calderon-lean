module

public import Proof.CalderonN.ActualSignedAdjoint

import Mathlib.Tactic

/-! Adapted from `ActualSignedAdjointSlice` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2200000

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

variable {γ g : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
  (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => γ p.1 p.2 i j))
  (hγPos : ∀ lam y, (γ lam y).PosDef)
  (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => g p.1 p.2 i j))
  (hgPos : ∀ lam y, (g lam y).PosDef)
  (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
  (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i))

include hγ hγPos hg hgPos hE he

theorem contDiffOn_signedNormalFirstAdjoint_slice (p : (SignedNormalParameter dim))
    (hp : {p} ×ˢ closedBall (0 : (X dim)) 1 ⊆ signedNormalNondegenerate E e) (j : (I dim)) :
    ContDiffOn ℝ ∞ (fun z => signedNormalFirstAdjoint γ g E e j (p,z)) ({0}ᶜ : Set (X dim)) := by
  obtain ⟨W,_,hpW,ha,_⟩ := exists_smooth_signedNormalAdjoints hγ hγPos hg hgPos hE he p hp 0 j
  exact ha.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hpW,hz⟩)

/-- The actual first scaled trace and its successive angular adjoint have
the specified signed-radius representatives on each actual sphere. -/
theorem scaledActualAdjoints_eq_signed {Y : Set (X dim)} {lam : ℝ}
    {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) {y : (X dim)} (hy : y ∈ Y) (hR : r y ≠ 0)
    (hFrame : ∀ i j, metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0)
    (hA : IsMovingTraceAdjoint Y (γ lam) (g lam) (e lam) (E lam) r
      (actualMovingTraceAdjoint (γ lam) (g lam) (E lam) (e lam) r))
    (hp : {actualSignedNormalParameter lam r y} ×ˢ closedBall (0 : (X dim)) 1 ⊆ signedNormalNondegenerate E e) :
    let A := actualMovingTraceAdjoint (γ lam) (g lam) (E lam) (e lam) r
    let α := scaledFirstTrace r A
    let p := actualSignedNormalParameter lam r y
    (∀ w ∈ (standardSphere dim), ∀ j, α j (y,frameVector (e lam) y w) =
      (signedNormalFirstAdjoint γ g E e j (p,w) : ℂ)) ∧
    (∀ w ∈ (standardSphere dim), ∀ i j, let q := (y,frameVector (e lam) y w)
      (r y : ℂ) * adjointField A i (α j) q -
        Complex.ofReal (coordDeriv i r y) * α j q =
          (signedNormalAdjointRemainder γ g E e i j (p,w) : ℂ)) := by
  let A := actualMovingTraceAdjoint (γ lam) (g lam) (E lam) (e lam) r
  let α := scaledFirstTrace r A
  let p := actualSignedNormalParameter lam r y
  let J (z : (X dim)) := (p,z)
  let U := J ⁻¹' signedNormalNondegenerate E e
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  let T := U ∩ N
  have hJ : ContDiff ℝ ∞ J := contDiff_const.prodMk contDiff_id
  have hU : IsOpen U := (signedNormalNondegenerate_isOpen hE he).preimage hJ.continuous
  have hT : IsOpen T := hU.inter isClosed_singleton.isOpen_compl
  have hCU : closedBall (0 : (X dim)) 1 ⊆ U := fun z hz => hp ⟨mem_singleton _,hz⟩
  have hST : (standardSphere dim) ⊆ T := by
    intro z hz
    refine ⟨hCU (sphere_subset_closedBall hz),?_⟩
    change z ≠ 0
    intro hzero
    have hn := mem_sphere_zero_iff_norm.mp hz
    simp [hzero] at hn
  have hT₀ : (0 : (X dim)) ∉ T := fun h => h.2 rfl
  have hm : SmoothMetric U (fun z => signedNormalMetric g E e (p,z)) := by
    refine ⟨fun i j => ((contDiff_signedNormalMetric_entry hg hE he i j).comp hJ).contDiffOn,?_⟩
    exact fun _ hz => signedNormalMetric_posDef hgPos hz
  have hV (i : (I dim)) : ContDiffOn ℝ ∞ (fun z => signedNormalVelocity γ E e i (p,z)) T :=
    (contDiffOn_signedNormalVelocity hγ hγPos hE he i).comp hJ.contDiffOn (fun _ hz => hz.1)
  have h₁ : ∀ w ∈ (standardSphere dim), ∀ j, α j (y,frameVector (e lam) y w) =
      (signedNormalFirstAdjoint γ g E e j (p,w) : ℂ) := by
    intro w hw j
    exact scaled_actualMovingTraceAdjoint_eq_signed hy hR hFrame j 1 (smoothNear_one_bundle Y (γ lam))
      (fun _ => 1) hU hT hCU hST inter_subset_left hT₀ hm (hV j) contDiffOn_const
      (fun _ _ => by simp) hw
  refine ⟨h₁,?_⟩
  intro w hw i j
  have ha := contDiffOn_signedNormalFirstAdjoint_slice hγ hγPos hg hgPos hE he p hp j
  have h₂ := scaled_actualMovingTraceAdjoint_eq_signed hy hR hFrame i (α j)
    (smoothNear_scaledFirstTrace hr hA j) (signedNormalFirstAdjoint γ g E e j)
    hU hT hCU hST inter_subset_left hT₀ hm (hV i) (ha.mono inter_subset_right)
    (fun z hz => h₁ z hz j) hw
  change (r y : ℂ) * adjointField A i (α j) (y,frameVector (e lam) y w) -
    Complex.ofReal (coordDeriv i r y) * α j (y,frameVector (e lam) y w) =
      (signedNormalAdjointRemainder γ g E e i j (p,w) : ℂ)
  rw [h₂,h₁ w hw j]
  simp only [signedNormalAdjointRemainder,Complex.ofReal_sub,Complex.ofReal_mul]
  rfl

end CalderonN
