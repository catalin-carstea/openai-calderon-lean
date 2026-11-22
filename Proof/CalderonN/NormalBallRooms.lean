module

public import Proof.CalderonN.NormalInverse
public import Proof.CalderonN.SphereFrame

import Proof.CalderonN.MetricPair
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def normalRadialSq (γ : (MetricField dim)) (V : (X dim) × (X dim) → (X dim)) (q : (X dim) × (X dim)) : ℝ :=
  metricPair γ q.2 (V q) (V q)

theorem continuousOn_normalRadialSq {N : Set ((X dim) × (X dim))} {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {V : (X dim) × (X dim) → (X dim)} (hV : ContinuousOn V N) :
    ContinuousOn (normalRadialSq γ V) N := by
  have h (i j : (I dim)) : ContinuousOn (fun q : (X dim) × (X dim) => γ q.2 i j) N :=
    ((contDiffOn_univ.mp (hγ.1 i j)).continuous.comp continuous_snd).continuousOn
  have hv (i : (I dim)) : ContinuousOn (fun q : (X dim) × (X dim) => V q i) N :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hV
  unfold normalRadialSq metricPair
  exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
    ((h i j).mul (hv i)).mul (hv j)

/-- The open ball around a center, within a joint normal tube with inverse
velocity `V`. The radius applies to the true metric velocity norm. -/
@[expose] def normalBallRoom (N : Set ((X dim) × (X dim))) (γ : (MetricField dim)) (V : (X dim) × (X dim) → (X dim)) (y : (X dim)) (r : ℝ) :
    Set (X dim) :=
  {x | (x,y) ∈ N ∧ normalRadialSq γ V (x,y) < r^2}

@[expose] def normalShellRoom (N : Set ((X dim) × (X dim))) (γ : (MetricField dim)) (V : (X dim) × (X dim) → (X dim)) (y : (X dim))
    (a b : ℝ) : Set (X dim) :=
  {x | (x,y) ∈ N ∧ a^2 < normalRadialSq γ V (x,y) ∧ normalRadialSq γ V (x,y) < b^2}

theorem isOpen_normalBallRoom {N : Set ((X dim) × (X dim))} (hN : IsOpen N)
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {V : (X dim) × (X dim) → (X dim)} (hV : ContinuousOn V N) (y : (X dim)) (r : ℝ) :
    IsOpen (normalBallRoom N γ V y r) :=
  ((continuousOn_normalRadialSq hγ hV).isOpen_inter_preimage hN isOpen_Iio).preimage
    (continuous_id.prodMk continuous_const)

theorem isOpen_normalShellRoom {N : Set ((X dim) × (X dim))} (hN : IsOpen N)
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {V : (X dim) × (X dim) → (X dim)} (hV : ContinuousOn V N) (y : (X dim)) (a b : ℝ) :
    IsOpen (normalShellRoom N γ V y a b) :=
  ((continuousOn_normalRadialSq hγ hV).isOpen_inter_preimage hN isOpen_Ioo).preimage
    (continuous_id.prodMk continuous_const)

theorem mem_closedBallImage_iff_normalRadialSq
    {Y : Set (X dim)} {γ : (MetricField dim)} {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {x y : (X dim)} (hy : y ∈ Y) {r : ℝ} (hr : 0 ≤ r) (hρ : r < ρ) :
    x ∈ closedBallImage γ E (fun _ => r) y ↔
      (x,y) ∈ normalPairDomain Y γ ρ E ∧ normalRadialSq γ V (x,y) ≤ r^2 := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    have hVel : (y,v) ∈ normalVelocityDomain Y γ ρ :=
      ⟨hy,hv.trans_lt (pow_lt_pow_left₀ hρ hr (by decide : 2 ≠ 0))⟩
    refine ⟨⟨(y,v),hVel,rfl⟩,?_⟩
    unfold normalRadialSq
    rw [hExact (y,v) hVel]
    exact hv
  · rintro ⟨hpair,hrad⟩
    exact ⟨V (x,y),hrad,(hInv (x,y) hpair).2⟩

theorem closedBallImage_subset_normalBallRoom
    {Y : Set (X dim)} {γ : (MetricField dim)} {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}
    (hExact : ∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {y : (X dim)} (hy : y ∈ Y) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ ρ) :
    closedBallImage γ E (fun _ => a) y ⊆ normalBallRoom (normalPairDomain Y γ ρ E) γ V y b := by
  intro x hx
  obtain ⟨hpair,hrad⟩ :=
    (mem_closedBallImage_iff_normalRadialSq hExact hInv hy ha (hab.trans_le hb)).mp hx
  exact ⟨hpair,hrad.trans_lt (pow_lt_pow_left₀ hab ha (by decide : 2 ≠ 0))⟩

theorem closedBallImage_eq_frameImage (γ : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (y : (X dim)) (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : ℝ} (hr : 0 ≤ r) :
    closedBallImage γ E (fun _ => r) y =
      (fun w => E (y,frameVector e y w)) '' closedBall (0 : (X dim)) r := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    let w := frameCoordinates γ y (e y) v
    have hw : w ∈ closedBall (0 : (X dim)) r := by
      apply mem_closedBall_zero_iff.mpr
      apply (sq_le_sq₀ (norm_nonneg _) hr).mp
      rw [norm_frameCoordinates_sq γ y v (e y) he]
      exact hv
    exact ⟨w,hw,congrArg (fun a => E (y,a)) (frameVector_frameCoordinates γ y v (e y) he)⟩
  · rintro ⟨w,hw,rfl⟩
    refine ⟨frameVector e y w,?_,rfl⟩
    change metricPair γ y (frameVector e y w) (frameVector e y w) ≤ r^2
    rw [metricPair_frameVector γ e y w w he]
    have hn := pow_le_pow_left₀ (norm_nonneg w) (mem_closedBall_zero_iff.mp hw) 2
    rw [EuclideanSpace.real_norm_sq_eq] at hn
    simpa only [pow_two] using hn

theorem isCompact_closedBallImage (γ : (MetricField dim)) {E : (X dim) × (X dim) → (X dim)}
    (hE : Continuous E) (e : (Frame dim)) (y : (X dim))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : ℝ} (hr : 0 ≤ r) : IsCompact (closedBallImage γ E (fun _ => r) y) := by
  rw [closedBallImage_eq_frameImage γ E e y he hr]
  exact (isCompact_closedBall _ _).image (hE.comp (continuous_const.prodMk (continuous_frameVector e y)))

end CalderonN
