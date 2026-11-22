module

public import Proof.CalderonN.MovingTrace
public import Proof.CalderonN.NormalInverse
public import Proof.CalderonN.NormalGreenFlux
public import Proof.CalderonN.DilatedGreenBounds

import Proof.CalderonN.GreenWeak
import Proof.CalderonN.WronskianFlux
import Proof.CalderonN.SpherePolarIntegration
import all Proof.CalderonN.MetricDivergence
import all Proof.CalderonN.DilatedGreenBounds
import all Proof.CalderonN.GreenCross
import Proof.CalderonN.MetricPair
import Mathlib.Tactic

public section

open Set Filter Metric MeasureTheory CalderonN
open scoped Topology

namespace CalderonPaper.SphereLocality

variable {n : ℕ}

private theorem eqOn_coordinateDerivative {U : Set (X n)} (hU : IsOpen U)
    {f k : X n → ℝ} (he : EqOn f k U) (i : I n) :
    EqOn (coordDeriv i f) (coordDeriv i k) U := by
  intro x hx
  have hlocal : f =ᶠ[𝓝 x] k := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact he hy
  exact congrArg (fun F : X n →L[ℝ] ℝ => F (axis i))
    (hlocal.fderiv (𝕜 := ℝ)).eq_of_nhds

/-- Coordinate jets depend only on the germ of the coefficient functions. -/
theorem chartPartial_congrOn {U : Set (X n)} (hU : IsOpen U)
    {f k : X n → ℝ} (he : EqOn f k U) (a : I n → ℕ) :
    EqOn (chartPartial a f) (chartPartial a k) U := by
  have hi (i : I n) (r : ℕ) {v w : X n → ℝ} (hvw : EqOn v w U) :
      EqOn ((coordDeriv i)^[r] v) ((coordDeriv i)^[r] w) U := by
    induction r with
    | zero => simpa using hvw
    | succ r ih =>
      simpa only [Function.iterate_succ', Function.comp_apply] using eqOn_coordinateDerivative hU ih i
  unfold chartPartial
  let Ds : List ((X n → ℝ) → X n → ℝ) := List.ofFn fun i : I n => (coordDeriv i)^[a i]
  have hDs : ∀ D ∈ Ds, ∀ {v w : X n → ℝ}, EqOn v w U → EqOn (D v) (D w) U := by
    intro D hD v w h
    change D ∈ List.ofFn (fun i : I n => (coordDeriv i)^[a i]) at hD
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hD
    exact hi i (a i) h
  change EqOn (Ds.foldr (fun D u => D u) f) (Ds.foldr (fun D u => D u) k) U
  revert hDs
  induction Ds with
  | nil => intro _; exact he
  | cons D Ds ih =>
    intro hDs
    exact hDs D (by simp) (ih (fun D' hD' => @hDs D' (List.mem_cons_of_mem D hD')))

theorem smallJet_congrOn {U : Set (X n)} (hU : IsOpen U)
    {g g' q q' : MetricField n} (hg : EqOn g g' U) (hq : EqOn q q' U) :
    EqOn (smallJet g q) (smallJet g' q') U := by
  intro x hx
  have hc (i j : I n) : EqOn (fun y => (principal g q y - (g y)⁻¹) i j)
      (fun y => (principal g' q' y - (g' y)⁻¹) i j) U := by
    intro y hy
    simp only [CalderonN.principal, hg hy, hq hy]
  unfold smallJet
  exact Finset.sum_congr rfl fun a _ => congrArg Real.sqrt (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => congrArg (fun t : ℝ => t ^ 2) (chartPartial_congrOn hU (hc i j) _ hx))

/-- The same flow remains a normal coordinate system after replacing its
metric field by one equal throughout the open ambient patch. -/
theorem normalCoordinates_congrOn {Y Ω : Set (X n)} (hΩ : IsOpen Ω) (hY : Y ⊆ Ω)
    {g h : MetricField n} (he : EqOn g h Ω)
    {E : (X n) × (X n) → X n} {r : X n → ℝ}
    (hE : NormalCoordinates Y Ω g E r) : NormalCoordinates Y Ω h E r := by
  have hPair (x : X n) (hx : x ∈ Ω) (u v : X n) :
      metricPair g x u v = metricPair h x u v := by simp only [metricPair, he hx]
  have hDisk (y : X n) (hy : y ∈ Y) : disk g y (r y) = disk h y (r y) := by
    ext v
    unfold disk
    exact Iff.of_eq (congrArg (· ≤ r y ^ 2) (hPair y (hY hy) v v))
  have hTube : {p : (X n) × (X n) | p.1 ∈ Y ∧ p.2 ∈ disk g p.1 (r p.1)} =
      {p : (X n) × (X n) | p.1 ∈ Y ∧ p.2 ∈ disk h p.1 (r p.1)} := by
    ext p
    exact ⟨fun hp => ⟨hp.1, hDisk _ hp.1 ▸ hp.2⟩, fun hp => ⟨hp.1, (hDisk _ hp.1).symm ▸ hp.2⟩⟩
  have hconn (x : X n) (hx : x ∈ Ω) (v w : X n) :
      connection g x v w = connection h x v w := by
    have hder (a b c : I n) : coordDeriv a (fun y => g y b c) x =
        coordDeriv a (fun y => h y b c) x :=
      eqOn_coordinateDerivative hΩ (fun y hy => congrArg (fun M : Mat n => M b c) (he hy)) a hx
    have hΓ (a b c : I n) : christoffel g x a b c = christoffel h x a b c := by
      simp only [christoffel, he hx, hder]
    simp only [connection, hΓ]
  refine ⟨hTube ▸ hE.1, ?_⟩
  intro y hy
  obtain ⟨hpos, hinj, hdata⟩ := hE.2 y hy
  refine ⟨hpos, hDisk y hy ▸ hinj, ?_⟩
  intro v hv
  have hvg : v ∈ disk g y (r y) := (hDisk y hy).symm ▸ hv
  obtain ⟨himage, hF, h0, h1, hODE⟩ := hdata v hvg
  refine ⟨himage, hF, h0, h1, ?_⟩
  intro t ht
  let path := fun s : ℝ => E (y, s • v)
  have htSq : t^2 ≤ 1 := by nlinarith [ht.1, ht.2, mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have hd : t • v ∈ disk g y (r y) := by
    change metricPair g y (t • v) (t • v) ≤ r y ^ 2
    rw [metricPair_smul_same]
    by_cases hnonneg : 0 ≤ metricPair g y v v
    · exact (by simpa only [one_mul] using mul_le_mul_of_nonneg_right htSq hnonneg :
        t^2 * metricPair g y v v ≤ metricPair g y v v).trans hvg
    · exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_ge hnonneg)).trans (sq_nonneg _)
  have hpΩ : path t ∈ Ω := (hdata _ hd).1
  exact (hODE t ht).trans (congrArg Neg.neg (hconn _ hpΩ _ _))

theorem bundle_congr {Y : Set (X n)} {g h : MetricField n} (he : EqOn g h Y) :
    bundle Y g = bundle Y h := by
  ext q
  constructor
  · rintro ⟨hy, hq⟩
    exact ⟨hy, by simpa only [sphereAt, mem_ofPred_eq, metricPair, he hy] using hq⟩
  · rintro ⟨hy, hq⟩
    exact ⟨hy, by simpa only [sphereAt, mem_ofPred_eq, metricPair, he hy] using hq⟩

theorem normalPairDomain_congr {Y : Set (X n)} {g h : MetricField n} (he : EqOn g h Y)
    (ρ : ℝ) (E : (X n) × (X n) → X n) :
    normalPairDomain Y g ρ E = normalPairDomain Y h ρ E := by
  have hvel : normalVelocityDomain Y g ρ = normalVelocityDomain Y h ρ := by
    ext q
    constructor
    · rintro ⟨hy, hq⟩
      exact ⟨hy, by simpa only [metricPair, he hy] using hq⟩
    · rintro ⟨hy, hq⟩
      exact ⟨hy, by simpa only [metricPair, he hy] using hq⟩
  rw [normalPairDomain, normalPairDomain, hvel]

/-- The harmonicity predicate is local in both fields. -/
theorem harmonic_congrOn {U : Set (X n)} (hU : IsOpen U)
    {g q : MetricField n} {u v : X n → ℝ} (hg : EqOn g q U) (hu : EqOn u v U)
    (h : Harmonic U g u) : Harmonic U q v := by
  refine ⟨h.1.congr hu.symm, fun x hx => ?_⟩
  exact (laplace_congrOn hU hg hu hx).symm.trans (h.2 x hx)

theorem closedBallImage_congr_at {g q : MetricField n} {y : X n} (h : g y = q y)
    (E : X n × X n → X n) (r : X n → ℝ) :
    closedBallImage g E r y = closedBallImage q E r y := by
  unfold closedBallImage
  have he : disk g y (r y) = disk q y (r y) := by
    ext v
    simp only [disk,mem_ofPred_eq,metricPair,h]
  rw [he]

theorem closedBallImage_subset_of_normalCoordinates {Y Ω : Set (X n)} {g : MetricField n}
    {y : X n} {E : X n × X n → X n} {ρ : ℝ} {r : X n → ℝ}
    (h : NormalCoordinates Y Ω g E (fun _ => ρ)) (hy : y ∈ Y) (hr : 0 ≤ r y) (hρ : r y ≤ ρ) :
    closedBallImage g E r y ⊆ Ω := by
  rintro _ ⟨v,hv,rfl⟩
  exact ((h.2 y hy).2.2 v (hv.trans (pow_le_pow_left₀ hr hρ 2))).1

theorem harmonicOnBall_congr_metric {B : Set (X n)} {g q : MetricField n} {u : X n → ℝ}
    (h : EqOn g q B) (hu : HarmonicOnBall g B u) : HarmonicOnBall q B u := by
  refine ⟨hu.1, fun x hx => ?_⟩
  exact (laplace_congrOn isOpen_interior (h.mono interior_subset) (fun _ _ => rfl) hx).symm.trans (hu.2 _ hx)

/-- The literal normal Green flux only uses the first metric on the
parametrized sphere and the value of the frame at the center. -/
theorem normalSphereGreenFlux_congr_at
    {g q : MetricField n} {E : X n × X n → X n} {e e' : Frame n} {r : X n → ℝ}
    {G : X n × X n → ℝ} {y : X n} {u : X n → ℝ}
    (he : e y = e' y)
    (hg : ∀ z ∈ standardSphere n, g (normalBallChartMap E e y (r y) z) =
      q (normalBallChartMap E e y (r y) z)) :
    normalSphereGreenFlux g E e r G y u = normalSphereGreenFlux q E e' r G y u := by
  let F := normalBallChartMap E e y (r y)
  have hF : F = normalBallChartMap E e' y (r y) := by
    funext z
    simp only [F,normalBallChartMap,frameVector,he]
  let F' := normalBallChartMap E e' y (r y)
  change unitSphereFlux (wronskianFlux (pullbackMetric g F) (u ∘ F) (fun z => G (F z,y))) =
    unitSphereFlux (wronskianFlux (pullbackMetric q F') (u ∘ F') (fun z => G (F' z,y)))
  rw [show F' = F from hF.symm]
  apply integral_congr_ae
  filter_upwards with z
  have hz : (z : X n) ∈ standardSphere n := z.property
  have hgF : g (F z) = q (F z) := hg z hz
  have hm : pullbackMetric g F z = pullbackMetric q F z := by
    simp only [pullbackMetric,hgF]
  simp only [wronskianFlux,divergenceFlux,divergenceCoeff,chartVolume,hm]

/-- Restricting the known side to a smaller chart does not change the
normalized mixed Green prescription on pairs in that chart. -/
theorem dilatedInitialGreen_inter_eq {D W : Set (X n)} {l : ℝ}
    (G₁ G₂ : X n × X n → ℝ) (q : X n × X n) (h₂ : l • q.2 ∈ D) :
    dilatedInitialGreen (W ∩ D) G₁ G₂ l q = dilatedInitialGreen W G₁ G₂ l q := by
  classical
  unfold dilatedInitialGreen initialGreenKernel
  by_cases hw : l • q.2 ∈ W
  · rw [ite_eq_left (show q.2 ∈ {x | l • x ∈ W ∩ D} from ⟨hw,h₂⟩),
      ite_eq_left (show q.2 ∈ {x | l • x ∈ W} from hw)]
  · rw [ite_eq_right (show q.2 ∉ {x | l • x ∈ W ∩ D} from fun hx => hw hx.1),
      ite_eq_right (show q.2 ∉ {x | l • x ∈ W} from hw)]

theorem normalPairDomain_subset_of_normalCoordinates {Y Z Ω : Set (X n)} (hYZ : Y ⊆ Z)
    {g : MetricField n} {E : X n × X n → X n} {ρ : ℝ}
    (h : NormalCoordinates Z Ω g E (fun _ => ρ)) :
    normalPairDomain Y g ρ E ⊆ Ω ×ˢ Y := by
  rintro _ ⟨⟨y,v⟩,hVel,rfl⟩
  exact ⟨((h.2 y (hYZ hVel.1)).2.2 v hVel.2.le).1,hVel.1⟩

end CalderonPaper.SphereLocality
