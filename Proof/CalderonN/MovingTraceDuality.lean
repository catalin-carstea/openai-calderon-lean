module

public import Proof.CalderonN.SphereIntegralCalculus

import Proof.CalderonN.CovariantHessian
import Proof.CalderonN.CrossProductWeak
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.MetricPair
import Proof.CalderonN.NormalizedMetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic

/-! Adapted from `MovingTraceDuality` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Pair a moving angular field with the trace of a fixed spatial test. -/
@[expose] def sphereTracePair (e : (Frame dim)) (E : (X dim) × (X dim) → (X dim)) (r : (X dim) → ℝ)
    (φ : (Field dim)) (u : (X dim) → ℝ) (y : (X dim)) : ℂ :=
  sphereAverage e y (fun w => φ (y,w) * (u (endpoint E r (y,w)) : ℂ))

theorem endpoint_mem_closedBallImage {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ}
    {y w : (X dim)} (hw : w ∈ sphereAt γ y) :
    endpoint E r (y,w) ∈ closedBallImage γ E r y := by
  refine ⟨r y • w,?_ ,rfl⟩
  change metricPair γ y (r y • w) (r y • w) ≤ (r y)^2
  rw [metricPair_smul_same,show metricPair γ y w w = 1 from hw,mul_one]

theorem smoothNear_endpointTrace {V U : Set (X dim)} (hV : IsOpen V) (hU : IsOpen U)
    {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    {r : (X dim) → ℝ} (hr : ContDiffOn ℝ ∞ r V)
    {u : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hball : ∀ y ∈ V, closedBallImage γ E r y ⊆ U) :
    smoothNear (fun q => u (endpoint E r q)) (bundle V γ) := by
  let D := V ×ˢ (univ : Set (X dim))
  have hD : IsOpen D := hV.prod isOpen_univ
  have hmap : ContDiffOn ℝ ∞ (endpoint E r) D :=
    hE.comp_contDiffOn (contDiffOn_fst.prodMk
      ((hr.comp contDiffOn_fst (fun _ h => h.1)).smul contDiffOn_snd))
  let S := D ∩ (endpoint E r) ⁻¹' U
  have hS : IsOpen S := hmap.continuousOn.isOpen_inter_preimage hD hU
  refine ⟨S,hS,fun q hq => ?_,hu.comp (hmap.mono inter_subset_left) inter_subset_right⟩
  exact ⟨⟨hq.1,mem_univ _⟩,hball q.1 hq.1 (endpoint_mem_closedBallImage hq.2)⟩

theorem contDiffOn_horizontalDirection {V : Set (X dim)} (hV : IsOpen V)
    {γ : (MetricField dim)} (hγ : SmoothMetric V γ) (i : (I dim)) :
    ContDiffOn ℝ ∞ (fun p : (X dim) × (X dim) => (axis i, -connection γ p.1 (axis i) p.2))
      (V ×ˢ univ) := by
  refine contDiffOn_const.prodMk ((?_ : ContDiffOn ℝ ∞ _ (V ×ˢ univ)).neg)
  apply (contDiffOn_piLp 2).mpr
  intro k
  change ContDiffOn ℝ ∞ (fun p : (X dim) × (X dim) =>
    ∑ a, ∑ b, christoffel γ p.1 k a b * (axis i) a * p.2 b) (V ×ˢ univ)
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact (((contDiffOn_christoffel hV hγ k a b).comp contDiffOn_fst
    (fun _ hp => hp.1)).mul contDiffOn_const).mul
      (((EuclideanSpace.proj (𝕜 := ℝ) b).contDiff.comp contDiff_snd).contDiffOn)

private theorem smoothNear_horizontal {V : Set (X dim)} (hV : IsOpen V)
    {γ : (MetricField dim)} (hγ : SmoothMetric V γ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : (X dim) × (X dim) → E}
    (hf : smoothNear f (bundle V γ)) (i : (I dim)) :
    smoothNear (fun p => horizontal γ f p.1 p.2 (axis i)) (bundle V γ) := by
  obtain ⟨O,hO,hSub,hfO⟩ := hf
  let Q := O ∩ (V ×ˢ (univ : Set (X dim)))
  refine ⟨Q,hO.inter (hV.prod isOpen_univ),fun p hp => ⟨hSub hp,⟨hp.1,mem_univ _⟩⟩,?_⟩
  exact ((hfO.fderiv_of_isOpen (m := ∞) hO (by simp)).mono inter_subset_left).clm_apply
    ((contDiffOn_horizontalDirection hV hγ i).mono inter_subset_right)

private theorem integrable_frameFiber {V : Set (X dim)} {γ : (MetricField dim)} {e : (Frame dim)}
    {y : (X dim)} (hy : y ∈ V)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {f : (Field dim)} (hf : smoothNear f (bundle V γ)) :
    Integrable (fun w : ↥(standardSphere dim) => f (y,frameVector e y w)) (sphereProbability dim) := by
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
  obtain ⟨S,_,hSub,hfS⟩ := hf
  have hMap : Continuous (fun w : ↥(standardSphere dim) => (y,frameVector e y w)) :=
    continuous_const.prodMk ((continuous_frameVector e y).comp continuous_subtype_val)
  exact (hfS.continuousOn.comp_continuous hMap
    (fun w => hSub ⟨hy,frameVector_mem_sphere γ e y he w⟩)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem smoothNear_mul_fields {V : Set (X dim)} {γ : (MetricField dim)}
    {φ τ : (Field dim)} (hφ : smoothNear φ (bundle V γ)) (hτ : smoothNear τ (bundle V γ)) :
    smoothNear (fun p => φ p * τ p) (bundle V γ) := by
  obtain ⟨S,hSo,hS,hφS⟩ := hφ
  obtain ⟨T,hTo,hT,hτT⟩ := hτ
  exact ⟨S ∩ T,hSo.inter hTo,fun p hp => ⟨hS hp,hT hp⟩,
    (hφS.mono inter_subset_left).mul (hτT.mono inter_subset_right)⟩

theorem smoothNear_add_fields {V : Set (X dim)} {γ : (MetricField dim)}
    {φ τ : (Field dim)} (hφ : smoothNear φ (bundle V γ)) (hτ : smoothNear τ (bundle V γ)) :
    smoothNear (fun p => φ p + τ p) (bundle V γ) := by
  obtain ⟨S,hSo,hS,hφS⟩ := hφ
  obtain ⟨T,hTo,hT,hτT⟩ := hτ
  exact ⟨S ∩ T,hSo.inter hTo,fun p hp => ⟨hS hp,hT hp⟩,
    (hφS.mono inter_subset_left).add (hτT.mono inter_subset_right)⟩

theorem smoothNear_traceDerivative {V : Set (X dim)} (hV : IsOpen V)
    {γ g : (MetricField dim)} (hγ : SmoothMetric V γ) {e : (Frame dim)}
    {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ} {A : (TraceAdjoint dim)}
    (hA : IsMovingTraceAdjoint V γ g e E r A)
    {φ : (Field dim)} (hφ : smoothNear φ (bundle V γ)) (i : (I dim)) :
    smoothNear (traceDerivative γ A i φ) (bundle V γ) :=
  smoothNear_add_fields (smoothNear_horizontal hV hγ hφ i) (hA i φ hφ).1

private theorem smoothNear_ofReal_field {S : Set ((X dim) × (X dim))} {f : (X dim) × (X dim) → ℝ}
    (hf : smoothNear f S) : smoothNear (fun p => (f p : ℂ)) S := by
  obtain ⟨V,hV,hSV,hfV⟩ := hf
  exact ⟨V,hV,hSV,Complex.ofRealCLM.contDiff.comp_contDiffOn hfV⟩

private theorem horizontal_ofReal {γ : (MetricField dim)} {τ : (X dim) × (X dim) → ℝ} {y w : (X dim)}
    (hτ : DifferentiableAt ℝ τ (y,w)) (i : (I dim)) :
    horizontal γ (fun p => (τ p : ℂ)) y w (axis i) =
      (↑(horizontal (E := ℝ) γ τ y w (axis i)) : ℂ) := by
  exact congrArg (fun L : (X dim) × (X dim) →L[ℝ] ℂ => L (axis i,-connection γ y (axis i) w))
    (Complex.ofRealCLM.hasFDerivAt.comp (y,w) hτ.hasFDerivAt).fderiv

set_option maxHeartbeats 1200000 in
/-- Horizontal differentiation of the moving pairing is dual to the
frozen trace derivative, with the spatial test held fixed. -/
theorem coordDeriv_sphereTracePair {V Y : Set (X dim)} (hV : IsOpen V) (hVY : V ⊆ Y)
    {γ g : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {e : (Frame dim)} (he : ∀ y ∈ V, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContDiffOn ℝ ∞ (fun y => e y i) V)
    {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ} {A : (TraceAdjoint dim)}
    (hA : IsMovingTraceAdjoint Y γ g e E r A)
    {φ : (Field dim)} (hφ : smoothNear φ (bundle Y γ)) {u : (X dim) → ℝ}
    (hτ : smoothNear (fun q => u (endpoint E r q)) (bundle V γ))
    (hu : ∀ y ∈ V, HarmonicOnBall g (closedBallImage γ E r y) u) (i : (I dim)) :
    EqOn (coordDeriv i (sphereTracePair e E r φ u))
      (sphereTracePair e E r (traceDerivative γ A i φ) u) V := by
  intro y hy
  let τR (p : (X dim) × (X dim)) := u (endpoint E r p)
  let τ (p : (X dim) × (X dim)) : ℂ := τR p
  have restrict {f : (Field dim)} (hf : smoothNear f (bundle Y γ)) : smoothNear f (bundle V γ) := by
    obtain ⟨S,hS,hSub,hf⟩ := hf
    exact ⟨S,hS,fun q hq => hSub ⟨hVY hq.1,hq.2⟩,hf⟩
  have hφV := restrict hφ
  have hτC : smoothNear τ (bundle V γ) := smoothNear_ofReal_field hτ
  have hφτ := smoothNear_mul_fields hφV hτC
  have hAvg := coordDeriv_sphereAverage hV hγ he hec hφτ hy i
  rw [show coordDeriv i (sphereTracePair e E r φ u) y =
    coordDeriv i (fun z => sphereAverage e z (fun w => φ (z,w) * τ (z,w))) y from rfl,hAvg]
  let H (p : (X dim) × (X dim)) := horizontal γ φ p.1 p.2 (axis i)
  let T (p : (X dim) × (X dim)) : ℂ := ↑(horizontal (E := ℝ) γ τR p.1 p.2 (axis i))
  let a := adjointField A i φ
  have hsγ := smoothMetric_restrict hγ (subset_univ V)
  have hH : smoothNear H (bundle V γ) := smoothNear_horizontal hV hsγ hφV i
  have hT : smoothNear T (bundle V γ) :=
    smoothNear_ofReal_field (smoothNear_horizontal hV hsγ hτ i)
  have hAφ : smoothNear a (bundle V γ) := restrict (hA i φ hφ).1
  have hI₁ := integrable_frameFiber hy (he y hy) (smoothNear_mul_fields hH hτC)
  have hI₂ := integrable_frameFiber hy (he y hy) (smoothNear_mul_fields hφV hT)
  have hI₃ := integrable_frameFiber hy (he y hy) (smoothNear_mul_fields hAφ hτC)
  have hDual := (hA i φ hφ).2 y (hVY hy) u (hu y hy)
  change (∫ w : ↥(standardSphere dim), a (y,frameVector e y w) * τ (y,frameVector e y w)
    ∂(sphereProbability dim)) = (∫ w : ↥(standardSphere dim), φ (y,frameVector e y w) *
      T (y,frameVector e y w) ∂(sphereProbability dim)) at hDual
  change (∫ w : ↥(standardSphere dim), horizontal γ (fun p => φ p * τ p) y (frameVector e y w)
    (axis i) ∂(sphereProbability dim)) = (∫ w : ↥(standardSphere dim), (H (y,frameVector e y w) +
      a (y,frameVector e y w)) * τ (y,frameVector e y w) ∂(sphereProbability dim))
  simp_rw [add_mul]
  rw [integral_add hI₁ hI₃,hDual,← integral_add hI₁ hI₂]
  apply integral_congr_ae
  filter_upwards with w
  let q : (X dim) × (X dim) := (y,frameVector e y w)
  have hq : q ∈ bundle V γ := ⟨hy,frameVector_mem_sphere γ e y (he y hy) w⟩
  obtain ⟨S,hS,hVS,hφS⟩ := hφV
  obtain ⟨T',hT',hVT',hτT'⟩ := hτ
  have hDf := (hφS.contDiffAt (hS.mem_nhds (hVS hq))).differentiableAt (by simp)
  have hDt := (hτT'.contDiffAt (hT'.mem_nhds (hVT' hq))).differentiableAt (by simp)
  have hDtC : DifferentiableAt ℝ τ q := Complex.ofRealCLM.differentiableAt.comp q hDt
  change horizontal γ (fun p => φ p * τ p) q.1 q.2 (axis i) = H q * τ q + φ q * T q
  have hTC : horizontal γ τ q.1 q.2 (axis i) = T q := horizontal_ofReal (γ := γ) hDt i
  rw [← hTC]
  simp only [horizontal,H,Prod.mk.eta,fderiv_fun_mul hDf hDtC,add_apply,smul_apply,smul_eq_mul]
  ring

/-- In the combined trace operator, the reference connection cancels
against the drift. -/
private theorem movingTrace_targetConnection (γ g₂ : (MetricField dim))
    (r : (X dim) → ℝ) (A : (TraceAdjoint dim)) (φ : (Field dim)) (q : (X dim) × (X dim)) :
    movingTrace γ g₂ r A φ q =
      (r q.1 : ℂ) * (((dim : ℝ) / ((γ q.1) * (g₂ q.1)⁻¹).trace : ℝ) : ℂ) *
        (∑ i, ∑ j, ((g₂ q.1)⁻¹ i j : ℂ) *
          (traceDerivative γ A i (traceDerivative γ A j φ) q -
            ∑ k, (christoffel g₂ q.1 k i j : ℂ) * traceDerivative γ A k φ q)) := by
  have hSwap (B : I dim → I dim → ℂ) (C : I dim → I dim → I dim → ℂ)
      (W : I dim → ℂ) :
      (∑ k, (∑ i, ∑ j, B i j * C k i j) * W k) =
        ∑ i, ∑ j, B i j * (∑ k, C k i j * W k) := by
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    calc
      _ = ∑ i, ∑ k, ∑ j, B i j * (C k i j * W k) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  simp only [movingTrace,drift,principal,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_sum,
    Complex.ofReal_mul,Complex.ofReal_sub]
  rw [hSwap,mul_assoc (r q.1 : ℂ)]
  apply congrArg (fun z : ℂ => (r q.1 : ℂ) * z)
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  ring

set_option maxHeartbeats 1200000 in
/-- Two derivatives of the trace pairing give the complexified second
metric Laplacian. In particular a pairing known to be real harmonic
annihilates the full moving trace residual. -/
theorem sphereTracePair_movingTrace_eq_zero_of_harmonic
    {V Y : Set (X dim)} (hV : IsOpen V) (hY : IsOpen Y) (hVY : V ⊆ Y)
    {γ g₁ g₂ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {e : (Frame dim)} (he : ∀ y ∈ V, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContDiffOn ℝ ∞ (fun y => e y i) V)
    {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ} {A : (TraceAdjoint dim)}
    (hA : IsMovingTraceAdjoint Y γ g₁ e E r A)
    {φ : (Field dim)} (hφ : smoothNear φ (bundle Y γ)) {u : (X dim) → ℝ}
    (hτ : smoothNear (fun q => u (endpoint E r q)) (bundle V γ))
    (hu : ∀ y ∈ V, HarmonicOnBall g₁ (closedBallImage γ E r y) u)
    {F : (X dim) → ℝ} (hF : Harmonic V g₂ F)
    (hPair : EqOn (sphereTracePair e E r φ u) (fun y => (F y : ℂ)) V) :
    EqOn (sphereTracePair e E r (movingTrace γ g₂ r A φ) u) 0 V := by
  let W (j : (I dim)) := traceDerivative γ A j φ
  let WW (i j : (I dim)) := traceDerivative γ A i (W j)
  have hγY := smoothMetric_restrict hγ (subset_univ Y)
  have hW (j : (I dim)) : smoothNear (W j) (bundle Y γ) := smoothNear_traceDerivative hY hγY hA hφ j
  have hWW (i j : (I dim)) : smoothNear (WW i j) (bundle Y γ) :=
    smoothNear_traceDerivative hY hγY hA (hW j) i
  have h1 (j : (I dim)) := coordDeriv_sphereTracePair hV hVY hγ he hec hA hφ hτ hu j
  have h2 (i j : (I dim)) := coordDeriv_sphereTracePair hV hVY hγ he hec hA (hW j) hτ hu i
  have hcongr {f g : (X dim) → ℂ} (eq : EqOn f g V) (i : (I dim)) :
      EqOn (coordDeriv i f) (coordDeriv i g) V := by
    intro y hy
    have hfg : f =ᶠ[𝓝 y] g := Filter.mem_of_superset (hV.mem_nhds hy) eq
    exact congrArg (fun L : (X dim) →L[ℝ] ℂ => L (axis i)) hfg.fderiv_eq
  have hReal (f : (X dim) → ℝ) (hf : ContDiffOn ℝ ∞ f V) (i : (I dim)) :
      EqOn (coordDeriv i (fun y => (f y : ℂ))) (fun y => (↑(coordDeriv (E := ℝ) i f y) : ℂ)) V := by
    intro y hy
    have hd := ((hf.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    exact congrArg (fun L : (X dim) →L[ℝ] ℂ => L (axis i))
      (Complex.ofRealCLM.hasFDerivAt.comp y hd).fderiv
  have hVal1 (j : (I dim)) : EqOn (sphereTracePair e E r (W j) u)
      (fun y => (↑(coordDeriv (E := ℝ) j F y) : ℂ)) V :=
    (h1 j).symm.trans ((hcongr hPair j).trans (hReal F hF.1 j))
  have hVal2 (i j : (I dim)) : EqOn (sphereTracePair e E r (WW i j) u)
      (fun y => (↑(coordDeriv (E := ℝ) i (coordDeriv j F) y) : ℂ)) V :=
    (h2 i j).symm.trans ((hcongr (hVal1 j) i).trans
      (hReal _ (contDiffOn_coordDeriv hF.1 hV j) i))
  intro y hy
  let q (w : ↥(standardSphere dim)) : (X dim) × (X dim) := (y,frameVector e y w)
  let T (w : ↥(standardSphere dim)) : ℂ := u (endpoint E r (q w))
  let L (f : (Field dim)) (w : ↥(standardSphere dim)) : ℂ := f (q w) * T w
  let C (i j : (I dim)) : ℂ := (g₂ y)⁻¹ i j
  let Γ (k i j : (I dim)) : ℂ := christoffel g₂ y k i j
  let s : ℂ := (r y : ℂ) * (((dim : ℝ) / ((γ y) * (g₂ y)⁻¹).trace : ℝ) : ℂ)
  have hInt {f : (Field dim)} (hf : smoothNear f (bundle Y γ)) :
      Integrable (L f) (sphereProbability dim) := by
    obtain ⟨S,hS,hSub,hfS⟩ := hf
    apply integrable_frameFiber (V := V) hy (he y hy)
      (smoothNear_mul_fields (τ := fun p => (u (endpoint E r p) : ℂ)) ?_ (smoothNear_ofReal_field hτ))
    exact ⟨S,hS,fun p hp => hSub ⟨hVY hp.1,hp.2⟩,hfS⟩
  have hTerm (i j : (I dim)) : Integrable
      (fun w => C i j * (L (WW i j) w - ∑ k, Γ k i j * L (W k) w)) (sphereProbability dim) :=
    ((hInt (hWW i j)).sub (integrable_finsetSum _ fun k _ => (hInt (hW k)).const_mul _)).const_mul _
  have hEq : sphereTracePair e E r (movingTrace γ g₂ r A φ) u y =
      ∫ w : ↥(standardSphere dim), s * (∑ i, ∑ j, C i j *
        (L (WW i j) w - ∑ k, Γ k i j * L (W k) w)) ∂(sphereProbability dim) := by
    change (∫ w : ↥(standardSphere dim), L (movingTrace γ g₂ r A φ) w ∂(sphereProbability dim)) = _
    apply integral_congr_ae
    filter_upwards with w
    simp only [L,movingTrace_targetConnection,q,C,Γ,s,W,WW,Finset.sum_mul,sub_mul,mul_assoc]
  rw [hEq,integral_const_mul,integral_finsetSum _
    (fun i _ => integrable_finsetSum _ (fun j _ => hTerm i j))]
  suffices hzero : (∑ i, ∫ w : ↥(standardSphere dim), ∑ j, C i j *
        (L (WW i j) w - ∑ k, Γ k i j * L (W k) w) ∂(sphereProbability dim)) = 0 by
    simp [hzero]
  have hRow (i : (I dim)) :
      (∫ w : ↥(standardSphere dim), ∑ j, C i j *
        (L (WW i j) w - ∑ k, Γ k i j * L (W k) w) ∂(sphereProbability dim)) =
      ∑ j, C i j * ((↑(coordDeriv (E := ℝ) i (coordDeriv j F) y) : ℂ) -
        ∑ k, Γ k i j * (↑(coordDeriv (E := ℝ) k F y) : ℂ)) := by
    rw [integral_finsetSum _ (fun j _ => hTerm i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul,integral_sub (hInt (hWW i j))
      (integrable_finsetSum _ (fun k _ => (hInt (hW k)).const_mul _)),
      integral_finsetSum _ (fun k _ => (hInt (hW k)).const_mul _)]
    simp_rw [integral_const_mul]
    exact congrArg (fun v => C i j * v) (congrArg₂ (· - ·) (hVal2 i j hy)
      (Finset.sum_congr rfl (fun k _ => congrArg (Γ k i j * ·) (hVal1 k hy))))
  have hLap : (↑(laplace g₂ F y) : ℂ) = ∑ i, ∑ j, C i j *
      ((↑(coordDeriv (E := ℝ) i (coordDeriv j F) y) : ℂ) -
        ∑ k, Γ k i j * (↑(coordDeriv (E := ℝ) k F y) : ℂ)) := by
    simp only [laplace,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_sub]
    rfl
  simp_rw [hRow]
  rw [← hLap,hF.2 y hy,Complex.ofReal_zero]

private theorem smoothNear_finsetSum_fields {ι : Type*} (s : Finset ι)
    {Y : Set (X dim)} {γ : (MetricField dim)} {f : ι → (Field dim)}
    (hf : ∀ i ∈ s, smoothNear (f i) (bundle Y γ)) :
    smoothNear (fun p => ∑ i ∈ s, f i p) (bundle Y γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using
      (show smoothNear (fun _ : (X dim) × (X dim) => (0 : ℂ)) (bundle Y γ) from
        ⟨univ,isOpen_univ,subset_univ _,contDiffOn_const⟩)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact smoothNear_add_fields (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem smoothNear_sub_fields {V : Set (X dim)} {γ : (MetricField dim)}
    {φ τ : (Field dim)} (hφ : smoothNear φ (bundle V γ)) (hτ : smoothNear τ (bundle V γ)) :
    smoothNear (fun p => φ p - τ p) (bundle V γ) := by
  obtain ⟨S,hSo,hS,hφS⟩ := hφ
  obtain ⟨T,hTo,hT,hτT⟩ := hτ
  exact ⟨S ∩ T,hSo.inter hTo,fun p hp => ⟨hS hp,hT hp⟩,
    (hφS.mono inter_subset_left).sub (hτT.mono inter_subset_right)⟩

theorem smoothNear_movingTrace {Y : Set (X dim)} (hY : IsOpen Y)
    {γ g₁ g₂ : (MetricField dim)} (hγ : SmoothMetric Y γ) (hg₂ : SmoothMetric Y g₂)
    {e : (Frame dim)} {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ} (hr : ContDiffOn ℝ ∞ r Y)
    {A : (TraceAdjoint dim)} (hA : IsMovingTraceAdjoint Y γ g₁ e E r A)
    {φ : (Field dim)} (hφ : smoothNear φ (bundle Y γ)) :
    smoothNear (movingTrace γ g₂ r A φ) (bundle Y γ) := by
  have base {f : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f Y) :
      smoothNear (fun q : (X dim) × (X dim) => (f q.1 : ℂ)) (bundle Y γ) :=
    smoothNear_ofReal_field ⟨Y ×ˢ univ,hY.prod isOpen_univ,
      fun _ hq => ⟨hq.1,mem_univ _⟩,hf.comp contDiffOn_fst (fun _ hq => hq.1)⟩
  have hscale : ContDiffOn ℝ ∞ (fun y => (dim : ℝ) / ((γ y) * (g₂ y)⁻¹).trace) Y := by
    have ht : ContDiffOn ℝ ∞ (fun y => ((γ y) * (g₂ y)⁻¹).trace) Y := by
      simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
      exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
        (hγ.1 i j).mul (contDiffOn_metric_inv_entry hg₂ j i)
    exact contDiffOn_const.div ht (fun y hy =>
      (trace_mul_pos_of_posDef (hγ.2 y hy) (hg₂.2 y hy).inv).ne')
  have hW (j : (I dim)) := smoothNear_traceDerivative hY hγ hA hφ j
  have hWW (i j : (I dim)) := smoothNear_traceDerivative hY hγ hA (hW j) i
  change smoothNear (fun q => movingTrace γ g₂ r A φ q) (bundle Y γ)
  simp_rw [movingTrace_targetConnection]
  refine smoothNear_mul_fields (smoothNear_mul_fields (base hr) (base hscale)) ?_
  refine smoothNear_finsetSum_fields Finset.univ fun i _ =>
    smoothNear_finsetSum_fields Finset.univ fun j _ => ?_
  refine smoothNear_mul_fields (base (contDiffOn_metric_inv_entry hg₂ i j))
    (smoothNear_sub_fields (hWW i j) (smoothNear_finsetSum_fields Finset.univ fun k _ => ?_))
  exact smoothNear_mul_fields (base (contDiffOn_christoffel hY hg₂ k i j)) (hW k)

end CalderonN
