module

public import Proof.CalderonN.SobolevDerivativeBridge
public import Proof.PriorAnalysis.TauCeti.Analysis.Sobolev.Wkp.LocalApproximation

public import Proof.CalderonN.SobolevPointEvaluation
public import Proof.CalderonN.SourceSobolev
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-! The local smooth-representative proof is adapted from
`Calderon/CollaboratorSmoothRepOct17.lean` at
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. Its pointwise estimate
uses one coordinate derivative per ambient dimension. -/

public section

noncomputable section
open MeasureTheory Set TopologicalSpace Metric Filter
open scoped ENNReal ContDiff Topology

namespace CalderonN

variable {d : ℕ}


set_option maxHeartbeats 1400000

theorem norm_iteratedFDeriv_iteratedFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (h : E → F) :
    ∀ (n l : ℕ) (x : E), ‖iteratedFDeriv ℝ l (iteratedFDeriv ℝ n h) x‖ =
      ‖iteratedFDeriv ℝ (l + n) h x‖ := by
  intro n
  induction n with
  | zero =>
    intro l x
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.norm_iteratedFDeriv_comp_left h x l
  | succ n ih =>
    intro l x
    rw [show l + (n + 1) = (l + 1) + n by omega,← ih]
    rw [iteratedFDeriv_succ_eq_comp_left]
    let A := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm
    let D := fderiv ℝ (iteratedFDeriv ℝ n h)
    change ‖iteratedFDeriv ℝ l (A ∘ D) x‖ = _
    rw [← norm_iteratedFDeriv_fderiv]
    change _ = ‖iteratedFDeriv ℝ l D x‖
    let U := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F
    let V := ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => E) F
    let nU : NormedAddCommGroup U := ContinuousLinearMap.toNormedAddCommGroup
    let nV : NormedAddCommGroup V := ContinuousMultilinearMap.normedAddCommGroup
    let AU : @LinearIsometryEquiv ℝ ℝ _ _ (RingHom.id ℝ) (RingHom.id ℝ) _ _ U V
        nU.toSeminormedAddCommGroup nV.toSeminormedAddCommGroup _ _ := A
    have hh := @LinearIsometryEquiv.norm_iteratedFDeriv_comp_left ℝ E U V _ _ _ nU _ nV _ AU D x l
    exact hh

private theorem deriv_bound (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, ∀ (m : ℕ), n + d ≤ m → ∀ (U : Opens (X d))
      (u : TauCeti.Wkp (volume : Measure (X d)) U 2 m) (h : X d → ℝ), ContDiff ℝ ∞ h →
      (TauCeti.Wkp.value m u : X d → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] h →
      ∀ y : X d, ball y r ⊆ U → ‖iteratedFDeriv ℝ n h y‖ ≤ C * ‖u‖ := by
  obtain ⟨C,hC,hBound⟩ := exists_norm_le_ball_L2_of_iterated_bounds d r hr
  refine ⟨C,fun m hm U u h hh hU y hy => ?_⟩
  let f := iteratedFDeriv ℝ n h
  have hf : ContDiff ℝ ∞ f := hh.iteratedFDeriv_right (by simp)
  apply hBound f hf y ‖u‖ (norm_nonneg _)
  intro k hk
  have hLp :
      eLpNorm (iteratedFDeriv ℝ k f) 2 (volume.restrict (ball y r)) ≤ ENNReal.ofReal ‖u‖ := by
    have hEq : eLpNorm (iteratedFDeriv ℝ k f) 2 (volume.restrict (ball y r)) =
        eLpNorm (iteratedFDeriv ℝ (k+n) h) 2 (volume.restrict (ball y r)) :=
      eLpNorm_congr_norm_ae ((hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
        ((hh.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
        (Eventually.of_forall (norm_iteratedFDeriv_iteratedFDeriv h n k))
    rw [hEq]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono hy le_rfl)).trans
      (eLpNorm_iteratedFDeriv_le U m u hh.contDiffOn hU (k+n) (by omega))
  have hMem : MemLp (iteratedFDeriv ℝ k f) 2 (volume.restrict (ball y r)) :=
    lt_of_le_of_lt hLp ENNReal.ofReal_lt_top
  have hSqrt : Real.sqrt (∫ z in ball y r, ‖iteratedFDeriv ℝ k f z‖ ^ 2) ≤ ‖u‖ := by
    rw [sqrt_integral_norm_sq_eq_eLpNorm_toReal hMem]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hLp).trans_eq
      (ENNReal.toReal_ofReal (norm_nonneg _))
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hSqrt 2
  rwa [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] at hp

theorem tendstoUniformlyOn_curryLeft {m : ℕ} {V : Set (X d)}
    {F : ℕ → (X d) → ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => (X d)) ℝ}
    {G : (X d) → ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => (X d)) ℝ}
    (h : TendstoUniformlyOn F G atTop V) :
    TendstoUniformlyOn (fun j x => (F j x).curryLeft) (fun x => (G x).curryLeft) atTop V := by
  let A := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => (X d)) ℝ
  exact A.isometry.uniformContinuous.comp_tendstoUniformlyOn h

theorem limit_contDiffOn {V : Set (X d)} (hV : IsOpen V) (k : ℕ) (φ : ℕ → (X d) → ℝ)
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hC : ∀ n ≤ k, UniformCauchySeqOn (fun j => iteratedFDeriv ℝ n (φ j)) atTop V) :
    ∃ f : (X d) → ℝ, ContDiffOn ℝ k f V ∧ ∀ y ∈ V, Tendsto (fun j => φ j y) atTop (𝓝 (f y)) := by
  let G : (n : ℕ) → (X d) → ContinuousMultilinearMap ℝ (fun _ : Fin n => (X d)) ℝ :=
    fun n y => limUnder atTop (fun j => iteratedFDeriv ℝ n (φ j) y)
  have hT : ∀ n ≤ k, TendstoUniformlyOn (fun j => iteratedFDeriv ℝ n (φ j)) (G n) atTop V :=
    fun n hn => (hC n hn).tendstoUniformlyOn_of_tendsto
      (fun y hy => ((hC n hn).cauchySeq hy).tendsto_limUnder)
  let p : (X d) → FormalMultilinearSeries ℝ (X d) ℝ := fun y n => G n y
  have hser : ∀ j, HasFTaylorSeriesUpTo (⊤ : ℕ∞) (φ j) (ftaylorSeries ℝ (φ j)) :=
    fun j => contDiff_iff_ftaylorSeries.1 (hφ j)
  have hp : HasFTaylorSeriesUpToOn (k : ℕ∞) (fun y => (G 0 y).curry0) p V := by
    refine ⟨fun x _ => rfl, ?_, ?_⟩
    · intro m hm x hx
      have hm' : m < k := by exact_mod_cast hm
      refine (hasFDerivAt_of_tendstoUniformlyOn (l := atTop) hV
        (f := fun j => iteratedFDeriv ℝ m (φ j))
        (f' := fun j x => (iteratedFDeriv ℝ (m + 1) (φ j) x).curryLeft)
        (tendstoUniformlyOn_curryLeft (hT (m + 1) (by omega)))
        (fun j x _ => (hser j).fderiv m (by exact_mod_cast WithTop.coe_lt_top _) x)
        (fun x hx => (hT m hm'.le).tendsto_at hx) hx).hasFDerivWithinAt
    · intro m hm
      have hm' : m ≤ k := by exact_mod_cast hm
      exact (hT m hm').continuousOn (Eventually.of_forall (f := atTop) fun j =>
        ((hφ j).continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).continuousOn).frequently
  refine ⟨_, hp.contDiffOn, fun y hy => ?_⟩
  have h0 := ((continuousMultilinearCurryFin0 ℝ (X d) ℝ).continuous.tendsto (G 0 y)).comp
    ((hT 0 (by omega)).tendsto_at hy)
  refine h0.congr fun j => ?_
  simp [Function.comp]

open scoped Distributions in
theorem local_order (w : (X d) → ℝ) (x : (X d)) (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ)
    (W : TauCeti.Wkp (volume : Measure (X d)) (⟨ball x ρ, isOpen_ball⟩ : Opens (X d)) 2 (k + d))
    (hW : ⇑(TauCeti.Wkp.value (k + d) W) =ᵐ[(volume : Measure (X d)).restrict (ball x ρ)] w) :
    ∃ f : (X d) → ℝ, ContDiffOn ℝ k f (ball x (ρ / 4)) ∧
      f =ᵐ[(volume : Measure (X d)).restrict (ball x (ρ / 4))] w := by
  let Ω : Opens (X d) := ⟨ball x ρ, isOpen_ball⟩
  let U : Opens (X d) := ⟨ball x (ρ / 2), isOpen_ball⟩
  have hcl : closure (U : Set (X d)) = closedBall x (ρ / 2) := closure_ball x (by positivity)
  have hcompact : IsCompact (closure (U : Set (X d))) := by
    rw [hcl]; exact isCompact_closedBall x _
  have hclosure : closure (U : Set (X d)) ⊆ Ω := by
    rw [hcl]; exact closedBall_subset_ball (by linarith)
  have hUO : U ≤ Ω := SetLike.coe_subset_coe.mp (subset_closure.trans hclosure)
  obtain ⟨ψ, hψ⟩ := TauCeti.Wkp.exists_testFunction_approximation_restrictL
    (mu := (volume : Measure (X d))) (p := 2) (by norm_num) hcompact hclosure (k + d) W
  let u : ℕ → TauCeti.Wkp (volume : Measure (X d)) U 2 (k + d) := fun j =>
    TauCeti.Wkp.restrictL hUO (k + d)
      (TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure (X d))) (p := 2) (k + d) (ψ j))
  have hu : Tendsto u atTop (𝓝 (TauCeti.Wkp.restrictL hUO (k + d) W)) := hψ
  have hψs : ∀ j, ContDiff ℝ ∞ (ψ j : (X d) → ℝ) := fun j => (ψ j).contDiff
  have hval : ∀ j, (TauCeti.Wkp.value (k + d) (u j) : (X d) → ℝ)
      =ᵐ[(volume : Measure (X d)).restrict U] (ψ j : (X d) → ℝ) := by
    intro j
    refine (TauCeti.Wkp.value_restrictL_ae hUO (k + d) _).trans ?_
    rw [TauCeti.Wkp.value_ofTestFunctionₗ]
    exact ae_restrict_of_ae_restrict_of_subset (show (U : Set (X d)) ⊆ Ω from hUO)
      (TauCeti.testFunctionLp_apply_ae 2 (ψ j))
  have hsub : ∀ y ∈ ball x (ρ / 4), ball y (ρ / 4) ⊆ (U : Set (X d)) := by
    intro y hy z hz
    show z ∈ ball x (ρ / 2)
    rw [mem_ball] at hy hz ⊢
    linarith [dist_triangle z y x]
  have hC : ∀ n ≤ k, UniformCauchySeqOn (fun j => iteratedFDeriv ℝ n (ψ j : (X d) → ℝ)) atTop
      (ball x (ρ / 4)) := by
    intro n hn
    obtain ⟨C, hCb⟩ := deriv_bound (d := d) n (ρ / 4) (by positivity)
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq (ε / (|C| + 1)) (by positivity)
    refine ⟨N, fun a ha b hb y hy => ?_⟩
    have hd : (TauCeti.Wkp.value (k + d) (u a - u b) : (X d) → ℝ)
        =ᵐ[(volume : Measure (X d)).restrict U] (⇑(ψ a) - ⇑(ψ b)) := by
      rw [← TauCeti.Wkp.valueL_apply, map_sub, TauCeti.Wkp.valueL_apply,
        TauCeti.Wkp.valueL_apply]
      filter_upwards [Lp.coeFn_sub (TauCeti.Wkp.value (k + d) (u a))
        (TauCeti.Wkp.value (k + d) (u b)), hval a, hval b] with z hz ha hb
      rw [hz, Pi.sub_apply, ha, hb, Pi.sub_apply]
    have hb' := hCb (k + d) (by omega) U (u a - u b) (⇑(ψ a) - ⇑(ψ b))
      ((hψs a).sub (hψs b)) hd y (hsub y hy)
    rw [iteratedFDeriv_sub_apply ((hψs a).contDiffAt.of_le (by exact_mod_cast le_top))
      ((hψs b).contDiffAt.of_le (by exact_mod_cast le_top))] at hb'
    rw [dist_eq_norm]
    have h1 : ‖u a - u b‖ < ε / (|C| + 1) := by rw [← dist_eq_norm]; exact hN a ha b hb
    calc _ ≤ C * ‖u a - u b‖ := hb'
      _ ≤ |C| * ‖u a - u b‖ := by gcongr; exact le_abs_self C
      _ ≤ |C| * (ε / (|C| + 1)) := by gcongr
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]
  obtain ⟨f, hf, hlim⟩ := limit_contDiffOn isOpen_ball k (fun j => (ψ j : (X d) → ℝ)) hψs hC
  refine ⟨f, hf, ?_⟩
  have hvL : Tendsto (fun j => TauCeti.Wkp.value (k + d) (u j)) atTop
      (𝓝 (TauCeti.Wkp.value (k + d) (TauCeti.Wkp.restrictL hUO (k + d) W))) := by
    simp only [← TauCeti.Wkp.valueL_apply]
    exact ((TauCeti.Wkp.valueL (k + d)).continuous.tendsto _).comp hu
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvL).exists_seq_tendsto_ae
  have hall : ∀ᵐ z ∂(volume : Measure (X d)).restrict U,
      ∀ j, (TauCeti.Wkp.value (k + d) (u j) : (X d) → ℝ) z = ψ j z := ae_all_iff.2 hval
  have hWU : (TauCeti.Wkp.value (k + d) (TauCeti.Wkp.restrictL hUO (k + d) W) : (X d) → ℝ)
      =ᵐ[(volume : Measure (X d)).restrict U] w :=
    (TauCeti.Wkp.value_restrictL_ae hUO (k + d) W).trans
      (ae_restrict_of_ae_restrict_of_subset (show (U : Set (X d)) ⊆ Ω from hUO) hW)
  have hVU : ball x (ρ / 4) ⊆ (U : Set (X d)) := ball_subset_ball (by linarith)
  have hres := ae_restrict_of_ae_restrict_of_subset hVU (hae.and (hall.and hWU))
  filter_upwards [hres, ae_restrict_mem measurableSet_ball] with z hz hzV
  obtain ⟨h1, h2, h3⟩ := hz
  have h4 : Tendsto (fun i => ψ (ns i) z) atTop (𝓝 (w z)) := by
    rw [← h3]; exact h1.congr fun i => h2 (ns i)
  exact tendsto_nhds_unique ((hlim z hzV).comp hns.tendsto_atTop) h4

theorem local_smooth (w : (X d) → ℝ) (x : (X d)) (ρ : ℝ) (hρ : 0 < ρ)
    (hW : ∀ k : ℕ,
      ∃ W : TauCeti.Wkp (volume : Measure (X d)) (⟨ball x ρ, isOpen_ball⟩ : Opens (X d)) 2 k,
        ⇑(TauCeti.Wkp.value k W) =ᵐ[(volume : Measure (X d)).restrict (ball x ρ)] w) :
    ∃ f : (X d) → ℝ, ContDiffOn ℝ ∞ f (ball x (ρ / 4)) ∧
      f =ᵐ[(volume : Measure (X d)).restrict (ball x (ρ / 4))] w := by
  have h : ∀ k : ℕ, ∃ f : (X d) → ℝ, ContDiffOn ℝ k f (ball x (ρ / 4)) ∧
      f =ᵐ[(volume : Measure (X d)).restrict (ball x (ρ / 4))] w := by
    intro k
    obtain ⟨W, hW'⟩ := hW (k + d)
    exact local_order w x ρ hρ k W hW'
  choose f hf hfw using h
  refine ⟨f 0, contDiffOn_infty.2 fun k => ?_, hfw 0⟩
  have heq : Set.EqOn (f k) (f 0) (ball x (ρ / 4)) :=
    Measure.eqOn_open_of_ae_eq ((hfw k).trans (hfw 0).symm) isOpen_ball
      (hf k).continuousOn (hf 0).continuousOn
  exact (hf k).congr fun y hy => (heq hy).symm


open TauCeti
open Filter Topology

/-- A function that is locally in every `W^{k,2}` has a smooth representative. -/
theorem exists_contDiffOn_ae_eq {O : Set (X d)} (_hO : IsOpen O) {w : (X d) → ℝ}
    (hloc : ∀ x ∈ O, ∃ ρ > 0, ball x ρ ⊆ O ∧ ∀ k : ℕ,
      ∃ W : Wkp (volume : Measure (X d)) (⟨ball x ρ, isOpen_ball⟩ : Opens (X d)) 2 k,
        ⇑(Wkp.value k W) =ᵐ[(volume : Measure (X d)).restrict (ball x ρ)] w) :
    ∃ w' : (X d) → ℝ, ContDiffOn ℝ ∞ w' O ∧ w' =ᵐ[(volume : Measure (X d)).restrict O] w := by
  have hloc' : ∀ x ∈ O, ∃ r > 0, ball x r ⊆ O ∧ ∃ f : (X d) → ℝ, ContDiffOn ℝ ∞ f (ball x r) ∧
      f =ᵐ[(volume : Measure (X d)).restrict (ball x r)] w := by
    intro x hx
    obtain ⟨ρ, hρ, hρO, hW⟩ := hloc x hx
    exact ⟨ρ / 4, by positivity, (ball_subset_ball (by linarith)).trans hρO,
      local_smooth w x ρ hρ hW⟩
  choose r hr hrO f hf hfw using hloc'
  classical
  let w' : (X d) → ℝ := fun y => if hy : y ∈ O then f y hy y else 0
  have key : ∀ z (hz : z ∈ O), ∀ y ∈ ball z (r z hz), w' y = f z hz y := by
    intro z hz y hy
    have hyO : y ∈ O := hrO z hz hy
    have hw' : w' y = f y hyO y := by simp [w', hyO]
    rw [hw']
    let S := ball z (r z hz) ∩ ball y (r y hyO)
    have hS : IsOpen S := isOpen_ball.inter isOpen_ball
    have hyS : y ∈ S := ⟨hy, mem_ball_self (hr y hyO)⟩
    have e1 : f z hz =ᵐ[(volume : Measure (X d)).restrict S] w :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hfw z hz)
    have e2 : f y hyO =ᵐ[(volume : Measure (X d)).restrict S] w :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hfw y hyO)
    exact (Measure.eqOn_open_of_ae_eq (e2.trans e1.symm) hS
      ((hf y hyO).continuousOn.mono Set.inter_subset_right)
      ((hf z hz).continuousOn.mono Set.inter_subset_left) hyS)
  refine ⟨w', fun z hz => ?_, ?_⟩
  · have hev : w' =ᶠ[𝓝 z] f z hz :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self (hr z hz))) (key z hz)
    exact (((hf z hz).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (hr z hz)))).congr_of_eventuallyEq
      hev).contDiffWithinAt
  · obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : O => ball (i : (X d)) (r i i.2)) (fun i => isOpen_ball)
    have hO' : O = ⋃ i ∈ T, ball (i : (X d)) (r i i.2) := by
      rw [hTU]
      ext y
      simp only [Set.mem_iUnion]
      exact ⟨fun hy => ⟨⟨y, hy⟩, mem_ball_self (hr y hy)⟩,
        fun ⟨i, hi⟩ => hrO i i.2 hi⟩
    rw [hO', Filter.EventuallyEq, ae_restrict_biUnion_iff _ hT]
    intro i _
    filter_upwards [hfw i i.2, ae_restrict_mem measurableSet_ball] with y hy hyb
    rw [key i i.2 y hyb, hy]


end CalderonN
