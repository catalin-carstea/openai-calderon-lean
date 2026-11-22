module

public import Proof.Manuscript.MovingTraceSymbols
import Proof.Manuscript.MovingTrace.ParameterIntegralJets
import Proof.Manuscript.MovingTrace.OscillatoryPhaseJets
import Proof.CalderonN.LocalMixedParameterJetCalculus
import Proof.CalderonN.TaylorJetCalculus
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

public section

noncomputable section
set_option maxHeartbeats 2300000
set_option synthInstance.maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory CalderonN
open scoped ContDiff Topology RealInnerProductSpace

namespace CalderonPaper

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {dim : ℕ}

/-- Rapid decay in frequency of every geometry and output-coordinate jet,
locally uniformly in the geometry parameters. -/
@[expose] def RapidAngularSymbol (U : Set P) (a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ) ∧
  ∀ J : Set P, IsCompact J → J ⊆ U → ∀ k N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ p ∈ J, ∀ x ξ, ‖iteratedFDeriv ℝ k (fun q => a q ξ) (p,x)‖ ≤
      C * (1 + ‖ξ‖) ^ (-(N : ℝ))

/-- Inverse Fourier transform of the left symbol in the difference of
its output and input angular coordinates. -/
@[expose] def rapidAngularFourierKernel (a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ) (q : P × (AngularCoordinates dim × AngularCoordinates dim)) : ℂ :=
  ∫ ξ, angularFourierPhase (q.2.1 - q.2.2) ξ * a (q.1,q.2.1) ξ

private def angularProjection : P × (AngularCoordinates dim × AngularCoordinates dim) →L[ℝ] P × AngularCoordinates dim :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

omit [FiniteDimensional ℝ P] in
private theorem norm_angularProjection :
    ‖(angularProjection : P × (AngularCoordinates dim × AngularCoordinates dim) →L[ℝ] P × AngularCoordinates dim)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  rw [one_mul, norm_prod_le_iff]
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _)⟩

private theorem angularProjection_jet_le {U : Set P} (hU : IsOpen U)
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ} (ha : RapidAngularSymbol U a) (ξ : AngularCoordinates dim)
    (q : P × (AngularCoordinates dim × AngularCoordinates dim)) (hq : q.1 ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q => a (q.1,q.2.1) ξ) q‖ ≤
      ‖iteratedFDeriv ℝ k (fun q => a q ξ) (q.1,q.2.1)‖ := by
  let L : P × (AngularCoordinates dim × AngularCoordinates dim) →L[ℝ] P × AngularCoordinates dim := angularProjection
  have hS : IsOpen (U ×ˢ (univ : Set (AngularCoordinates dim))) := hU.prod isOpen_univ
  have hA : ContDiffOn ℝ ∞ (fun q => a q ξ) (U ×ˢ univ) :=
    ha.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hq => ⟨hq,mem_univ _⟩)
  obtain ⟨g,hg,he⟩ := exists_global_smooth_germ_of_open (fun q => a q ξ) hS hA
    (show L q ∈ U ×ˢ univ from ⟨hq,mem_univ _⟩)
  have hqg := (he.comp_tendsto L.continuous.continuousAt).iteratedFDeriv ℝ k
  change ‖iteratedFDeriv ℝ k ((fun q => a q ξ) ∘ L) q‖ ≤
    ‖iteratedFDeriv ℝ k (fun q => a q ξ) (L q)‖
  rw [← hqg.eq_of_nhds, L.iteratedFDeriv_comp_right hg q (by simp),
    (he.iteratedFDeriv ℝ k).eq_of_nhds]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  exact mul_le_of_le_one_right (norm_nonneg _) (by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (pow_le_one₀ (norm_nonneg L) (norm_angularProjection (P := P) (dim := dim)) :
        ‖L‖ ^ k ≤ 1))

private def angularDifference : P × (AngularCoordinates dim × AngularCoordinates dim) →L[ℝ] AngularCoordinates dim :=
  ((ContinuousLinearMap.fst ℝ (AngularCoordinates dim) (AngularCoordinates dim)) - (ContinuousLinearMap.snd ℝ (AngularCoordinates dim) (AngularCoordinates dim))).comp
    (ContinuousLinearMap.snd ℝ _ _)

private def angularPhaseLinear (ξ : AngularCoordinates dim) : P × (AngularCoordinates dim × AngularCoordinates dim) →L[ℝ] ℝ :=
  (2 * Real.pi) • (innerSL ℝ ξ).comp angularDifference

omit [FiniteDimensional ℝ P] in
private theorem angularPhaseLinear_apply (ξ : AngularCoordinates dim) (q : P × (AngularCoordinates dim × AngularCoordinates dim)) :
    angularPhaseLinear ξ q = 2 * Real.pi * inner ℝ (q.2.1 - q.2.2) ξ := by
  change 2 * Real.pi * inner ℝ ξ (q.2.1 - q.2.2) = _
  rw [real_inner_comm]

omit [FiniteDimensional ℝ P] in
private theorem norm_angularPhaseLinear (ξ : AngularCoordinates dim) :
    ‖(angularPhaseLinear ξ : P × (AngularCoordinates dim × AngularCoordinates dim) →L[ℝ] ℝ)‖ ≤
      (1 + 4 * Real.pi) * (1 + ‖ξ‖) := by
  have hπ := Real.pi_pos
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun q => ?_
  have hq₁ : ‖q.2.1‖ ≤ ‖q‖ := (le_max_left _ _).trans (le_max_right _ _)
  have hq₂ : ‖q.2.2‖ ≤ ‖q‖ := (le_max_right _ _).trans (le_max_right _ _)
  have hd : ‖q.2.1-q.2.2‖ ≤ 2 * ‖q‖ := (norm_sub_le _ _).trans (by linarith)
  rw [angularPhaseLinear_apply, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
  calc
    _ ≤ (2*Real.pi) * ((2*‖q‖)*‖ξ‖) := by
      gcongr
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
    _ ≤ _ := by
      have hb : 4*Real.pi*‖ξ‖ ≤ (1+4*Real.pi)*(1+‖ξ‖) := by
        nlinarith only [hπ, norm_nonneg ξ]
      convert mul_le_mul_of_nonneg_right hb (norm_nonneg q) using 1 <;> ring

private def phaseJetConstant (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * oscillatoryPhaseJetBound * (1 + 4 * Real.pi) ^ n

private theorem phaseJetConstant_nonneg (n : ℕ) : 0 ≤ phaseJetConstant n := by
  have := oscillatoryPhaseJetBound_nonneg
  have := Real.pi_pos
  unfold phaseJetConstant
  positivity

private theorem angularPhase_jet_le (ξ : AngularCoordinates dim) (q : P × (AngularCoordinates dim × AngularCoordinates dim))
    {n j : ℕ} (hj : j ≤ n) :
    ‖iteratedFDeriv ℝ j (fun q => angularFourierPhase (q.2.1-q.2.2) ξ) q‖ ≤
      phaseJetConstant n * (1 + ‖ξ‖) ^ (n : ℝ) := by
  let L : P × (AngularCoordinates dim × AngularCoordinates dim) →L[ℝ] ℝ := angularPhaseLinear ξ
  let A := (1 + 4 * Real.pi) * (1 + ‖ξ‖)
  have hp := Real.pi_pos
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le (by linarith) (le_add_of_nonneg_right (norm_nonneg ξ))
  have hL (i : ℕ) (hi : 1 ≤ i) (_ : i ≤ n) :
      ‖iteratedFDeriv ℝ i L q‖ ≤ A := by
    rcases i with _ | _ | i
    · omega
    · rw [norm_iteratedFDeriv_one, L.fderiv]
      exact norm_angularPhaseLinear ξ
    · have he : (fun y => fderiv ℝ L y) = fun _ => L := funext (fun _ => L.fderiv)
      simp only [Nat.succ_eq_add_one, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        he, iteratedFDeriv_succ_const, Pi.zero_apply, LinearIsometryEquiv.map_zero, norm_zero]
      exact zero_le_one.trans hA
  have h := norm_iteratedFDeriv_oscillatoryPhase_le L.contDiff.contDiffAt hA n hL
    (h := 1) zero_lt_one le_rfl j hj
  have he : (fun y : P × (AngularCoordinates dim × AngularCoordinates dim) =>
      Complex.exp (Complex.I * ((L y / 1 : ℝ) : ℂ))) =
      fun y => angularFourierPhase (y.2.1-y.2.2) ξ := by
    funext y
    simp only [div_one,L,angularPhaseLinear_apply,angularFourierPhase]
    rw [mul_comm]
  rw [he] at h
  simpa only [inv_one,one_pow,mul_one,A,mul_pow,Real.rpow_natCast,phaseJetConstant,mul_assoc]
    using h

private theorem joint_left_jets {Q S : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    {O : Set Q} (hO : IsOpen O) {f : Q × S → ℂ}
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ univ)) (n : ℕ) :
    ContDiffOn ℝ ∞ (fun q => iteratedFDeriv ℝ n (fun x => f (x,q.2)) q.1) (O ×ˢ univ) := by
  let L := ContinuousLinearMap.inl ℝ Q S
  let R : ContinuousMultilinearMap ℝ (fun _ : Fin n => Q × S) ℂ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Q) ℂ :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin n => L)
  have hU : IsOpen (O ×ˢ (univ : Set S)) := hO.prod isOpen_univ
  have hR : ContDiffOn ℝ ∞ (fun q => R (iteratedFDeriv ℝ n f q)) (O ×ˢ univ) :=
    R.contDiff.comp_contDiffOn (contDiffOn_iteratedFDeriv_top hf hU n)
  apply hR.congr
  intro q hq
  obtain ⟨g,hg,he⟩ := exists_global_smooth_germ_of_open f hU hf hq
  have heg := (he.iteratedFDeriv ℝ n).eq_of_nhds
  have hs : (fun a => g (a,q.2)) =ᶠ[𝓝 q.1] (fun a => f (a,q.2)) :=
    he.comp_tendsto ((continuous_id.prodMk continuous_const).continuousAt)
  have hT : ContDiff ℝ ∞ (fun z : Q × S => g ((0,q.2)+z)) :=
    hg.comp (contDiff_const.add contDiff_id)
  have hEq : (fun a => g (a,q.2)) = (fun z => g ((0,q.2)+z)) ∘ L := by
    funext b
    simp [L]
  change iteratedFDeriv ℝ n (fun a => f (a,q.2)) q.1 = _
  rw [← (hs.iteratedFDeriv ℝ n).eq_of_nhds, hEq, L.iteratedFDeriv_comp_right hT _ (by simp),
    iteratedFDeriv_comp_add_left]
  simpa [R,L] using congrArg R heg

private theorem contDiff_angularFourierPhase {Q : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {x ξ : Q → AngularCoordinates dim}
    (hx : ContDiff ℝ ∞ x) (hξ : ContDiff ℝ ∞ ξ) :
    ContDiff ℝ ∞ (fun q => angularFourierPhase (x q) (ξ q)) := by
  have h := (contDiff_const (c := 2*Real.pi)).mul (hx.inner ℝ hξ)
  have hexp : ContDiff ℂ ∞ Complex.exp := Complex.contDiff_exp
  have hexpR : ContDiff ℝ ∞ Complex.exp := hexp.restrict_scalars (𝕜 := ℝ)
  exact hexpR.comp ((Complex.ofRealCLM.contDiff.comp h).mul contDiff_const)

local notation "KernelParameter" => (P × (AngularCoordinates dim × AngularCoordinates dim))

private def angularFourierIntegrand (a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ)
    (q : KernelParameter) (ξ : AngularCoordinates dim) : ℂ :=
  angularFourierPhase (q.2.1-q.2.2) ξ * a (q.1,q.2.1) ξ

omit [FiniteDimensional ℝ P] in
private theorem contDiffOn_angularFourierIntegrand {U : Set P}
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ} (ha : RapidAngularSymbol U a) :
    ContDiffOn ℝ ∞ (Function.uncurry (angularFourierIntegrand a)) ((U ×ˢ univ) ×ˢ univ) := by
  apply ContDiffOn.mul
  · exact (contDiff_angularFourierPhase
      (contDiff_fst.snd.fst.sub contDiff_fst.snd.snd) contDiff_snd).contDiffOn
  · exact ha.1.comp (show ContDiff ℝ ∞ (fun s : KernelParameter × AngularCoordinates dim =>
      ((s.1.1,s.1.2.1),s.2)) from
        (contDiff_fst.fst.prodMk contDiff_fst.snd.fst).prodMk contDiff_snd).contDiffOn
      (fun _ hs => ⟨⟨hs.1.1,mem_univ _⟩,mem_univ _⟩)

omit [FiniteDimensional ℝ P] in
private theorem contDiffOn_angularFourierIntegrand_slice {U : Set P}
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ} (ha : RapidAngularSymbol U a) (ξ : AngularCoordinates dim) :
    ContDiffOn ℝ ∞ (fun q => angularFourierIntegrand a q ξ) (U ×ˢ univ) := by
  have hp : ContDiff ℝ ∞ (fun q : KernelParameter => angularFourierPhase (q.2.1-q.2.2) ξ) :=
    contDiff_angularFourierPhase (contDiff_snd.fst.sub contDiff_snd.snd) contDiff_const
  have ha' : ContDiffOn ℝ ∞ (fun q : KernelParameter => a (q.1,q.2.1) ξ) (U ×ˢ univ) :=
    ha.1.comp (show ContDiff ℝ ∞ (fun q : KernelParameter => ((q.1,q.2.1),ξ)) from
      (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_const).contDiffOn
      (fun _ hx => ⟨⟨hx.1,mem_univ _⟩,mem_univ _⟩)
  exact hp.contDiffOn.mul ha'

private theorem continuous_angularFourierIntegrand_left_jet {U : Set P} (hU : IsOpen U)
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ} (ha : RapidAngularSymbol U a)
    (q : KernelParameter) (hq : q.1 ∈ U) (k : ℕ) :
    Continuous (fun ξ => iteratedFDeriv ℝ k (fun q => angularFourierIntegrand a q ξ) q) := by
  let O : Set (KernelParameter) := U ×ˢ univ
  have hO : IsOpen O := hU.prod isOpen_univ
  have hJoint : ContDiffOn ℝ ∞ (Function.uncurry (angularFourierIntegrand a))
      (O ×ˢ (univ : Set (AngularCoordinates dim))) := contDiffOn_angularFourierIntegrand ha
  let D (v : KernelParameter × AngularCoordinates dim) :=
    iteratedFDeriv ℝ k (fun q => angularFourierIntegrand a q v.2) v.1
  have hD : ContDiffOn ℝ ∞ D (O ×ˢ univ) := joint_left_jets hO hJoint k
  let g (ξ : AngularCoordinates dim) := (q,ξ)
  have hg : Continuous g := continuous_const.prodMk continuous_id
  have hgmap (ξ : AngularCoordinates dim) : g ξ ∈ O ×ˢ univ := ⟨⟨hq,mem_univ _⟩,mem_univ _⟩
  change Continuous (D ∘ g)
  exact hD.continuousOn.comp_continuous hg hgmap

private theorem angularFourierIntegrand_jet_le
    {U H : Set P} (hU : IsOpen U) (hHU : H ⊆ U)
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ} (ha : RapidAngularSymbol U a) (C : ℕ → ℕ → ℝ)
    (hC : ∀ k N p, p ∈ H → ∀ x ξ,
      ‖iteratedFDeriv ℝ k (fun q => a q ξ) (p,x)‖ ≤ C k N * (1 + ‖ξ‖) ^ (-(N : ℝ)))
    (n d : ℕ) (q : KernelParameter) (hq : q.1 ∈ H) (ξ : AngularCoordinates dim) :
    ‖iteratedFDeriv ℝ n (fun q => angularFourierIntegrand a q ξ) q‖ ≤
      (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * phaseJetConstant n * C (n-i) (n+d)) *
        (1 + ‖ξ‖) ^ (-(d : ℝ)) := by
  let O : Set (KernelParameter) := U ×ˢ univ
  have hO : IsOpen O := hU.prod isOpen_univ
  have hqO : q ∈ O := ⟨hHU hq,mem_univ _⟩
  have hp : ContDiff ℝ ∞ (fun q : KernelParameter => angularFourierPhase (q.2.1-q.2.2) ξ) :=
    contDiff_angularFourierPhase (contDiff_snd.fst.sub contDiff_snd.snd) contDiff_const
  have ha' : ContDiffOn ℝ ∞ (fun q : KernelParameter => a (q.1,q.2.1) ξ) O :=
    ha.1.comp (show ContDiff ℝ ∞ (fun q : KernelParameter => ((q.1,q.2.1),ξ)) from
      (contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_const).contDiffOn
      (fun _ hx => ⟨⟨hx.1,mem_univ _⟩,mem_univ _⟩)
  have hMul := norm_iteratedFDerivWithin_mul_le hp.contDiffOn ha' hO.uniqueDiffOn hqO
    (n := n) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hqO] at hMul
  refine hMul.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := by simpa using hi
  have hP := angularPhase_jet_le ξ q hi'
  have hA := (angularProjection_jet_le hU ha ξ q (hHU hq) (n-i)).trans
      (hC (n-i) (n+d) q.1 hq q.2.1 ξ)
  calc
    _ ≤ (n.choose i : ℝ) * (phaseJetConstant n * (1+‖ξ‖) ^ (n : ℝ)) *
        (C (n-i) (n+d) * (1+‖ξ‖) ^ (-((n+d : ℕ) : ℝ))) := by
      have hchoose : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
      have hphase : 0 ≤ phaseJetConstant n * (1+‖ξ‖) ^ (n : ℝ) :=
        mul_nonneg (phaseJetConstant_nonneg n) (Real.rpow_nonneg (by positivity) _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hP hchoose) hA (norm_nonneg _)
        (mul_nonneg hchoose hphase)
    _ = _ := by
      have hpow : (1+‖ξ‖) ^ (n : ℝ) * (1+‖ξ‖) ^ (-((n+d : ℕ) : ℝ)) =
          (1+‖ξ‖) ^ (-(d : ℝ)) := by
        rw [← Real.rpow_add (by positivity), Nat.cast_add]
        congr 1
        ring
      rw [← hpow]
      ring

/-- A rapid symbol gives a jointly smooth kernel. Control of geometry jets
is needed only locally uniformly in the open geometry domain. -/
theorem contDiffOn_rapidAngularFourierKernel {U : Set P} (hU : IsOpen U)
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ} (ha : RapidAngularSymbol U a) :
    ContDiffOn ℝ ∞ (rapidAngularFourierKernel a) (U ×ˢ univ) := by
  let f := angularFourierIntegrand a
  intro q hq
  obtain ⟨ε,hε,hεK⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hq.1)
  let H := Metric.closedBall q.1 (ε/2)
  have hH : IsCompact H := isCompact_closedBall _ _
  have hHU : H ⊆ U := fun x hx => hεK (Metric.closedBall_subset_ball (by linarith) hx)
  let O : Set (KernelParameter) := interior H ×ˢ univ
  have hO : IsOpen O := isOpen_interior.prod isOpen_univ
  have hOU : O ⊆ U ×ˢ univ := fun _ h => ⟨hHU (interior_subset h.1),h.2⟩
  have hqO : q ∈ O :=
    ⟨mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ (by positivity)),mem_univ _⟩
  have hF (ξ : AngularCoordinates dim) : ContDiffOn ℝ ∞ (fun q => f q ξ) O :=
    (contDiffOn_angularFourierIntegrand_slice ha ξ).mono hOU
  have hMeas (q : KernelParameter) (hq : q ∈ O) (k : ℕ) :
      AEStronglyMeasurable (fun ξ => iteratedFDeriv ℝ k (fun q => f q ξ) q) volume := by
    letI : SecondCountableTopologyEither (AngularCoordinates dim) (KernelParameter [×k]→L[ℝ] ℂ) :=
      secondCountableTopologyEither_of_left _ _
    exact (continuous_angularFourierIntegrand_left_jet hU ha q (hOU hq).1 k).aestronglyMeasurable
  let d := Module.finrank ℝ (AngularCoordinates dim) + 1
  choose C _hCpos hC using ha.2 H hH hHU
  let c (n : ℕ) := ∑ i ∈ Finset.range (n+1),
    (n.choose i : ℝ) * phaseJetConstant n * C (n-i) (n+d)
  let B (n : ℕ) (ξ : AngularCoordinates dim) := c n * (1 + ‖ξ‖) ^ (-(d : ℝ))
  have hB (n : ℕ) : Integrable (B n) := by
    exact (integrable_one_add_norm (E := AngularCoordinates dim) (r := d) (by norm_cast; exact Nat.lt_succ_self _)).const_mul (c n)
  have hBounds (q : KernelParameter) (hq : q ∈ O) (ξ : AngularCoordinates dim) (n : ℕ) :
      ‖iteratedFDeriv ℝ n (fun q => f q ξ) q‖ ≤ B n ξ :=
    angularFourierIntegrand_jet_le hU hHU ha C hC n d q (interior_subset hq.1) ξ
  have hInt : ContDiffOn ℝ ∞ (fun q => ∫ ξ, f q ξ) O :=
    (parameterIntegral_iteratedFDeriv (μ := volume) hO f hF hMeas
      B hB hBounds).1
  exact (hInt.contDiffAt (hO.mem_nhds hqO)).contDiffWithinAt

private theorem norm_angularFourierPhase (x ξ : AngularCoordinates dim) : ‖angularFourierPhase x ξ‖ = 1 := by
  simp [angularFourierPhase,Complex.norm_exp]

private theorem angularFourierPhase_sub (x z ξ : AngularCoordinates dim) :
    angularFourierPhase (x-z) ξ = angularFourierPhase x ξ * angularFourierPhase (-z) ξ := by
  unfold angularFourierPhase
  rw [← Complex.exp_add,inner_sub_left,inner_neg_left]
  push_cast
  congr 1
  ring

omit [FiniteDimensional ℝ P] in
/-- Exact Fubini identity for the Fourier quantization of a rapid symbol
against a continuous integrable datum. -/
theorem rapidAngularFourierKernel_quantization {U : Set P} {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (ha : RapidAngularSymbol U a) {p : P} (hp : p ∈ U)
    (x : AngularCoordinates dim) {f : AngularCoordinates dim → ℂ} (hf : Continuous f) (hfi : Integrable f) :
    (∫ ξ, angularFourierPhase x ξ * a (p,x) ξ * angularFourierTransform f ξ) =
      ∫ z, rapidAngularFourierKernel a (p,(x,z)) * f z := by
  let d := Module.finrank ℝ (AngularCoordinates dim) + 1
  obtain ⟨C,hC,hBound⟩ := ha.2 {p} isCompact_singleton (singleton_subset_iff.mpr hp) 0 d
  have hA : Continuous (a (p,x)) := continuousOn_univ.mp
    (ha.1.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun ξ _ => ⟨⟨hp,mem_univ _⟩,mem_univ ξ⟩))
  have hAi : Integrable (a (p,x)) := by
    refine ((integrable_one_add_norm (E := AngularCoordinates dim) (r := d) (by norm_cast; exact Nat.lt_succ_self _)).const_mul C).mono'
      hA.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    simpa only [norm_iteratedFDeriv_zero] using hBound p (mem_singleton _) x ξ
  let F (ξ z : AngularCoordinates dim) := angularFourierPhase (x-z) ξ * a (p,x) ξ * f z
  have hF : Integrable (Function.uncurry F) ((volume : Measure (AngularCoordinates dim)).prod volume) := by
    have hphase : ContDiff ℝ ∞ (fun q : AngularCoordinates dim × AngularCoordinates dim => angularFourierPhase (x-q.2) q.1) :=
      contDiff_angularFourierPhase (contDiff_const.sub contDiff_snd) contDiff_fst
    have hc : Continuous (Function.uncurry F) :=
      (hphase.continuous.mul (hA.comp continuous_fst)).mul (hf.comp continuous_snd)
    refine (hAi.norm.mul_prod hfi.norm).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    simp [Function.uncurry, F, norm_angularFourierPhase]
  calc
    _ = ∫ ξ, ∫ z, F ξ z := by
      apply integral_congr_ae
      refine Eventually.of_forall fun ξ => ?_
      change angularFourierPhase x ξ * a (p,x) ξ *
        (∫ z, angularFourierPhase (-z) ξ * f z) = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change _ = angularFourierPhase (x-z) ξ * a (p,x) ξ * f z
        rw [angularFourierPhase_sub]
        ring
    _ = ∫ z, ∫ ξ, F ξ z := integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change (∫ ξ, F ξ z) = (∫ ξ, angularFourierPhase (x-z) ξ * a (p,x) ξ) * f z
        rw [← integral_mul_const]

end CalderonPaper
