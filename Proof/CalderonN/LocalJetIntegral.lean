module

public import Proof.CalderonN.LocalSmoothJetBudget
public import Proof.CalderonN.FixedKernelIntegral

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Uniform local jet bounds pass through integration on a fixed compact
interval. The quadratic directional Taylor formula uses that same interval. -/

public section

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

theorem norm_iteratedFDeriv_integral_on_compact_le
    {P A : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [OpensMeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {K U : Set A} {V : Set P}
    (hK : IsCompact K) (hKU : K ⊆ U) (hU : IsOpen U) (hV : IsOpen V) (hμ : μ Kᶜ = 0)
    (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : A → P → E}
      (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ V)) {p : P} (hp : p ∈ V) {C : ℝ},
      (∀ x ∈ K, ‖iteratedFDeriv ℝ n (f x) p‖ ≤ C) →
      ‖iteratedFDeriv ℝ n (fun z => ∫ x, f x z ∂μ) p‖ ≤ C*μ.real univ := by
  induction n with
  | zero =>
    intro E _ _ f hf p hp C hC
    rw [norm_iteratedFDeriv_zero]
    apply norm_integral_le_of_norm_le_const
    filter_upwards [ae_mem_of_measure_compl hμ] with x hx
    simpa only [norm_iteratedFDeriv_zero] using hC x hx
  | succ n ih =>
    intro E _ _ f hf p hp C hC
    have hSmooth : ContDiffOn ℝ ∞ (Function.uncurry fun x z => fderiv ℝ (f x) z) (U ×ˢ V) :=
      contDiffOn_partial hf (by simp) hU hV
    have hD : (fderiv ℝ (fun z => ∫ x, f x z ∂μ)) =ᶠ[𝓝 p]
        (fun z => ∫ x, fderiv ℝ (f x) z ∂μ) := by
      filter_upwards [hV.mem_nhds hp] with z hz
      exact (hasFDerivAt_integral_on_compact hK hKU hU hV hμ hf (by simp) hz).fderiv
    rw [← norm_iteratedFDeriv_fderiv,(hD.iteratedFDeriv ℝ n).eq_of_nhds]
    apply ih hSmooth hp
    intro x hx
    rw [norm_iteratedFDeriv_fderiv]
    exact hC x hx

theorem localSmoothJetBudget_intervalIntegral_unit
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (ℝ × P)} (hU : IsOpen U) {f : ℝ × P → E}
    (hf : ContDiffOn ℝ ∞ f U) {p : P} (hp : Icc (0:ℝ) 1 ×ˢ {p} ⊆ U)
    (N : ℕ) (C : ℝ) (hC : ∀ t ∈ Icc (0:ℝ) 1, ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (fun z => f (t,z)) p‖ ≤ C) :
    LocalSmoothJetBudget (fun z => ∫ t in (0:ℝ)..1, f (t,z)) p N C := by
  obtain ⟨W,V,hW,hV,hKW,hpV,hWV⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton hU hp
  have hpV' : p ∈ V := hpV (mem_singleton p)
  let μ := (volume : Measure ℝ).restrict (Icc (0:ℝ) 1)
  have hFinite : μ univ < ⊤ := by simp [μ,Real.volume_Icc]
  letI : IsFiniteMeasure μ := ⟨hFinite⟩
  have hμ : μ (Icc (0:ℝ) 1)ᶜ = 0 := by
    simp [μ,Measure.restrict_apply isClosed_Icc.measurableSet.compl]
  have hMass : μ.real univ = 1 := by simp [μ,Measure.real,Real.volume_Icc]
  have hEq : (fun z => ∫ t in (0:ℝ)..1, f (t,z)) = fun z => ∫ t, f (t,z) ∂μ := by
    funext z
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (integral_Icc_eq_integral_Ioc (f:=fun t => f (t,z))).symm
  have hF : ContDiffOn ℝ ∞ (Function.uncurry fun t z => f (t,z)) (W ×ˢ V) := hf.mono hWV
  rw [hEq]
  have hI : ContDiffOn ℝ ∞ (fun z => ∫ t, f (t,z) ∂μ) V := by
    apply contDiffOn_infty.mpr
    intro n
    exact contDiffOn_integral_on_compact isCompact_Icc hKW hW hV hμ n _ (hF.of_le (by simp))
  refine ⟨hI.contDiffAt (hV.mem_nhds hpV'),?_⟩
  intro n hn
  simpa only [hMass,mul_one] using
    norm_iteratedFDeriv_integral_on_compact_le isCompact_Icc hKW hW hV hμ n hF hpV'
      (fun t ht => hC t ht n hn)

/-- The set of parameters whose entire integration segment lies in the
joint smooth domain is open, and the integral is smooth there. -/
theorem contDiffOn_intervalIntegral_unit_of_tube
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : Set (ℝ × P)} (hV : IsOpen V) {f : ℝ × P → E} (hf : ContDiffOn ℝ ∞ f V) :
    let U : Set P := {p | Icc (0:ℝ) 1 ×ˢ {p} ⊆ V}
    IsOpen U ∧ ContDiffOn ℝ ∞ (fun z => ∫ t in (0:ℝ)..1, f (t,z)) U := by
  dsimp only
  refine ⟨isOpen_iff_mem_nhds.mpr ?_,?_⟩
  · intro p hp
    obtain ⟨W,Z,_,hZ,hKW,hpZ,hWZ⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton hV hp
    exact mem_of_superset (hZ.mem_nhds (hpZ (mem_singleton p))) (fun z hz q hq =>
      hWZ ⟨hKW hq.1,(mem_singleton_iff.mp hq.2).symm ▸ hz⟩)
  · intro p hp
    have ht : ContinuousOn (fun t => f (t,p)) (Icc (0:ℝ) 1) :=
      hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => hp (show (t,p) ∈ Icc (0:ℝ) 1 ×ˢ {p} from ⟨ht,mem_singleton p⟩))
    obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ht
    have h := localSmoothJetBudget_intervalIntegral_unit hV hf hp 0 C (fun t ht n hn => by
      have hn₀ : n = 0 := Nat.eq_zero_of_le_zero hn
      subst n
      simpa only [norm_iteratedFDeriv_zero] using hC t ht)
    exact h.smooth.contDiffWithinAt

theorem second_directional_taylor_integral_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F G H : ℝ → E)
    (hF : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt F (G t) t)
    (hG : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt G (H t) t)
    (hH : ContinuousOn H (Icc (0:ℝ) 1)) :
    F 1-F 0-G 0 = ∫ t in (0:ℝ)..1, (1-t) • H t := by
  let q (t : ℝ) := F t+(1-t) • G t
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt q ((1-t) • H t) t := by
    have hScalar : HasDerivAt (fun t : ℝ => 1-t) (-1) t := by
      have h := (hasDerivAt_id t).const_sub (1:ℝ)
      exact h
    have h := (hF t ht).add (hScalar.smul (hG t ht))
    convert h using 1
    rw [neg_one_smul]
    abel
  have hI : IntervalIntegrable (fun t => (1-t) • H t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (continuous_const.sub continuous_id).continuousOn.smul hH
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=q) (f':=fun t => (1-t) • H t)
    (fun t ht => hq t (by rwa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht)) hI
  rw [h]
  simp only [q,sub_self,zero_smul,add_zero,sub_zero,one_smul]
  abel

theorem affineLine_second_taylor_integral_unit
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set P} (hU : IsOpen U) {F : P → E} (hF : ContDiffOn ℝ ∞ F U)
    {p w : P} (s : ℝ) (hLine : ∀ t ∈ Icc (0:ℝ) 1, p+(t*s) • w ∈ U) :
    F (p+s • w) = F p+s • fderiv ℝ F p w+s^2 •
      (∫ t in (0:ℝ)..1, (1-t) • fderiv ℝ (fderiv ℝ F) (p+(t*s) • w) w w) := by
  let L (t : ℝ) := p+(t*s) • w
  let G (t : ℝ) := s • fderiv ℝ F (L t) w
  let H (t : ℝ) := s^2 • fderiv ℝ (fderiv ℝ F) (L t) w w
  have hL (t : ℝ) : HasDerivAt L (s • w) t := by
    simpa only [L,id_eq,one_mul] using (((hasDerivAt_id t).mul_const s).smul_const w).const_add p
  have hF' := hF.fderiv_of_isOpen (m:=∞) hU (by simp)
  have hG (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt (F ∘ L) (G t) t := by
    have hd := ((hF.contDiffAt (hU.mem_nhds (hLine t ht))).differentiableAt (by simp)).hasFDerivAt
    have h := hd.comp_hasDerivAt t (hL t)
    rw [map_smul] at h
    exact h
  have hH (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt G (H t) t := by
    have hd := ((hF'.contDiffAt (hU.mem_nhds (hLine t ht))).differentiableAt (by simp)).hasFDerivAt
    have h := ((hd.comp_hasDerivAt t (hL t)).clm_apply (hasDerivAt_const t w)).const_smul s
    simpa only [G,H,map_smul,ContinuousLinearMap.smul_apply,ContinuousLinearMap.zero_apply,
      map_zero,add_zero,zero_add,smul_smul,pow_two,Function.comp_def,Pi.smul_def] using h
  have hHC : ContinuousOn H (Icc (0:ℝ) 1) := by
    have hLC : ContinuousOn L (Icc (0:ℝ) 1) := fun t _ => (hL t).continuousAt.continuousWithinAt
    have h := (hF'.fderiv_of_isOpen (m:=∞) hU (by simp)).continuousOn.comp hLC hLine
    exact ((h.clm_apply continuousOn_const).clm_apply continuousOn_const).const_smul (s^2)
  have h := second_directional_taylor_integral_unit (F ∘ L) G H hG hH hHC
  have hIntegrand : (fun t => (1-t) • H t) =
      fun t => s^2 • ((1-t) • fderiv ℝ (fderiv ℝ F) (L t) w w) := by
    funext t
    simp only [H,smul_smul]
    rw [mul_comm]
  rw [hIntegrand,intervalIntegral.integral_smul] at h
  simp only [Function.comp_def,L,G,one_mul,zero_mul,zero_smul,add_zero] at h
  exact (sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp h)).trans (by abel)

end CalderonN
