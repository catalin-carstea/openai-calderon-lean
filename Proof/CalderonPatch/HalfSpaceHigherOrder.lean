module

public import Proof.CalderonPatch.SobolevPrincipalEquation
public import Proof.CalderonN.SobolevMultiplication

public import Proof.CalderonPatch.HalfSpaceTangentialExtension
import Mathlib.Tactic

public section

/-! Higher-order half-space regularity. This uses the same
differentiated equation and Sobolev products as the checked
whole-space argument. Only tangential directions preserve the
Dirichlet condition; the strong equation supplies the final normal
Hessian component. -/

noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPatch

open CalderonN TauCeti TauCeti.PDE WkpCalculus WeakTest

variable {n : ℕ} [NeZero n]

local notation "H" => positiveHalfSpaceOpens n
local notation "μ" => (volume : Measure (X n))

local instance : PseudoMetrizableSpace (Mat n) :=
  inferInstanceAs (PseudoMetrizableSpace (I n → I n → ℝ))

private theorem exists_lowerOrder_two (m : ℕ) (U : Wkp μ H 2 (m + 2)) :
    ∃ V : Wkp μ H 2 2, Wkp.lowerOrder 1 V = Wkp.firstOrder (m + 1) U := by
  induction m with
  | zero => exact ⟨U, rfl⟩
  | succ m ih =>
    obtain ⟨V, hV⟩ := ih (Wkp.lowerOrder (m + 2) U)
    exact ⟨V, hV.trans (Wkp.firstOrder_succ (m + 1) U).symm⟩

private theorem value_finsetSum_ae {J : Type*} (s : Finset J) (k : ℕ)
    (U : J → Wkp μ H 2 k) :
    ⇑(Wkp.value k (∑ j ∈ s, U j)) =ᵐ[(μ).restrict H]
      (fun x => ∑ j ∈ s, Wkp.value k (U j) x) := by
  simpa only [← TauCeti.Wkp.valueL_apply, map_sum] using
    (Lp.coeFn_fun_finsetSum s (fun j => TauCeti.Wkp.valueL k (U j)))

omit [NeZero n] in
private theorem derivatives_of_const_add_compact
    {a : X n → Mat n} {a₀ : Mat n}
    (h : HasCompactSupport (fun x => a x - a₀)) (i j k : Fin n) :
    HasCompactSupport (pd (fun x => a x i j) k) := by
  let b := fun x : X n => a x i j - a₀ i j
  have hs : HasCompactSupport b :=
    h.comp_left (g := fun M : Mat n => M i j) rfl
  have h' := hs.fderiv_apply ℝ (WeakTest.e k)
  have heq : pd (fun x => a x i j) k = pd b k := by
    funext x
    simp only [pd, b, fderiv_sub_const]
  rw [heq]
  exact h'

set_option maxHeartbeats 4000000 in
private theorem exists_forcing_partial
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) {a₀ : Mat n}
    (hac : HasCompactSupport (fun x => a x - a₀)) (m : ℕ)
    (U : Wkp μ H 2 (m + 2)) (V : Wkp μ H 2 2)
    (hV : Wkp.lowerOrder 1 V = Wkp.firstOrder (m + 1) U)
    (F : Wkp μ H 2 (m + 1)) (k : Fin n) :
    ∃ G : Wkp μ H 2 m,
      ⇑(Wkp.value m G) =ᵐ[(μ).restrict H]
        partialForcing a k V (Wkp.firstOrder m F) := by
  let du := fun j => d j (m + 1) U
  have hdu (j : Fin n) :
      ⇑(Wkp.value m (Wkp.lowerOrder m (du j))) =ᵐ[(μ).restrict H]
        (fun x => W1p.gradient (Wkp.lowerOrder 1 V) x j) := by
    rw [← Wkp.value_succ, hV]
    exact value_d j (m + 1) U
  have hfirst (j : Fin n) : d1 j V = Wkp.firstOrder m (du j) := by
    apply W1p.ext_value
    rw [Wkp.value_firstOrder]
    apply Lp.ext
    change ⇑(Wkp.value 1 (d j 1 V)) =ᵐ[(μ).restrict H] ⇑(Wkp.value (m + 1) (du j))
    rw [← Wkp.firstOrder_zero (Wkp.lowerOrder 1 V)] at hV
    exact (value_d j 1 V).trans (by
      rw [Wkp.firstOrder_succ, hV]
      exact (value_d j (m + 1) U).symm)
  have hdu₂ (i j : Fin n) :
      ⇑(Wkp.value m (d i m (du j))) =ᵐ[(μ).restrict H]
        (fun x => Wkp.iteratedGradient 1 V x (WeakTest.e i) j) :=
    (value_d i m (du j)).trans (by rw [← hfirst j]; exact gradient_d1_coordinate V j i)
  let B := fun (i j : Fin n) => pd (fun x => a x i j) k
  let C := fun (i j : Fin n) => pd (B i j) i
  have hB (i j : Fin n) : ContDiff ℝ ∞ (B i j) :=
    ((WeakTest.contDiff_entry ha i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hC (i j : Fin n) : ContDiff ℝ ∞ (C i j) :=
    ((hB i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hBc i j : HasCompactSupport (B i j) := derivatives_of_const_add_compact hac i j k
  have hCc i j : HasCompactSupport (C i j) := (hBc i j).fderiv_apply ℝ (WeakTest.e i)
  choose Y hY using fun i j => SobolevMultiplication.exists_mul m (hC i j) (hCc i j)
    (Wkp.lowerOrder m (du j))
  choose Z hZ using fun i j => SobolevMultiplication.exists_mul m (hB i j) (hBc i j)
    (d i m (du j))
  let P := fun (i j : Fin n) => Y i j + Z i j
  have hP (i j : Fin n) : ⇑(Wkp.value m (P i j)) =ᵐ[(μ).restrict H]
      (fun x => C i j x * W1p.gradient (Wkp.lowerOrder 1 V) x j +
        B i j x * Wkp.iteratedGradient 1 V x (WeakTest.e i) j) := by
    rw [show P i j = Y i j + Z i j by rfl, Wkp.value_add]
    filter_upwards [Lp.coeFn_add (Wkp.value m (Y i j)) (Wkp.value m (Z i j)),
      hY i j, hZ i j, hdu j, hdu₂ i j] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁, Pi.add_apply, h₂, h₃, h₄, h₅]
  let S := ∑ i, ∑ j, P i j
  have hS := value_finsetSum_ae Finset.univ m (fun i => ∑ j, P i j)
  have hS' := ae_all_iff.2 fun i => value_finsetSum_ae Finset.univ m (P i)
  refine ⟨d k m F + S, ?_⟩
  rw [Wkp.value_add]
  filter_upwards [Lp.coeFn_add (Wkp.value m (d k m F)) (Wkp.value m S),
    value_d k m F, hS, hS', ae_all_iff.2 (fun i => ae_all_iff.2 (hP i))] with x h₀ h₁ h₂ h₃ h₄
  simp only [h₀, Pi.add_apply, h₁, S, h₂, h₃, h₄, partialForcing, C, B]


private theorem halfSpace_weak_iff_test
    {a : X n → Mat n} (ha : Continuous a) {lo hi : ℝ}
    (hell : UniformlyEllipticOn univ a lo hi)
    (f : Lp ℝ 2 ((μ).restrict H)) (u : W1p0 μ H 2) :
    IsWeakSolutionDirichlet a 0 0 f u ↔
      ∀ φ : 𝓓(H, ℝ), (∫ x, matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
        (W1p.gradient (u : W1p μ H 2) x)) = ∫ x, f x * φ x := by
  have hcoeff : MemLp (fun x => energyIntegrand (a x)
      ((0 : X n → X n) x) ((0 : X n → ℝ) x)) ⊤ ((μ).restrict H) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) hell.upper_nonneg
      ha.aestronglyMeasurable aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x _ => hell.upper_bound (mem_univ x)) (by simp) (by simp)
  rw [isWeakSolutionDirichlet_iff_forall_testFunction hcoeff]
  apply forall_congr'
  intro φ
  change energyFormH1 a 0 0 (u : W1p μ H 2) (W1p.ofTestFunctionₗ μ H 2 φ) = _ ↔ _
  rw [energyFormH1_zero_zero_eq_setIntegral]
  have hL : (∫ x in H, matrixBilinearForm (a x)
      (W1p.gradient (W1p.ofTestFunctionₗ μ H 2 φ) x)
      (W1p.gradient (u : W1p μ H 2) x)) =
    ∫ x in H, matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
      (W1p.gradient (u : W1p μ H 2) x) := by
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := μ) 2 φ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ,hx]
  rw [hL,← WeakTest.integral_eq_setIntegral (Ω := H) (Z := fun x => f x * φ x)
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun hp => hx (φ.tsupport_subset hp)),mul_zero])]
  rw [← WeakTest.integral_eq_setIntegral (Ω := H)
    (Z := fun x => matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
      (W1p.gradient (u : W1p μ H 2) x))
    (fun x hx => by
      rw [gradient_of_notMem_tsupport (fun hp => hx (φ.tsupport_subset hp)), map_zero]
      rfl)]

private theorem exists_mul_of_compact_perturbation {φ : X n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (c : ℝ) (hc : HasCompactSupport (fun x => φ x - c)) (k : ℕ)
    (U : Wkp μ H 2 k) :
    ∃ V : Wkp μ H 2 k, (Wkp.value k V : X n → ℝ) =ᵐ[(μ).restrict H]
      fun x => φ x * Wkp.value k U x := by
  obtain ⟨V,hV⟩ := SobolevMultiplication.exists_mul k (hφ.sub contDiff_const) hc U
  refine ⟨V + c • U, ?_⟩
  rw [Wkp.value_add, Wkp.value_smul]
  filter_upwards [Lp.coeFn_add (Wkp.value k V) (c • Wkp.value k U),
    Lp.coeFn_smul c (Wkp.value k U),hV] with x h₁ h₂ h₃
  rw [h₁,Pi.add_apply,h₂,Pi.smul_apply,h₃,smul_eq_mul]
  ring

set_option maxHeartbeats 4000000 in
private theorem exists_normal_hessian_sobolev
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) {a₀ : Mat n}
    (hac : HasCompactSupport (fun x => a x - a₀)) (ha₀ : ∀ x, a x 0 0 ≠ 0)
    (k : ℕ) (F : Wkp μ H 2 k) (V : Wkp μ H 2 2)
    (heq : ∀ φ : 𝓓(H,ℝ), (∫ x, matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
      (W1p.gradient (Wkp.lowerOrder 1 V) x)) = ∫ x, Wkp.value k F x * φ x)
    (hG : ∀ j : Fin n, ∃ W : Wkp μ H 2 k, Wkp.value k W =ᵐ[(μ).restrict H]
      fun x => W1p.gradient (Wkp.lowerOrder 1 V) x j)
    (hM : ∀ i j : Fin n, i ≠ 0 ∨ j ≠ 0 → ∃ W : Wkp μ H 2 k, Wkp.value k W =ᵐ[(μ).restrict H]
      fun x => Wkp.iteratedGradient 1 V x (WeakTest.e i) j) :
    ∃ W : Wkp μ H 2 k, Wkp.value k W =ᵐ[(μ).restrict H]
      fun x => Wkp.iteratedGradient 1 V x (WeakTest.e 0) 0 := by
  classical
  choose G hG using hG
  have hM' (i j : Fin n) : ∃ W : Wkp μ H 2 k, Wkp.value k W =ᵐ[(μ).restrict H]
      fun x => if i = 0 ∧ j = 0 then 0 else Wkp.iteratedGradient 1 V x (WeakTest.e i) j := by
    by_cases h : i = 0 ∧ j = 0
    · refine ⟨0,?_⟩
      rw [← Wkp.valueL_apply, map_zero]
      simp only [ite_eq_left h]
      exact Lp.coeFn_zero _ _ _
    · obtain ⟨W,hW⟩ := hM i j (by tauto)
      exact ⟨W,by simpa only [ite_eq_right h] using hW⟩
  choose MM hMM using hM'
  let A (i j : Fin n) (z : X n) := a z i j
  let B (i j : Fin n) := pd (A i j) i
  have hac' (i j : Fin n) : HasCompactSupport (fun z => A i j z - a₀ i j) :=
    hac.comp_left (g := fun M : Mat n => M i j) rfl
  have hA (i j : Fin n) : ContDiff ℝ ∞ (A i j) := WeakTest.contDiff_entry ha i j
  have hB (i j : Fin n) : ContDiff ℝ ∞ (B i j) :=
    ((hA i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  choose P hP using fun i j => SobolevMultiplication.exists_mul k (hB i j)
    (derivatives_of_const_add_compact hac i j i) (G j)
  choose Q hQ using fun i j => exists_mul_of_compact_perturbation (hA i j)
    (a₀ i j) (hac' i j) k (MM i j)
  let S₁ := ∑ i, ∑ j, P i j
  let S₂ := ∑ i, ∑ j, Q i j
  have hp := (value_finsetSum_ae Finset.univ k (fun i => ∑ j, P i j)).and
    (ae_all_iff.2 (fun i => value_finsetSum_ae Finset.univ k (P i)))
  have hq := (value_finsetSum_ae Finset.univ k (fun i => ∑ j, Q i j)).and
    (ae_all_iff.2 (fun i => value_finsetSum_ae Finset.univ k (Q i)))
  let N := - (F + S₁ + S₂)
  have hφ : ContDiff ℝ ∞ (fun x => (A 0 0 x)⁻¹) := (hA 0 0).inv ha₀
  have hχ : HasCompactSupport (fun x => (A 0 0 x)⁻¹ - (a₀ 0 0)⁻¹) := by
    convert (hac' 0 0).comp_left
      (g := fun t : ℝ => (t + a₀ 0 0)⁻¹ - (a₀ 0 0)⁻¹) (by simp) using 1
    funext x
    simp
  obtain ⟨Z,hZ⟩ := exists_mul_of_compact_perturbation hφ _ hχ k N
  refine ⟨Z,?_⟩
  have hstrong := ae_principal_equation_of_wkp_two ha V (Wkp.value k F) heq
  have hN : Wkp.value k N = - (Wkp.value k F + Wkp.value k S₁ + Wkp.value k S₂) := by
    simp [N,← Wkp.valueL_apply]
  filter_upwards [hstrong,hZ,hp,hq,ae_all_iff.2 hG,ae_all_iff.2 (fun i => ae_all_iff.2 (hMM i)),
    ae_all_iff.2 (fun i => ae_all_iff.2 (hP i)),ae_all_iff.2 (fun i => ae_all_iff.2 (hQ i)),
    Lp.coeFn_neg (Wkp.value k F + Wkp.value k S₁ + Wkp.value k S₂),
    Lp.coeFn_add (Wkp.value k F + Wkp.value k S₁) (Wkp.value k S₂),
    Lp.coeFn_add (Wkp.value k F) (Wkp.value k S₁)]
    with x he hz ⟨hp₁,hp₂⟩ ⟨hq₁,hq₂⟩ hg hm hp hq hn hAdd hAdd'
  rw [hz,hN,hn,Pi.neg_apply,hAdd,Pi.add_apply,hAdd',Pi.add_apply]
  change (A 0 0 x)⁻¹ * _ = _
  rw [hp₁,hq₁]
  simp only [hp₂,hq₂,hp,hq,hg,hm]
  have hSplit :
      (∑ i, ∑ j, A i j x * Wkp.iteratedGradient 1 V x (WeakTest.e i) j) =
      (∑ i, ∑ j, A i j x * if i = 0 ∧ j = 0 then 0 else
        Wkp.iteratedGradient 1 V x (WeakTest.e i) j) +
      A 0 0 x * Wkp.iteratedGradient 1 V x (WeakTest.e 0) 0 := by
    calc
      _ = ∑ i, ∑ j,
          ((A i j x * if i = 0 ∧ j = 0 then 0 else Wkp.iteratedGradient 1 V x (WeakTest.e i) j) +
            if i = 0 ∧ j = 0 then A i j x * Wkp.iteratedGradient 1 V x (WeakTest.e i) j else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      _ = _ := by simp [Finset.sum_add_distrib,ite_and]
  change Wkp.value k F x + ∑ i, ∑ j,
    (B i j x * W1p.gradient (Wkp.lowerOrder 1 V) x j +
      A i j x * Wkp.iteratedGradient 1 V x (WeakTest.e i) j) = 0 at he
  simp only [Finset.sum_add_distrib] at he
  rw [hSplit] at he
  have hsolve : - (Wkp.value k F x +
      (∑ i, ∑ j, B i j x * W1p.gradient (Wkp.lowerOrder 1 V) x j) +
      (∑ i, ∑ j, A i j x * if i = 0 ∧ j = 0 then 0 else
        Wkp.iteratedGradient 1 V x (WeakTest.e i) j)) =
      A 0 0 x * Wkp.iteratedGradient 1 V x (WeakTest.e 0) 0 := by linarith
  rw [hsolve,← mul_assoc, inv_mul_cancel₀ (ha₀ x),one_mul]

set_option maxHeartbeats 6000000 in
/-- Higher-order regularity of homogeneous Dirichlet data on the
flat half-space, using its genuine tangential zero-trace property. -/
theorem exists_halfSpace_higher_solution_of_tangential_trace
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) {a₀ : Mat n}
    (hac : HasCompactSupport (fun x => a x - a₀)) {lo hi : ℝ} {K : NNReal}
    (hell : UniformlyEllipticOn univ a lo hi)
    (hLip : LipschitzWith K fun x => matrixBilinearForm (a x))
    (hA : ContDiff ℝ ∞ fun x => matrixBilinearForm (a x))
    (hPos : ∀ x v, v ≠ 0 → 0 < matrixBilinearForm (a x) v v)
    (htrace : ∀ V : Wkp μ H 2 2, Wkp.lowerOrder 1 V ∈ w1p0Submodule μ H 2 →
      ∀ j : Fin n, j ≠ 0 → WkpCalculus.d1 j V ∈ w1p0Submodule μ H 2)
    (m : ℕ) (F : Wkp μ H 2 m) (u : W1p0 μ H 2)
    (h : IsWeakSolutionDirichlet a 0 0 (Wkp.value m F) u) :
    ∃ U : Wkp μ H 2 (m + 2), Wkp.firstOrder (m + 1) U = (u : W1p μ H 2) := by
  have hν : WeakTest.e (0 : Fin n) ≠ 0 := by
    intro he
    have h := congrArg (fun z : X n => z 0) he
    simp [WeakTest.e] at h
  have hH (x : X n) : x ∈ H ↔ 0 < ⟪x, WeakTest.e (0 : Fin n)⟫_ℝ := by
    change 0 < x 0 ↔ _
    rw [← WeakTest.coord_eq_inner]
  have h00 (x : X n) : a x 0 0 ≠ 0 := by
    have h := hPos x _ hν
    rw [WeakTest.matrixBilinearForm_eq_sum] at h
    simp [WeakTest.e] at h
    exact h.ne'
  induction m generalizing u with
  | zero =>
    obtain ⟨V,hV⟩ := (hell.mono_set (subset_univ (H : Set (X n)))).exists_lowerOrder_eq_of_halfSpace
      hν hH hLip.lipschitzOnWith hA hPos h
    exact ⟨V,by rwa [Wkp.firstOrder_succ,Wkp.firstOrder_zero]⟩
  | succ m ih =>
    obtain ⟨U,hU⟩ := ih (Wkp.lowerOrder m F) u (by rwa [← Wkp.value_succ])
    obtain ⟨V,hV⟩ := exists_lowerOrder_two m U
    have hVu := hV.trans hU
    have hVzero : Wkp.lowerOrder 1 V ∈ w1p0Submodule μ H 2 := hVu.symm ▸ u.property
    let Fw := Wkp.firstOrder m F
    have heq := (halfSpace_weak_iff_test ha.continuous hell (Wkp.value (m + 1) F) u).mp h
    have heq' (φ : 𝓓(H,ℝ)) :
        (∫ x, matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
          (W1p.gradient (Wkp.lowerOrder 1 V) x)) = ∫ x, W1p.value Fw x * φ x := by
      simpa only [hVu,Fw,Wkp.value_firstOrder] using heq φ
    have hT (j : Fin n) (hj : j ≠ 0) :
        ∃ Z : Wkp μ H 2 (m + 2), Wkp.firstOrder (m + 1) Z = WkpCalculus.d1 j V := by
      obtain ⟨G,hG⟩ := exists_forcing_partial ha hac m U V hV F j
      let w : W1p0 μ H 2 := ⟨WkpCalculus.d1 j V,htrace V hVzero j hj⟩
      have hw : IsWeakSolutionDirichlet a 0 0 (Wkp.value m G) w := by
        apply (halfSpace_weak_iff_test ha.continuous hell _ _).2
        intro φ
        have hφ := partial_test_equation ha V Fw heq' j φ
        change (∫ x, matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
          (W1p.gradient (d1 j V) x)) = ∫ x, Wkp.value m G x * φ x
        rw [WeakTest.integral_eq_setIntegral (Ω := H)
          (Z := fun x => matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
            (W1p.gradient (d1 j V) x))
            (fun x hx => by
              rw [gradient_of_notMem_tsupport (fun hp => hx (φ.tsupport_subset hp)),map_zero]
              rfl)]
        refine hφ.trans ?_
        rw [WeakTest.integral_eq_setIntegral (Ω := H) (Z := fun x => φ x * partialForcing a j V Fw x)
          (fun x hx => by rw [(TF.of φ).zero_of_notMem hx,zero_mul]),
          WeakTest.integral_eq_setIntegral (Ω := H) (Z := fun x => Wkp.value m G x * φ x)
          (fun x hx => by rw [(TF.of φ).zero_of_notMem hx,mul_zero])]
        refine integral_congr_ae ?_
        filter_upwards [hG] with x hx
        rw [hx,mul_comm]
      exact ih G w hw
    have hM' (i j : Fin n) (hj : j ≠ 0) :
        ∃ Z : Wkp μ H 2 (m + 1), Wkp.value (m + 1) Z =ᵐ[(μ).restrict H]
          fun x => Wkp.iteratedGradient 1 V x (WeakTest.e i) j := by
      obtain ⟨Z,hZ⟩ := hT j hj
      refine ⟨WkpCalculus.d i (m + 1) Z,?_⟩
      have hd := value_d i (m + 1) Z
      rw [hZ] at hd
      exact hd.trans (gradient_d1_coordinate V j i)
    have hM (i j : Fin n) (hij : i ≠ 0 ∨ j ≠ 0) :
        ∃ Z : Wkp μ H 2 (m + 1), Wkp.value (m + 1) Z =ᵐ[(μ).restrict H]
          fun x => Wkp.iteratedGradient 1 V x (WeakTest.e i) j := by
      rcases hij with hi | hj
      · obtain ⟨Z,hZ⟩ := hM' j i hi
        exact ⟨Z,hZ.trans (wkp_two_hessian_symm V j i)⟩
      · exact hM' i j hj
    have hGrad (j : Fin n) :
        ∃ Z : Wkp μ H 2 (m + 1), Wkp.value (m + 1) Z =ᵐ[(μ).restrict H]
          fun x => W1p.gradient (Wkp.lowerOrder 1 V) x j :=
      ⟨WkpCalculus.d j (m + 1) U,by rw [hV]; exact value_d j (m + 1) U⟩
    obtain ⟨Z₀,hZ₀⟩ := exists_normal_hessian_sobolev ha hac h00 (m + 1) F V
      (fun φ => by simpa only [Fw,Wkp.value_firstOrder] using heq' φ) hGrad hM
    have hD (i : Fin n) :
        ∃ Z : Wkp μ H 2 (m + 1), Wkp.value (m + 1) Z =ᵐ[(μ).restrict H]
          fun x => W1p.gradient (WkpCalculus.d1 0 V) x i := by
      by_cases hi : i = 0
      · subst i
        exact ⟨Z₀,hZ₀.trans (gradient_d1_coordinate V 0 0).symm⟩
      · obtain ⟨Z,hZ⟩ := hM i 0 (Or.inl hi)
        exact ⟨Z,hZ.trans (gradient_d1_coordinate V 0 i).symm⟩
    choose Z hZ using hD
    have hdN : ∃ Z : Wkp μ H 2 (m + 2), Wkp.firstOrder (m + 1) Z = WkpCalculus.d1 0 V :=
      ⟨ofPartials (m + 1) (d1 0 V) Z hZ,firstOrder_ofPartials _ _ _ _⟩
    have hPartial (j : Fin n) :
        ∃ Z : Wkp μ H 2 (m + 2), Wkp.value (m + 2) Z =ᵐ[(μ).restrict H]
          fun x => W1p.gradient (u : W1p μ H 2) x j := by
      have hj : ∃ Z : Wkp μ H 2 (m + 2), Wkp.firstOrder (m + 1) Z = WkpCalculus.d1 j V := by
        by_cases h : j = 0
        · subst j; exact hdN
        · exact hT j h
      obtain ⟨Z,hZ⟩ := hj
      refine ⟨Z,?_⟩
      rw [← Wkp.value_firstOrder,hZ]
      have hVfirst : Wkp.firstOrder 1 V = (u : W1p μ H 2) := by
        rw [Wkp.firstOrder_succ,Wkp.firstOrder_zero,hVu]
      change Wkp.value 1 (d j 1 V) =ᵐ[(μ).restrict H] _
      simpa only [hVfirst] using value_d j 1 V
    choose P hP using hPartial
    exact ⟨ofPartials (m + 2) (u : W1p μ H 2) P hP,firstOrder_ofPartials _ _ _ _⟩

end CalderonPatch
