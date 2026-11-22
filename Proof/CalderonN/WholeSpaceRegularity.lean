module

public import Proof.CalderonN.WeakPartialEquation
public import Proof.CalderonN.SobolevMultiplication
public import Proof.CalderonN.WholeSpaceVariableH2
import Mathlib.Tactic

public section

/-! Whole-space regularity for the localized divergence equation. The
order-raising step follows the released fixed-ball induction, using the
whole-space second-order estimate instead of a boundary estimate. -/
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonN
open TauCeti TauCeti.PDE WkpCalculus WeakTest
variable {n : ℕ}

local notation "Ω₀" => (⊤ : Opens (X n))
local notation "μ₀" => (volume : Measure (X n))

local instance : PseudoMetrizableSpace (Mat n) :=
  inferInstanceAs (PseudoMetrizableSpace (I n → I n → ℝ))

private theorem exists_lowerOrder_two (m : ℕ) (U : Wkp μ₀ Ω₀ 2 (m + 2)) :
    ∃ V : Wkp μ₀ Ω₀ 2 2, Wkp.lowerOrder 1 V = Wkp.firstOrder (m + 1) U := by
  induction m with
  | zero => exact ⟨U, rfl⟩
  | succ m ih =>
    obtain ⟨V, hV⟩ := ih (Wkp.lowerOrder (m + 2) U)
    exact ⟨V, hV.trans (Wkp.firstOrder_succ (m + 1) U).symm⟩

private theorem value_finsetSum_ae {J : Type*} (s : Finset J) (k : ℕ)
    (U : J → Wkp μ₀ Ω₀ 2 k) :
    ⇑(Wkp.value k (∑ j ∈ s, U j)) =ᵐ[(μ₀).restrict Ω₀]
      (fun x => ∑ j ∈ s, Wkp.value k (U j) x) := by
  simpa only [← TauCeti.Wkp.valueL_apply, map_sum] using
    (Lp.coeFn_fun_finsetSum s (fun j => TauCeti.Wkp.valueL k (U j)))

private theorem wholeSpace_weak_iff_test
    {a : X n → Mat n} (ha : Continuous a) {lo hi : ℝ}
    (hell : UniformlyEllipticOn univ a lo hi)
    (f : Lp ℝ 2 ((μ₀).restrict Ω₀)) (u : W1p0 μ₀ Ω₀ 2) :
    IsWeakSolutionDirichlet a 0 0 f u ↔
      ∀ φ : 𝓓(Ω₀, ℝ), (∫ x, matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
        (W1p.gradient (u : W1p μ₀ Ω₀ 2) x)) = ∫ x, f x * φ x := by
  have htop : (μ₀).restrict Ω₀ = μ₀ := by rw [Opens.coe_top, Measure.restrict_univ]
  have hcoeff : MemLp (fun x => energyIntegrand (a x)
      ((0 : X n → X n) x) ((0 : X n → ℝ) x)) ⊤ ((μ₀).restrict Ω₀) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) (hell.1.le.trans hell.2.1)
      ha.aestronglyMeasurable aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x _ => (hell.2.2 (x := x) (mem_univ _)).2) (by simp) (by simp)
  rw [isWeakSolutionDirichlet_iff_forall_testFunction hcoeff]
  apply forall_congr'
  intro φ
  have hint (F : X n → ℝ) : (∫ x in (Ω₀ : Set (X n)), F x ∂μ₀) = ∫ x, F x ∂μ₀ := by
    rw [htop]
  rw [energyFormH1_def, hint, hint]
  simp only [energyIntegrand_apply, jetField_apply, Pi.zero_apply, driftForm_apply,
    massForm_apply, add_zero, zero_mul, inner_zero_left]
  have hL : (∫ x, matrixBilinearForm (a x)
      (W1p.gradient (W1p.ofTestFunctionₗ μ₀ Ω₀ 2 φ) x)
      (W1p.gradient (u : W1p μ₀ Ω₀ 2) x)) =
    ∫ x, matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
      (W1p.gradient (u : W1p μ₀ Ω₀ 2) x) := by
    refine integral_congr_ae ?_
    have hφ := (gradientTestFunctionLp_apply_ae (mu := μ₀) 2 φ).filter_mono (ae_mono htop.ge)
    filter_upwards [hφ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx]
  rw [hL]

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
    (U : Wkp μ₀ Ω₀ 2 (m + 2)) (V : Wkp μ₀ Ω₀ 2 2)
    (hV : Wkp.lowerOrder 1 V = Wkp.firstOrder (m + 1) U)
    (F : Wkp μ₀ Ω₀ 2 (m + 1)) (k : Fin n) :
    ∃ G : Wkp μ₀ Ω₀ 2 m,
      ⇑(Wkp.value m G) =ᵐ[(μ₀).restrict Ω₀]
        partialForcing a k V (Wkp.firstOrder m F) := by
  let du := fun j => d j (m + 1) U
  have hdu (j : Fin n) :
      ⇑(Wkp.value m (Wkp.lowerOrder m (du j))) =ᵐ[(μ₀).restrict Ω₀]
        (fun x => W1p.gradient (Wkp.lowerOrder 1 V) x j) := by
    rw [← Wkp.value_succ, hV]
    exact value_d j (m + 1) U
  have hfirst (j : Fin n) : d1 j V = Wkp.firstOrder m (du j) := by
    apply W1p.ext_value
    rw [Wkp.value_firstOrder]
    apply Lp.ext
    change ⇑(Wkp.value 1 (d j 1 V)) =ᵐ[(μ₀).restrict Ω₀] ⇑(Wkp.value (m + 1) (du j))
    rw [← Wkp.firstOrder_zero (Wkp.lowerOrder 1 V)] at hV
    exact (value_d j 1 V).trans (by
      rw [Wkp.firstOrder_succ, hV]
      exact (value_d j (m + 1) U).symm)
  have hdu₂ (i j : Fin n) :
      ⇑(Wkp.value m (d i m (du j))) =ᵐ[(μ₀).restrict Ω₀]
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
  have hP (i j : Fin n) : ⇑(Wkp.value m (P i j)) =ᵐ[(μ₀).restrict Ω₀]
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

set_option maxHeartbeats 4500000 in
theorem exists_wholeSpace_higher_solution [NeZero n]
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) {a₀ : Mat n}
    (hac : HasCompactSupport (fun x => a x - a₀)) {lo hi : ℝ} {K : NNReal}
    (hell : UniformlyEllipticOn univ a lo hi)
    (hlip : ∀ i j, LipschitzWith K (fun x => a x i j)) (m : ℕ)
    (F : Wkp μ₀ Ω₀ 2 m) (u : W1p0 μ₀ Ω₀ 2)
    (h : IsWeakSolutionDirichlet a 0 0 (Wkp.value m F) u) :
    ∃ U : Wkp μ₀ Ω₀ 2 (m + 2), Wkp.firstOrder (m + 1) U = (u : W1p μ₀ Ω₀ 2) := by
  induction m generalizing u with
  | zero => exact OAI.AnisotropicCalderon.Regularity.exists_lowerOrder_eq_var hell hlip h
  | succ m ih =>
    obtain ⟨U,hU⟩ := ih (Wkp.lowerOrder m F) u (by rwa [← Wkp.value_succ])
    obtain ⟨V,hV⟩ := exists_lowerOrder_two m U
    have hVu := hV.trans hU
    let Fw := Wkp.firstOrder m F
    have heq := (wholeSpace_weak_iff_test ha.continuous hell (Wkp.value (m+1) F) u).mp h
    have heq' : ∀ φ : 𝓓(Ω₀, ℝ), (∫ x, matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
        (W1p.gradient (Wkp.lowerOrder 1 V) x)) = ∫ x, W1p.value Fw x * φ x := by
      simpa only [hVu, Fw, Wkp.value_firstOrder] using heq
    have hsol (k : Fin n) :
        ∃ Z : Wkp μ₀ Ω₀ 2 (m + 2),
          ⇑(Wkp.value (m + 2) Z) =ᵐ[(μ₀).restrict Ω₀]
            (fun x => W1p.gradient (u : W1p μ₀ Ω₀ 2) x k) := by
      obtain ⟨G,hG⟩ := exists_forcing_partial ha hac m U V hV F k
      let w : W1p0 μ₀ Ω₀ 2 := ⟨d1 k V, W1p.mem_w1p0Submodule_top (by norm_num) _⟩
      have htop : (μ₀).restrict Ω₀ = μ₀ := by rw [Opens.coe_top, Measure.restrict_univ]
      have hw : IsWeakSolutionDirichlet a 0 0 (Wkp.value m G) w := by
        apply (wholeSpace_weak_iff_test ha.continuous hell _ _).2
        intro φ
        have hφ := partial_test_equation ha V Fw heq' k φ
        have hIntegral (F : X n → ℝ) : (∫ x in (Ω₀ : Set (X n)), F x ∂μ₀) = ∫ x, F x ∂μ₀ := by
          rw [htop]
        rw [hIntegral] at hφ
        have hG' := hG.filter_mono (ae_mono htop.ge)
        change (∫ x, matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
            (W1p.gradient (d1 k V) x)) = ∫ x, Wkp.value m G x * φ x
        refine hφ.trans (integral_congr_ae ?_)
        filter_upwards [hG'] with x hx
        rw [hx, mul_comm]
      obtain ⟨Z,hZ⟩ := ih G w hw
      refine ⟨Z,?_⟩
      rw [← Wkp.value_firstOrder, hZ]
      change ⇑(Wkp.value 1 (d k 1 V)) =ᵐ[(μ₀).restrict Ω₀] _
      have hVfirst : Wkp.firstOrder 1 V = (u : W1p μ₀ Ω₀ 2) := by
        rw [Wkp.firstOrder_succ, Wkp.firstOrder_zero, hVu]
      simpa only [hVfirst] using value_d k 1 V
    choose Z hZ using hsol
    exact ⟨ofPartials (m + 2) (u : W1p μ₀ Ω₀ 2) Z hZ, firstOrder_ofPartials _ _ _ _⟩

end CalderonN
