module

public import Proof.CalderonN.BallRegularity.HigherOrder
public import Proof.CalderonN.BallRegularity.SecondDerivative

/-! From Proof/Archive/CollaboratorRegularityInductionStepOct17.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace CalderonN.BallRegularity.HO

set_option maxHeartbeats 1200000

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE


theorem exists_lowerTo : ∀ (m : ℕ) (W : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 (m + 2)),
    ∃ V : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 2, Wkp.lowerOrder 1 V = Wkp.firstOrder (m + 1) W
  | 0, W => ⟨W, rfl⟩
  | m + 1, W => by
      obtain ⟨V, hV⟩ := exists_lowerTo m (Wkp.lowerOrder (m + 2) W)
      exact ⟨V, hV.trans (Wkp.firstOrder_succ (m + 1) W).symm⟩

theorem matrixBilinearForm_eq_sum (A : Matrix (Fin dim) (Fin dim) ℝ) (η ξ : (X dim)) :
    matrixBilinearForm A η ξ = ∑ i, ∑ k, η i * A i k * ξ k := by
  rw [matrixBilinearForm_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem contDiff_coord (j : Fin dim) : ContDiff ℝ ∞ (fun x : (X dim) => x j) :=
  (EuclideanSpace.proj j : (X dim) →L[ℝ] ℝ).contDiff

theorem contDiff_gradient_coord {ψ : (X dim) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (k : Fin dim) :
    ContDiff ℝ ∞ (fun x => gradient ψ x k) :=
  (EuclideanSpace.proj k : (X dim) →L[ℝ] ℝ).contDiff.comp (hψ.gradient_right (m := ∞) (by simp))

theorem contDiff_matrix_entry {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a) (i k : Fin dim) :
    ContDiff ℝ ∞ (fun x => a x i k) :=
  contDiff_pi.mp (contDiff_pi.mp ha i) k


theorem contDiff_divCoeffGradient {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a)
    {ψ : (X dim) → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (divCoeffGradient a ψ) := by
  have hg : ∀ i : Fin dim, ContDiff ℝ ∞ (fun y => matrixBilinearForm (a y)
      (EuclideanSpace.basisFun (Fin dim) ℝ i) (gradient ψ y)) := fun i => by
    have : (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun (Fin dim) ℝ i)
        (gradient ψ y)) = fun y => ∑ i', ∑ k, (EuclideanSpace.basisFun (Fin dim) ℝ i) i' *
          a y i' k * gradient ψ y k := funext fun y => matrixBilinearForm_eq_sum _ _ _
    rw [this]
    exact ContDiff.sum fun i' _ => ContDiff.sum fun k _ =>
      (contDiff_const.mul (contDiff_matrix_entry ha i' k)).mul (contDiff_gradient_coord hψ k)
  have : divCoeffGradient a ψ = fun x => ∑ i : Fin dim, fderiv ℝ (fun y => matrixBilinearForm (a y)
      (EuclideanSpace.basisFun (Fin dim) ℝ i) (gradient ψ y)) x
        (EuclideanSpace.basisFun (Fin dim) ℝ i) := by
    funext x
    simp only [divCoeffGradient]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact ((hg i).differentiable (by simp) x).lineDeriv_eq_fderiv
  rw [this]
  exact ContDiff.sum fun i _ =>
    ((hg i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem aeIn_mulc (m : ℕ) {c : (X dim) → ℝ} (hc : ContDiff ℝ ∞ c) {f : (X dim) → ℝ}
    (hf : AEIn ((Hs dim) m) f) : AEIn ((Hs dim) m) (fun x => c x * f x) := by
  obtain ⟨h, hP, hh⟩ := hf
  let χ := bump (dim := dim) 1 2 (by norm_num) (by norm_num)
  have hcs : HasCompactSupport (fun x => χ x * c x) := χ.hasCompactSupport.mul_right
  refine aeIn_congr (aeIn_mul m (χ.contDiff.mul hc) hcs hP) ?_
  filter_upwards [hh, ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with x h1 hx
  have hx1 : χ x = 1 := χ.one_of_mem_closedBall (by
    have : ‖x‖ < 1 := by simpa [fixedBallOpens] using hx
    simpa [χ] using this.le)
  rw [h1, hx1, one_mul]

theorem aeIn_of_mem_Hs {m : ℕ} {g : (L2B dim)} (hg : g ∈ (Hs dim) m) : AEIn ((Hs dim) m) g := aeIn_of_mem hg

theorem aeIn_mono {m n : ℕ} (h : m ≤ n) {f : (X dim) → ℝ} (hf : AEIn ((Hs dim) n) f) : AEIn ((Hs dim) m) f := by
  obtain ⟨g, hg, hgf⟩ := hf
  exact ⟨g, Hs_le h hg, hgf⟩


theorem aeIn_locForcing (m : ℕ) {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a)
    {ζ : (X dim) → ℝ} (hζ : ContDiff ℝ ∞ ζ) {F : (L2B dim)} (hF : F ∈ (Hs dim) (m + 1))
    (U : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 (m + 2)) :
    AEIn ((Hs dim) (m + 1)) (locForcing a ζ F (Wkp.firstOrder (m + 1) U)) := by
  set u := Wkp.firstOrder (m + 1) U
  have hdu : ∀ i, AEIn ((Hs dim) (m + 1)) (fun x => W1p.gradient u x i) := aeIn_partial (m + 1) U
  have hu : AEIn ((Hs dim) (m + 1)) (W1p.value u) :=
    aeIn_of_mem (Hs_succ_le (m + 1) (value_firstOrder_mem_Hs (m + 1) U))
  have hgζ : ∀ k, ContDiff ℝ ∞ (fun x => gradient ζ x k) := contDiff_gradient_coord hζ
  have h1 : AEIn ((Hs dim) (m + 1)) (fun x => ζ x * F x) := aeIn_mulc (m + 1) hζ (aeIn_of_mem hF)
  have h2 : AEIn ((Hs dim) (m + 1))
      (fun x => matrixBilinearForm (a x) (W1p.gradient u x) (gradient ζ x)) := by
    simp only [matrixBilinearForm_eq_sum]
    refine aeIn_sum _ fun i _ => aeIn_sum _ fun k _ => ?_
    refine aeIn_congr (aeIn_mulc (m + 1) ((contDiff_matrix_entry ha i k).mul (hgζ k)) (hdu i)) ?_
    exact Filter.Eventually.of_forall fun x => by ring
  have h3 : AEIn ((Hs dim) (m + 1))
      (fun x => matrixBilinearForm (a x) (gradient ζ x) (W1p.gradient u x)) := by
    simp only [matrixBilinearForm_eq_sum]
    refine aeIn_sum _ fun i _ => aeIn_sum _ fun k _ => ?_
    refine aeIn_congr (aeIn_mulc (m + 1) ((hgζ i).mul (contDiff_matrix_entry ha i k)) (hdu k)) ?_
    exact Filter.Eventually.of_forall fun x => by ring
  have h4 : AEIn ((Hs dim) (m + 1)) (fun x => W1p.value u x * divCoeffGradient a ζ x) := by
    refine aeIn_congr (aeIn_mulc (m + 1) (contDiff_divCoeffGradient ha hζ) hu) ?_
    exact Filter.Eventually.of_forall fun x => by ring
  refine aeIn_congr (aeIn_sub (aeIn_sub (aeIn_sub h1 h2) h3) h4) ?_
  exact Filter.Eventually.of_forall fun x => by simp only [locForcing]


theorem integrable_mul_test {f : (X dim) → ℝ} (hf : AEIn ((Hs dim) 0) f) (φ : 𝓓((fixedBallOpens dim), ℝ)) :
    Integrable (fun x => f x * φ x) ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) := by
  obtain ⟨g, -, hg⟩ := hf
  refine (L2.integrable_inner (𝕜 := ℝ) (testFunctionLp (mu := (volume : Measure (X dim))) 2 φ) g).congr ?_
  filter_upwards [hg, testFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2 φ] with x h1 h2
  rw [real_inner_eq_re_inner, h1, h2]
  simp


theorem aeIn_dv (m : ℕ) (W : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 (m + 2)) (k : Fin dim) :
    AEIn ((Hs dim) (m + 1)) (fun x => W1p.gradient (Wkp.firstOrder (m + 1) W) x k) :=
  aeIn_partial (m + 1) W k


theorem aeIn_sd (m : ℕ) (W : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 (m + 2))
    (V2 : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 2) (hV2 : Wkp.lowerOrder 1 V2 = Wkp.firstOrder (m + 1) W)
    (i k : Fin dim) : AEIn ((Hs dim) m) (SD.sd V2 i k) := by
  have heq : SD.dv V2 k = Wkp.firstOrder m (WkpCalculus.d k (m + 1) W) := by
    apply W1p.ext_value
    apply Lp.ext
    filter_upwards [SD.value_dv V2 k, WkpCalculus.value_d k (m + 1) W] with x h1 h2
    rw [h1, hV2, Wkp.value_firstOrder, h2]
  have := aeIn_partial m (WkpCalculus.d k (m + 1) W) i
  rw [← heq] at this
  exact this


theorem exists_rhs (m : ℕ) (W : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 (m + 2))
    (V2 : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 2) (hV2 : Wkp.lowerOrder 1 V2 = Wkp.firstOrder (m + 1) W)
    {M : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (hM : ContDiff ℝ ∞ M) {c : (X dim) → (X dim)} (hc : ContDiff ℝ ∞ c)
    {Fw : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2} (hFw : W1p.value Fw ∈ (Hs dim) (m + 1)) :
    ∃ G : (L2B dim), G ∈ (Hs dim) m ∧ ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      (∫ x in ((fixedBallOpens dim) : Set (X dim)), ⟪c x, W1p.gradient Fw x⟫_ℝ * φ x) +
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (M x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient (Wkp.lowerOrder 1 V2) x) =
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), G x * φ x := by
  obtain ⟨W', hW'⟩ := exists_of_value_mem_Hs m Fw hFw
  have hcF : AEIn ((Hs dim) m) (fun x => ⟪c x, W1p.gradient Fw x⟫_ℝ) := by
    have : (fun x => ⟪c x, W1p.gradient Fw x⟫_ℝ) =
        fun x => ∑ l, c x l * W1p.gradient Fw x l := by
      funext x
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, mul_comm]
    rw [this]
    refine aeIn_sum _ fun l _ => aeIn_mulc m
      ((EuclideanSpace.proj l : (X dim) →L[ℝ] ℝ).contDiff.comp hc) ?_
    simpa only [hW'] using aeIn_partial m W' l
  have hdiv : AEIn ((Hs dim) m) (fun x => ∑ i, ∑ k,
      (fderiv ℝ (fun y => M y i k) x (EuclideanSpace.single i 1) *
        W1p.gradient (Wkp.lowerOrder 1 V2) x k + M x i k * SD.sd V2 i k x)) := by
    refine aeIn_sum _ fun i _ => aeIn_sum _ fun k _ => aeIn_add ?_ ?_
    · have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => M y i k) x (EuclideanSpace.single i 1)) :=
        ((contDiff_matrix_entry hM i k).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      refine aeIn_mulc m hd ?_
      rw [hV2]
      exact aeIn_mono (Nat.le_succ m) (aeIn_dv m W k)
    · exact aeIn_mulc m (contDiff_matrix_entry hM i k) (aeIn_sd m W V2 hV2 i k)
  obtain ⟨G, hG, hGe⟩ := aeIn_sub hcF hdiv
  refine ⟨G, hG, fun φ => ?_⟩
  rw [SD.integral_mbf_eq V2 hM φ, ← sub_eq_add_neg,
    ← integral_sub (integrable_mul_test (aeIn_mono (Nat.zero_le m) hcF) φ)
      (integrable_mul_test (aeIn_mono (Nat.zero_le m) hdiv) φ)]
  refine integral_congr_ae ?_
  filter_upwards [hGe] with x hx
  rw [hx, sub_mul]

def RegAt (a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ) (m : ℕ) : Prop :=
  ∀ F : (L2B dim), F ∈ (Hs dim) m → ∀ w : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2,
    w ∈ w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2 →
    (∀ φ : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2,
      φ ∈ w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2 →
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient w x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), F x * W1p.value φ x) →
    W1p.value w ∈ (Hs dim) (m + 2)

theorem regAt_congr {a b : (X dim) → Matrix (Fin dim) (Fin dim) ℝ}
    (hab : ∀ x ∈ ((fixedBallOpens dim) : Set (X dim)), a x = b x) {m : ℕ} (h : RegAt a m) : RegAt b m :=
  fun F hF w hw heq => h F hF w hw fun φ hφ => by
    rw [← heq φ hφ]
    exact setIntegral_congr_fun (fixedBallOpens dim).isOpen.measurableSet fun x hx => by rw [hab x hx]

theorem gradient_eq_zero_of_notMem_tsupport {ζ : (X dim) → ℝ} {x : (X dim)} (hx : x ∉ tsupport ζ) :
    gradient ζ x = 0 := by
  simp [gradient, fderiv_of_notMem_tsupport ℝ hx]


theorem value_mul_mem_Hs (m : ℕ) {ζ : (X dim) → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (U : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 (m + 2)) {w : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2}
    (hw : ⇑(W1p.value w) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => ζ x * W1p.value (Wkp.firstOrder (m + 1) U) x) :
    W1p.value w ∈ (Hs dim) (m + 2) :=
  mem_of_aeIn (aeIn_congr (aeIn_mulc (m + 2) hζ
    (aeIn_of_mem (value_firstOrder_mem_Hs (m + 1) U))) hw.symm)


theorem exists_w1p_of_mem_Hs (m : ℕ) {F : (L2B dim)} (hF : F ∈ (Hs dim) (m + 1)) :
    ∃ Fw : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2, W1p.value Fw = F ∧
      W1p.value Fw ∈ (Hs dim) (m + 1) := by
  obtain ⟨G, hG⟩ := mem_Hs.mp hF
  exact ⟨Wkp.firstOrder m G, by rw [Wkp.value_firstOrder, hG], by
    rw [Wkp.value_firstOrder, hG]; exact hF⟩

theorem interior_step (m : ℕ) {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a)
    (ih : RegAt a m) (U : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 (m + 2))
    {ζ : (X dim) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζB : tsupport ζ ⊆ ((fixedBallOpens dim) : Set (X dim)))
    (hζc : HasCompactSupport ζ) {Fζ : (L2B dim)} (hFζ : Fζ ∈ (Hs dim) (m + 1))
    (w : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2)
    (hwv : ⇑(W1p.value w) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => ζ x * W1p.value (Wkp.firstOrder (m + 1) U) x)
    (hwg : ⇑(W1p.gradient w) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => ζ x • W1p.gradient (Wkp.firstOrder (m + 1) U) x +
        W1p.value (Wkp.firstOrder (m + 1) U) x • gradient ζ x)
    (heq : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
          (ζ x • W1p.gradient (Wkp.firstOrder (m + 1) U) x +
            W1p.value (Wkp.firstOrder (m + 1) U) x • gradient ζ x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), Fζ x * φ x) (k : Fin dim) :
    AEIn ((Hs dim) (m + 2)) (fun x => W1p.gradient w x k) := by
  obtain ⟨Wn, hWn⟩ := exists_of_value_mem_Hs (m + 1) w (value_mul_mem_Hs m hζ U hwv)
  obtain ⟨V2, hV2'⟩ := exists_lowerTo m Wn
  have hV2 : Wkp.lowerOrder 1 V2 = w := hV2'.trans hWn
  obtain ⟨Fw, hFw, hFwH⟩ := exists_w1p_of_mem_Hs m hFζ
  have heq' : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient (Wkp.lowerOrder 1 V2) x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), W1p.value Fw x * φ x := by
    intro φ
    rw [hV2, hFw, ← heq φ]
    refine integral_congr_ae ?_
    filter_upwards [hwg] with x hx
    rw [hx]
  have hdiv : ∀ x, ∑ l : Fin dim, fderiv ℝ (fun _ : (X dim) => (EuclideanSpace.single k 1 : (X dim))) x
      (EuclideanSpace.single l 1) l = 0 := fun x => by simp
  obtain ⟨z, hz, M, hM, hzeq⟩ := BallRegularity.exists_diff_equation ha contDiff_const hdiv V2 Fw heq'
  obtain ⟨G, hG, hGe⟩ := exists_rhs m Wn V2 hV2' hM contDiff_const hFwH
  have htest : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient z x) = ∫ x in ((fixedBallOpens dim) : Set (X dim)), G x * φ x :=
    fun φ => (hzeq φ).trans (hGe φ)
  have hzH := eq_of_testFunction ha.continuous htest
  have hzk : ⇑(W1p.value z) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => W1p.gradient w x k := by
    filter_upwards [hz] with x hx
    rw [hx, hV2, EuclideanSpace.inner_single_left]
    simp
  have hz0 : z ∈ w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2 := by
    refine W1p.mem_w1p0Submodule_of_isCompact (p := 2) (by norm_num) hζc hζB ?_
    filter_upwards [hzk, hwg] with x h1 h2 hx
    rw [h1, h2, image_eq_zero_of_notMem_tsupport hx, gradient_eq_zero_of_notMem_tsupport hx]
    simp
  exact aeIn_congr (aeIn_of_mem (ih G hG z hz0 hzH)) hzk


theorem contDiff_gen (j k : Fin dim) : ContDiff ℝ ∞ (BallRotation.gen j k) := by
  unfold BallRotation.gen
  exact ((contDiff_coord j).smul contDiff_const).sub ((contDiff_coord k).smul contDiff_const)

theorem div_gen (j k : Fin dim) (x : (X dim)) :
    ∑ l : Fin dim, fderiv ℝ (BallRotation.gen j k) x (EuclideanSpace.single l 1) l = 0 := by
  have hlin : BallRotation.gen j k = fun y : (X dim) =>
      ((EuclideanSpace.proj j : (X dim) →L[ℝ] ℝ).smulRight (EuclideanSpace.single k (1 : ℝ)) -
        (EuclideanSpace.proj k : (X dim) →L[ℝ] ℝ).smulRight (EuclideanSpace.single j (1 : ℝ))) y := by
    funext y; simp [BallRotation.gen]
  rw [hlin, ContinuousLinearMap.fderiv]
  apply Finset.sum_eq_zero
  intro l _
  rw [sub_apply, PiLp.sub_apply]
  simp only [ContinuousLinearMap.smulRight_apply, PiLp.smul_apply, EuclideanSpace.coe_proj,
    EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]
  by_cases hlj : l = j <;> by_cases hlk : l = k <;> simp [hlj, hlk, eq_comm]

theorem boundary_step (m : ℕ) {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a)
    (hac : HasCompactSupport a) {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ ((fixedBallOpens dim) : Set (X dim)), ∀ ξ : (X dim), lam * ‖ξ‖ ^ 2 ≤ matrixBilinearForm (a x) ξ ξ)
    (ih : RegAt a m) {v : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2}
    (hv0 : v ∈ w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2)
    (V' : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 (m + 2)) (hV' : Wkp.firstOrder (m + 1) V' = v)
    (hvz : ∀ᵐ x ∂(volume : Measure (X dim)).restrict (fixedBallOpens dim), ‖x‖ < 3 / 4 → W1p.value v x = 0)
    {Fv : (L2B dim)} (hFv : Fv ∈ (Hs dim) (m + 1))
    (heq : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient v x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), Fv x * φ x) (k : Fin dim) :
    AEIn ((Hs dim) (m + 2)) (fun x => W1p.gradient v x k) := by
  obtain ⟨V2, hV2'⟩ := exists_lowerTo m V'
  have hV2 : Wkp.lowerOrder 1 V2 = v := hV2'.trans hV'
  obtain ⟨Fw, hFw, hFwH⟩ := exists_w1p_of_mem_Hs m hFv
  have heq' : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient (Wkp.lowerOrder 1 V2) x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), W1p.value Fw x * φ x := by
    intro φ; rw [hV2, hFw]; exact heq φ
  have hdv : ∀ i, AEIn ((Hs dim) (m + 1)) (fun x => W1p.gradient v x i) := fun i => by
    have := aeIn_dv m V' i; rwa [hV'] at this

  have hrot : ∀ j l : Fin dim, j ≠ l → ∀ i, AEIn ((Hs dim) (m + 1))
      (fun x => x j * SD.sd V2 i l x - x l * SD.sd V2 i j x) := by
    intro j l hjl i
    obtain ⟨z₀, hz₀, hz₀v⟩ := BallRotation.exists_rotational_mem_w1p0 hv0 V2 hV2 j l hjl
    obtain ⟨z, hz, M, hM, hzeq⟩ :=
      BallRegularity.exists_diff_equation ha (contDiff_gen j l) (div_gen j l) V2 Fw heq'
    have hzz : z = z₀ := by
      apply W1p.ext_value; apply Lp.ext
      filter_upwards [hz, hz₀v] with x h1 h2
      rw [h1, h2, hV2]
    subst hzz
    obtain ⟨G, hG, hGe⟩ := exists_rhs m V' V2 hV2' hM (contDiff_gen j l) hFwH
    have htest : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
            (W1p.gradient z x) = ∫ x in ((fixedBallOpens dim) : Set (X dim)), G x * φ x :=
      fun φ => (hzeq φ).trans (hGe φ)
    have hzm := ih G hG z hz₀ (eq_of_testFunction ha.continuous htest)
    obtain ⟨Z, hZ⟩ := exists_of_value_mem_Hs (m + 1) z hzm
    have hgz : AEIn ((Hs dim) (m + 1)) (fun x => W1p.gradient z x i) := by
      have := aeIn_partial (m + 1) Z i; rwa [hZ] at this
    have htan := SD.gradient_tangential V2 j l (z := z) (by
      filter_upwards [hz] with x hx
      rw [hx, inner_gen]) i
    have hcomb := aeIn_add (aeIn_sub hgz
      (aeIn_mulc (m + 1) (contDiff_const (c := if i = j then (1 : ℝ) else 0)) (hdv l)))
      (aeIn_mulc (m + 1) (contDiff_const (c := if i = l then (1 : ℝ) else 0)) (hdv j))
    refine aeIn_congr (P := (Hs dim) (m + 1)) (f := fun x => W1p.gradient z x i -
      (if i = j then (1 : ℝ) else 0) * W1p.gradient v x l +
      (if i = l then (1 : ℝ) else 0) * W1p.gradient v x j) ?_ ?_
    · simpa only [sub_eq_add_neg] using hcomb
    · filter_upwards [htan] with x hx
      rw [hx, hV2]
      split_ifs <;> ring

  let D : Fin dim → Fin dim → (L2B dim) := fun i l =>
    (EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).compLp (W1p.gradient (SD.dv V2 l))
  have hD : ∀ i l, ⇑(D i l) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] SD.sd V2 i l :=
    fun i l => ContinuousLinearMap.coeFn_compLp _ _
  have hvz' : ∀ᵐ x ∂(volume : Measure (X dim)).restrict (fixedBallOpens dim),
      ‖x‖ < 3 / 4 → W1p.value (Wkp.lowerOrder 1 V2) x = 0 := by rw [hV2]; exact hvz
  have hmem := mem_of_algebra (P := (Hs dim) (m + 1))
    (fun ψ hψ hc g hg => aeIn_mul (m + 1) hψ hc hg) ha hac hlam hell D
    (fun i l => Lp.ext ((hD i l).trans ((SD.sd_symm V2 i l).trans (hD l i).symm)))
    (fun i l => by
      filter_upwards [hD i l, SD.sd_eq_zero V2 hvz' i l] with x h1 h2 hx
      rw [h1, h2 hx])
    (fun i j l => by
      by_cases hjl : j = l
      · subst hjl
        refine ⟨0, ((Hs dim) (m + 1)).zero_mem, ?_⟩
        filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))] with x hx
        rw [hx]; simp
      · refine aeIn_congr (hrot j l hjl i) ?_
        filter_upwards [hD i l, hD i j] with x h1 h2
        rw [h1, h2])
    (by
      have hsf := SD.strong_form V2 ha (F := Fv) (fun φ => by rw [hV2]; exact heq φ)
      have hrhs : AEIn ((Hs dim) (m + 1)) (fun x => -Fv x - ∑ i, ∑ l,
          fderiv ℝ (fun y => a y i l) x (EuclideanSpace.single i 1) *
            W1p.gradient (Wkp.lowerOrder 1 V2) x l) := by
        refine aeIn_sub (aeIn_neg (aeIn_of_mem hFv)) (aeIn_sum _ fun i _ => aeIn_sum _ fun l _ => ?_)
        have hd : ContDiff ℝ ∞
            (fun x => fderiv ℝ (fun y => a y i l) x (EuclideanSpace.single i 1)) :=
          ((contDiff_matrix_entry ha i l).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
        rw [hV2]
        exact aeIn_mulc (m + 1) hd (hdv l)
      refine aeIn_congr hrhs ?_
      filter_upwards [hsf, ae_all_iff.mpr fun i => ae_all_iff.mpr fun l => hD i l] with x h1 h2
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      rw [h2 i l])
  have hdk : W1p.value (SD.dv V2 k) ∈ (Hs dim) (m + 2) := by
    refine value_mem_Hs_of_partials (m + 1) (SD.dv V2 k) fun i => ?_
    exact aeIn_congr (aeIn_of_mem (hmem i k)) (hD i k |>.trans (by rfl))
  refine aeIn_congr (aeIn_of_mem hdk) ?_
  filter_upwards [SD.value_dv V2 k] with x hx
  rw [hx, hV2]

theorem eq_sub {A : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (hA : Continuous A)
    {u w v : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2} {F G : (L2B dim)} {gw : (X dim) → (X dim)}
    (hgv : ⇑(W1p.gradient v) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => W1p.gradient u x - W1p.gradient w x)
    (hwg : ⇑(W1p.gradient w) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] gw)
    (hu : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (A x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient u x) = ∫ x in ((fixedBallOpens dim) : Set (X dim)), F x * φ x)
    (hw : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (A x) (gradient (φ : (X dim) → ℝ) x) (gw x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), G x * φ x) (φ : 𝓓((fixedBallOpens dim), ℝ)) :
    ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (A x) (gradient (φ : (X dim) → ℝ) x)
        (W1p.gradient v x) = ∫ x in ((fixedBallOpens dim) : Set (X dim)), (F - G) x * φ x := by
  have hgφ := gradientTestFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2 φ
  have e1 : ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (A x) (gradient (φ : (X dim) → ℝ) x)
        (W1p.gradient v x) =
      (∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (A x)
        (gradientTestFunctionLp (mu := (volume : Measure (X dim))) 2 φ x) (W1p.gradient u x)) -
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (A x)
        (gradientTestFunctionLp (mu := (volume : Measure (X dim))) 2 φ x) (W1p.gradient w x) := by
    refine (integral_congr_ae ?_).trans (integral_sub
      (integrable_mbf hA (W1p.gradient u) (gradientTestFunctionLp 2 φ))
      (integrable_mbf hA (W1p.gradient w) (gradientTestFunctionLp 2 φ)))
    filter_upwards [hgφ, hgv] with x h1 h2
    rw [h1, h2, map_sub]
  have e2 : ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (A x)
      (gradientTestFunctionLp (mu := (volume : Measure (X dim))) 2 φ x) (W1p.gradient u x) =
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), F x * φ x := by
    rw [← hu φ]
    refine integral_congr_ae ?_
    filter_upwards [hgφ] with x h1
    rw [h1]
  have e3 : ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (A x)
      (gradientTestFunctionLp (mu := (volume : Measure (X dim))) 2 φ x) (W1p.gradient w x) =
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), G x * φ x := by
    rw [← hw φ]
    refine integral_congr_ae ?_
    filter_upwards [hgφ, hwg] with x h1 h2
    rw [h1, h2]
  have e4 : ∫ x in ((fixedBallOpens dim) : Set (X dim)), (F - G) x * φ x =
      (∫ x in ((fixedBallOpens dim) : Set (X dim)), F x * φ x) - ∫ x in ((fixedBallOpens dim) : Set (X dim)), G x * φ x := by
    refine (integral_congr_ae ?_).trans (integral_sub
      (integrable_mul_test (aeIn_of_mem (mem_Hs_zero F)) φ)
      (integrable_mul_test (aeIn_of_mem (mem_Hs_zero G)) φ))
    filter_upwards [Lp.coeFn_sub F G] with x hx
    rw [hx, Pi.sub_apply, sub_mul]
  rw [e1, e2, e3, e4]

theorem regAt_zero {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} {lam Lam : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ a (closedBall 0 2))
    (hell : UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim)) a lam Lam) : RegAt a 0 :=
  fun _ _ w hw heq => by
    obtain ⟨U, hU⟩ := exists_H2 hsmooth hell hw heq
    rw [← hU]
    exact mem_Hs.mpr ⟨U, by rw [Wkp.value_succ, Wkp.value_one]⟩

theorem regAt_succ {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} {lam Lam : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ a (closedBall 0 2))
    (hell : UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim)) a lam Lam) (m : ℕ) (ih : RegAt a m) :
    RegAt a (m + 1) := by
  intro F hF u hu0 hu
  have hum := ih F (Hs_succ_le _ hF) u hu0 hu
  obtain ⟨U, hU⟩ := exists_of_value_mem_Hs (m + 1) u hum
  obtain ⟨â, hâ, hâa, hâc⟩ := exists_smooth_extension hsmooth
  have hlam : 0 < lam := hell.1
  have hB : ∀ x ∈ ((fixedBallOpens dim) : Set (X dim)), â x = a x := fun x hx => hâa x (by
    have : ‖x‖ < 1 := by simpa [fixedBallOpens] using hx
    simp only [mem_closedBall, dist_zero_right]; linarith)
  have hmeas : MeasurableSet ((fixedBallOpens dim) : Set (X dim)) := (fixedBallOpens dim).isOpen.measurableSet
  have ihâ : RegAt â m := regAt_congr (fun x hx => (hB x hx).symm) ih
  have huâ : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (â x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient u x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), F x * φ x := by
    intro φ
    rw [← testFunction_of_eq hu φ]
    exact setIntegral_congr_fun hmeas fun x hx => by rw [hB x hx]
  have hellâ : ∀ x ∈ ((fixedBallOpens dim) : Set (X dim)), ∀ ξ : (X dim),
      lam * ‖ξ‖ ^ 2 ≤ matrixBilinearForm (â x) ξ ξ := by
    intro x hx ξ
    have := (hell.2.2 hx).1 ξ
    rwa [Matrix.toQuadraticForm'_apply, ← hB x hx, ← matrixBilinearForm_apply] at this

  let ζ := bump (dim := dim) (3 / 4) (13 / 16) (by norm_num) (by norm_num)
  have hζB : tsupport ζ ⊆ ((fixedBallOpens dim) : Set (X dim)) := fun x hx => by
    rw [ζ.tsupport_eq] at hx
    have : ‖x‖ ≤ 13 / 16 := by simpa [ζ] using hx
    simp only [fixedBallOpens, TopologicalSpace.Opens.coe_mk, mem_ball, dist_zero_right]; linarith
  obtain ⟨M, hM, hζM, hgM⟩ :=
    ((ζ.contDiff (n := ⊤)).of_le (by simp)).exists_abs_le_and_norm_gradient_le ζ.hasCompactSupport
  have hwv := W1p.value_contDiffSMul_ae ζ.contDiff hM (fun x _ => hζM x) (fun x _ => hgM x) u
  have hwg := W1p.gradient_contDiffSMul_ae ζ.contDiff hM (fun x _ => hζM x) (fun x _ => hgM x) u
  have hwζ0 := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (p := 2) (by norm_num)
    ζ.contDiff hM (fun x _ => hζM x) (fun x _ => hgM x) ζ.hasCompactSupport hζB u
  generalize W1p.contDiffSMul ζ ζ.contDiff hM (fun x _ => hζM x) (fun x _ => hgM x) u = wζ
    at hwv hwg hwζ0
  obtain ⟨Fζ, hFζe, hFζ⟩ := exists_localized_forcing_eq hâ huâ (ζ.contDiff (n := ⊤))
  have hFζH : Fζ ∈ (Hs dim) (m + 1) := by
    refine mem_of_aeIn (aeIn_congr ?_ hFζe.symm)
    have := aeIn_locForcing m hâ (ζ.contDiff (n := ⊤)) hF U
    rwa [hU] at this
  have hU' : u = Wkp.firstOrder (m + 1) U := hU.symm

  have hint : ∀ k, AEIn ((Hs dim) (m + 2)) (fun x => W1p.gradient wζ x k) := by
    intro k
    refine interior_step m hâ ihâ U (ζ.contDiff (n := ⊤)) hζB ζ.hasCompactSupport hFζH wζ ?_ ?_ ?_ k
    · filter_upwards [hwv] with x hx; rw [hx, ← hU', smul_eq_mul]
    · filter_upwards [hwg] with x hx; rw [hx, ← hU']
    · intro φ; rw [← hU']; exact hFζ φ

  obtain ⟨v, hvdef⟩ : ∃ v, v = u - wζ := ⟨_, rfl⟩
  have hv0 : v ∈ w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2 := by
    rw [hvdef]; exact (w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2).toSubmodule.sub_mem hu0 hwζ0
  obtain ⟨Wn, hWn⟩ := exists_of_value_mem_Hs (m + 1) wζ (value_mul_mem_Hs m (ζ.contDiff (n := ⊤)) U
    (by filter_upwards [hwv] with x hx; rw [hx, ← hU', smul_eq_mul]))
  have hV' : Wkp.firstOrder (m + 1) (U - Wn) = v := by
    apply W1p.ext_value
    have h1 : Wkp.value (m + 1 + 1) (U - Wn) = Wkp.value (m + 1 + 1) U - Wkp.value (m + 1 + 1) Wn :=
      map_sub (Wkp.valueL (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) (m + 1 + 1))
        U Wn
    rw [Wkp.value_firstOrder, h1, ← Wkp.value_firstOrder, ← Wkp.value_firstOrder, hU, hWn, hvdef]
    simp only [← W1p.valueL_apply, map_sub]
  have hgv : ⇑(W1p.gradient v) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => W1p.gradient u x - W1p.gradient wζ x := by
    have : W1p.gradient v = W1p.gradient u - W1p.gradient wζ := by
      simp only [hvdef, ← W1p.gradientL_apply, map_sub]
    rw [this]
    exact Lp.coeFn_sub _ _
  have hvz : ∀ᵐ x ∂(volume : Measure (X dim)).restrict (fixedBallOpens dim),
      ‖x‖ < 3 / 4 → W1p.value v x = 0 := by
    have : W1p.value v = W1p.value u - W1p.value wζ := by
      simp only [hvdef, ← W1p.valueL_apply, map_sub]
    rw [this]
    filter_upwards [Lp.coeFn_sub (W1p.value u) (W1p.value wζ), hwv] with x h1 h2 hx
    rw [h1, Pi.sub_apply, h2, ζ.one_of_mem_closedBall (by simp [ζ]; linarith), one_smul, sub_self]
  have heqv := eq_sub hâ.continuous hgv hwg huâ (by
    intro φ; exact hFζ φ)
  have hbd : ∀ k, AEIn ((Hs dim) (m + 2)) (fun x => W1p.gradient v x k) := fun k =>
    boundary_step m hâ hâc hlam hellâ ihâ hv0 (U - Wn) hV' hvz
      (((Hs dim) (m + 1)).sub_mem hF hFζH) heqv k

  refine value_mem_Hs_of_partials (m + 2) u fun k => ?_
  refine aeIn_congr (aeIn_add (hint k) (hbd k)) ?_
  filter_upwards [hgv] with x hx
  rw [hx]
  simp

end CalderonN.BallRegularity.HO
