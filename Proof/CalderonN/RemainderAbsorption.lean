module

public import Proof.CalderonN.SmoothModelCoercivity
public import Proof.CalderonN.SmoothEnergyRegularity

import Mathlib.Tactic

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The exact frozen four-term density controls the H¹ mass with the square of the
    admitted profile floor. This is independent of the radius construction. -/
lemma Profile.sobolev_one_density_le {Y : Set (X dim)} {g : (MetricField dim)} {e : (Frame dim)} {r : (X dim) → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 0 ≤ floor)
    (φ : (Field dim)) {y : (X dim)} (hy : y ∈ Y) :
    floor^2*(metricDensity g y*sobolevSq g e 1 y (fun w => φ (y,w))) ≤ physicalEnergyDensity g e r φ y := by
  have hb : 0 ≤ beta g r y := Real.sqrt_nonneg _
  have hβ := (hp.2 y hy).2.1
  have hfβ : floor^2 ≤ (beta g r y)^2 := (sq_le_sq₀ hfloor hb).mpr hβ
  have hH : 0 ≤ ∑ i,fiberSq e y (fun w => horizontal g φ y w (e y i)) := Finset.sum_nonneg (fun _ _ => fiberSq_nonneg e y _)
  have hHs : 0 ≤ ∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)) := Finset.sum_nonneg (fun _ _ => sobolevSq_nonneg g e _ y _)
  have hhalf := mul_nonneg (inv_nonneg.mpr hb) hHs
  have hthree := mul_nonneg hb (sobolevSq_nonneg g e (3/2) y (fun w => φ (y,w)))
  have hmass := mul_le_mul_of_nonneg_right hfβ (sobolevSq_nonneg g e 1 y (fun w => φ (y,w)))
  have hinside : floor^2*sobolevSq g e 1 y (fun w => φ (y,w)) ≤
      (∑ i,fiberSq e y (fun w => horizontal g φ y w (e y i)))+
        (beta g r y)^2*sobolevSq g e 1 y (fun w => φ (y,w))+
        (beta g r y)⁻¹*(∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)))+
        beta g r y*sobolevSq g e (3/2) y (fun w => φ (y,w)) := by linarith
  have hweighted := mul_le_mul_of_nonneg_left hinside (show 0 ≤ metricDensity g y from Real.sqrt_nonneg _)
  simpa only [physicalEnergyDensity,mul_left_comm,mul_assoc] using hweighted

lemma Profile.sobolev_one_mass_le (hn : 3 ≤ dim) {Y : Set (X dim)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField dim)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame dim))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X dim) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hfloor : 1 ≤ floor) {φ : (Field dim)} (hφ : Test Y g e φ) :
    floor^2*(∫ y in Y,metricDensity g y*sobolevSq g e 1 y (fun w => φ (y,w))) ≤ energySq Y g e r φ := by
  rw [← integral_const_mul,energySq_eq_integral_density]
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun y => mul_nonneg (sq_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (sobolevSq_nonneg g e _ y _))))
    (hp.integrableOn_physicalEnergyDensity hn hY h hK e he hframe hfloor hφ)
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  exact hp.sobolev_one_density_le (zero_le_one.trans hfloor) φ hy

lemma energyNorm_sq (Y : Set (X dim)) (d : Data dim) (φ : Field dim) :
    (energyNorm Y d φ)^2 = energySq Y d.γ d.frame d.radius φ := by
  unfold energyNorm
  apply Real.sq_sqrt
  rw [energySq_eq_integral_density]
  exact integral_nonneg (physicalEnergyDensity_nonneg _ _ _ _)

/-- A physical complement bounded by the fibre H¹ mass has the inverse-floor
    estimate used to absorb it into the frozen energy. -/
theorem remainder_norm_le_of_sobolev_one (hn : 3 ≤ dim) {Y : Set (X dim)} (hY : IsOpen Y)
    {K : ℝ} {d : Data dim} (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i = j then 1 else 0)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hfloor : 1 ≤ floor) {φ : Field dim} (hφ : Test Y d.γ d.frame φ)
    {J C : ℝ} (hJ₀ : 0 ≤ J) (hC : 0 ≤ C)
    (hJ : J^2 ≤ C^2*(∫ y in Y, metricDensity d.γ y*sobolevSq d.γ d.frame 1 y (fun w => φ (y,w)))) :
    J ≤ C/floor*energyNorm Y d φ := by
  have hf : 0 < floor := zero_lt_one.trans_le hfloor
  have hmass := hp.sobolev_one_mass_le hn hY h hK d.frame he hframe hfloor hφ
  have heq := energyNorm_sq Y d φ
  have hb := mul_le_mul_of_nonneg_left hJ (sq_nonneg floor)
  have hc := mul_le_mul_of_nonneg_left hmass (sq_nonneg C)
  have hsq : (floor*J)^2 ≤ (C*energyNorm Y d φ)^2 := by nlinarith only [hb,hc,heq]
  have hle := (sq_le_sq₀ (mul_nonneg hf.le hJ₀) (mul_nonneg hC (Real.sqrt_nonneg _))).mp hsq
  calc
    J ≤ (C*energyNorm Y d φ)/floor := (le_div_iff₀ hf).mpr (by simpa only [mul_comm, energyNorm] using hle)
    _ = C/floor*energyNorm Y d φ := by ring

/-- The squared model comparison and the complete discarded physical complement
    suffice to obtain the frozen estimate with uniform constants. The premise
    is an internal physical estimate on the same test and the same admissible data. -/
theorem uniformEstimate_of_movingTrace_comparison_on (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hsub : Y ⊆ Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hc₀ : 0 < c₀)
    {F₀ η CE CJ : ℝ} (hη : 0 < η) (hCE : 0 ≤ CE) (hCJ : 0 ≤ CJ)
    (P : Data dim → Prop)
    (compare : ∀ floor ≥ F₀, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → P d → ∀ φ, Test Y d.γ d.frame φ →
      ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      ∃ A : ℝ, 0 ≤ A ∧
        4*(D.raisingSquare-D.loweringSquare) ≤ A^2 + CE*ε*energySq Y d.γ d.frame d.radius φ ∧
        A ≤ traceNorm Y d φ + CJ/floor*energyNorm Y d φ) :
    ∃ floor ε₀ C : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧
      ∀ d ε,0 ≤ ε → ε ≤ ε₀ → Admissible Y Ω K ρ c₀ M Cj floor ε d → P d →
        ∀ φ,Test Y d.γ d.frame φ → energyNorm Y d φ ≤ C*traceNorm Y d φ := by
  let κ := backgroundModeCoercivityConstant c₀
  have hκ : 0 < κ := backgroundModeCoercivityConstant_pos _ hc₀
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  let floor := max (backgroundCoercivityFloor dim hm K M c₀) (max F₀ ((CJ+1)/Real.sqrt κ))
  let ε₀ := min η (κ/(CE+1))
  have hf : 1 ≤ floor := (backgroundCoercivityFloor_ge_one dim hm K M c₀).trans (le_max_left _ _)
  have hε₀ : 0 < ε₀ := lt_min hη (div_pos hκ (by positivity))
  have hJf : CJ/floor ≤ Real.sqrt κ := by
    have hh : (CJ+1)/Real.sqrt κ ≤ floor := (le_max_right _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ (zero_lt_one.trans_le hf)).2
      ((le_add_of_nonneg_right zero_le_one).trans
        (mul_comm floor (Real.sqrt κ) ▸ (div_le_iff₀ hs).1 hh))
  refine ⟨floor, ε₀, 2/Real.sqrt κ, hf, hε₀, div_pos two_pos hs, ?_⟩
  intro d ε hε hsmall hd hP φ hφ
  have hεη := hsmall.trans (min_le_left _ _)
  have hEε : CE*ε ≤ κ := by
    have h := (le_div_iff₀ (by positivity : 0 < CE+1)).1 (hsmall.trans (min_le_right _ _))
    nlinarith
  have hfbg : backgroundCoercivityFloor dim hm K M c₀ ≤ floor := le_max_left _ _
  have hf₀ : F₀ ≤ floor := (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨E,D,hModel⟩ := hd.1.exists_coercive_smooth_model hn hY hΩ hsub
    (zero_lt_one.trans_le hK) hm hd.2.2.2.2.1 hc₀ hfbg hφ
  obtain ⟨A,hA,hGap,hComp⟩ := compare floor hf₀ ε hε hεη d hd hP φ hφ E D
  have he := energyNorm_sq Y d φ
  have hEnergy : 0 ≤ energySq Y d.γ d.frame d.radius φ := he ▸ sq_nonneg _
  have hProd := mul_le_mul_of_nonneg_right hEε hEnergy
  have h3 : 3*κ*energySq Y d.γ d.frame d.radius φ ≤ A^2 := by
    nlinarith only [hModel,hGap,hProd]
  have hASq : ((3/2 : ℝ)*Real.sqrt κ * energyNorm Y d φ)^2 ≤ A^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hκ.le, he]
    nlinarith only [h3,mul_nonneg hκ.le hEnergy]
  have hNorm : 0 ≤ energyNorm Y d φ := Real.sqrt_nonneg _
  have hLeft : 0 ≤ (3/2 : ℝ)*Real.sqrt κ * energyNorm Y d φ := by positivity
  have hStrong := (sq_le_sq₀ hLeft hA).1 hASq
  have hUpper := hComp.trans (add_le_add_right (mul_le_mul_of_nonneg_right hJf hNorm) _)
  have hFinal : energyNorm Y d φ * Real.sqrt κ ≤ 2 * traceNorm Y d φ := by
    linarith only [hStrong,hUpper]
  have hDiv := (le_div_iff₀ hs).2 hFinal
  convert hDiv using 1
  ring

theorem uniformEstimate_of_movingTrace_comparison (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hsub : Y ⊆ Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hc₀ : 0 < c₀)
    {F₀ η CE CJ : ℝ} (hη : 0 < η) (hCE : 0 ≤ CE) (hCJ : 0 ≤ CJ)
    (compare : ∀ floor ≥ F₀, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ, Test Y d.γ d.frame φ →
      ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
      ∃ A : ℝ, 0 ≤ A ∧
        4*(D.raisingSquare-D.loweringSquare) ≤ A^2 + CE*ε*energySq Y d.γ d.frame d.radius φ ∧
        A ≤ traceNorm Y d φ + CJ/floor*energyNorm Y d φ) :
    ∃ floor ε₀ C : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧
      UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C := by
  obtain ⟨floor,ε₀,C,hfloor,hε₀,hC,h⟩ := uniformEstimate_of_movingTrace_comparison_on hn hY hΩ hsub
    hm K ρ c₀ M Cj hK hc₀ hη hCE hCJ (fun _ => True)
    (fun floor hf ε he hs d hd _ => compare floor hf ε he hs d hd)
  exact ⟨floor,ε₀,C,hfloor,hε₀,hC,fun d ε he hs hd => h d ε he hs hd trivial⟩

end CalderonN
