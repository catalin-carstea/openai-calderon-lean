import Proof.GeneralLocalCommonSupportFamily
import Proof.ParallelCoefficientNeighborhood
import Proof.ParallelFirstCoefficientModel
import Proof.UniformParallelFirstCoefficientCenter

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

theorem Background.exists_parallel_coefficient_pair_domain {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (a : X) (r : ℝ) (L : X →L[ℝ] X) (z : X)
    (hv : r • L z ∈ disk g y (R y))
    (hPos : 0 < (parallelFrameNormalMetric g E y a r L (0,z)).det) :
    ∃ S : Set (ℝ × X),IsOpen S ∧ (0,z) ∈ S ∧ ContDiffOn ℝ ∞
      (fun p => (parallelNormalizedFirstCoefficient g g₁ E y a r L p,parallelFirstCoefficientModel g g₁ y a L p)) S := by
  obtain ⟨S,hS,hp,hA,hCenter⟩ := h.exists_parallel_normalized_coefficient_domain hΩ hK hN hy a r L z hv hPos
  refine ⟨S,hS,hp,hA.prodMk ?_⟩
  intro p hp
  have hEll := (h.firstDensityLogDifferential_smooth hK hΩ).contDiffAt (hΩ.mem_nhds (hCenter p hp))
  exact (contDiffAt_parallelFirstCoefficientModel g g₁ y a L p hEll).contDiffWithinAt

/-- Genuine common-support actual coefficient and first model for a parallel
    center path, with their same-witness quadratic derivative estimates. -/
theorem uniform_parallel_coefficient_pair_family {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      ∃ A A1 : ℝ × X → Mat,ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ A1 ∧
      ∃ S : Set X,IsCompact S ∧ (∀ t z,z ∉ S → A (t,z) = 0) ∧ (∀ t z,z ∉ S → A1 (t,z) = 0) ∧
      ∃ V : Set ℝ,IsOpen V ∧ (0:ℝ) ∈ V ∧ (∀ t ∈ V,y+t • a ∈ Y) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) Z,A =ᶠ[𝓝 (t,z)]
        parallelNormalizedFirstCoefficient d.γ d.g₁ d.expMap y a (d.radius y) (frameVectorLinear d.frame y)) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) Z,A1 =ᶠ[𝓝 (t,z)]
        parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y)) ∧
      ∀ z ∈ Metric.closedBall (0:X) Z,∀ b : X,∀ i j,
      let F := fun p => A p i j-(1:Mat) i j-d.radius y*A1 p i j
      |fderiv ℝ F (0,z) (1,0)| ≤ uniformParallelFirstCoefficientCenterBudget hm K M Z*(d.radius y)^2*‖a‖ ∧
      |fderiv ℝ (fderiv ℝ F) (0,z) (0,b) (1,0)| ≤
        uniformParallelFirstCoefficientMixedBudget hm K M Z*(d.radius y)^2*‖a‖*‖b‖ := by
  obtain ⟨ηG,hηG,hGeometry⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηC,hηC,hCenter⟩ := uniform_parallel_first_coefficient_center hY hΩ hm K ρ c₀ M Cj hK hρ Z hZ
  refine ⟨min ηG (min ηE ηC),lt_min hηG (lt_min hηE hηC),?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  let r := d.radius y
  let L := frameVectorLinear d.frame y
  let B0 : ℝ × X → Mat × Mat := fun p =>
    (parallelNormalizedFirstCoefficient d.γ d.g₁ d.expMap y a r L p,parallelFirstCoefficientModel d.γ d.g₁ y a L p)
  let Y0 : Set ℝ := (fun t => y+t • a) ⁻¹' Y
  have hY0 : IsOpen Y0 := hY.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hZero : (0:ℝ) ∈ Y0 := by simpa only [Y0,mem_preimage,zero_smul,add_zero] using hy
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hEll : Elliptic (Metric.closedBall (0:X) Z) (4*K^2)
      (framedNormalMetric d.γ d.frame d.expMap y r) :=
    hElliptic floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy d.γ (by simp)
  have hLocal (z : X) (hz : z ∈ Metric.closedBall (0:X) Z) :
      ∃ S : Set (ℝ × X),IsOpen S ∧ (0,z) ∈ S ∧ ContDiffOn ℝ ∞ B0 S := by
    have hw := frameVector_mem_disk d.γ d.frame y z Z hFrame hz
    have hPack := hGeometry floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy (L z) hw
    have hAt : parallelFrameNormalMetric d.γ d.expMap y a r L (0,z) = framedNormalMetric d.γ d.frame d.expMap y r z :=
      parallelFrameNormalMetric_zero d.γ d.expMap y a r d.frame z
    have hPos : 0 < (parallelFrameNormalMetric d.γ d.expMap y a r L (0,z)).det := by
      rw [hAt];exact (hEll.posDef (by positivity) hz).det_pos
    exact hd.1.exists_parallel_coefficient_pair_domain hΩ hKpos hd.2.1 hy a r L z
      (mem_of_mem_of_subset hPack.1.1 interior_subset) hPos
  choose W hW hHere hBW using hLocal
  let U := ⋃ z,⋃ hz : z ∈ Metric.closedBall (0:X) Z,W z hz
  have hU : IsOpen U := isOpen_iUnion (fun z => isOpen_iUnion (fun hz => hW z hz))
  have hBU : ContDiffOn ℝ ∞ B0 U := by
    intro p hp
    simp only [U,mem_iUnion] at hp
    obtain ⟨z,hz,hp⟩ := hp
    exact ((hBW z hz).contDiffAt ((hW z hz).mem_nhds hp)).contDiffWithinAt
  have hSub : {(0:ℝ)} ×ˢ Metric.closedBall (0:X) Z ⊆ U := by
    rintro ⟨t,z⟩ ⟨ht,hz⟩
    have ht0 : t = 0 := ht
    subst t
    exact mem_iUnion_of_mem z (mem_iUnion_of_mem hz (hHere z hz))
  obtain ⟨B,hB,S,hS,hSupport,V,hV,h0V,hVY,hRep⟩ :=
    exists_local_commonSupport_family_on_open hY0 B0 Z U hU hBU hZero hSub
  let A : ℝ × X → Mat := fun p => (B p).1
  let A1 : ℝ × X → Mat := fun p => (B p).2
  have hA : ContDiff ℝ ∞ A := hB.fst
  have hA1 : ContDiff ℝ ∞ A1 := hB.snd
  have hSupportA : ∀ t z,z ∉ S → A (t,z) = 0 := by
    intro t z hz;change (B (t,z)).1 = 0;rw [hSupport t z hz];rfl
  have hSupportA1 : ∀ t z,z ∉ S → A1 (t,z) = 0 := by
    intro t z hz;change (B (t,z)).2 = 0;rw [hSupport t z hz];rfl
  have hRepA (t : ℝ) (ht : t ∈ V) (z : X) (hz : z ∈ Metric.closedBall (0:X) Z) :
      A =ᶠ[𝓝 (t,z)] parallelNormalizedFirstCoefficient d.γ d.g₁ d.expMap y a r L := by
    filter_upwards [hRep t ht z hz] with p hp
    exact congrArg Prod.fst hp
  have hRepA1 (t : ℝ) (ht : t ∈ V) (z : X) (hz : z ∈ Metric.closedBall (0:X) Z) :
      A1 =ᶠ[𝓝 (t,z)] parallelFirstCoefficientModel d.γ d.g₁ y a L := by
    filter_upwards [hRep t ht z hz] with p hp
    exact congrArg Prod.snd hp
  refine ⟨A,A1,hA,hA1,S,hS,hSupportA,hSupportA1,V,hV,h0V,(fun t ht => hVY ht),hRepA,hRepA1,?_⟩
  intro z hz b i j
  dsimp only
  have hNear : (fun p => A p i j-(1:Mat) i j-r*A1 p i j) =ᶠ[𝓝 (0,z)]
      (fun p => parallelNormalizedFirstCoefficientRemainder d.γ d.g₁ d.expMap y a r L p i j) := by
    filter_upwards [hRepA 0 h0V z hz,hRepA1 0 h0V z hz] with p hp hp1
    rw [hp,hp1,parallelFirstCoefficientModel_remainder]
  rw [hNear.fderiv_eq,hNear.fderiv.fderiv_eq]
  exact hCenter floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy a z hz b i j

end ShrinkingSpheres
