module

public import Proof.CalderonN.SobolevMultiplication
public import Proof.CalderonN.WeakSolutionLocalization
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Zero
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Restriction
import Mathlib.Tactic

public section

/-! The localized forcing from the Calderón fixed-ball solver, with
Sobolev factors read on an arbitrary common open half-space.
Its products have representatives of order `m` as soon as the value and
gradient cut off on a larger set have that order. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal ContDiff Distributions Gradient Matrix.Norms.Elementwise Topology

namespace CalderonPatch
open CalderonN
open TauCeti TauCeti.PDE OAI.AnisotropicCalderon.Regularity
variable {n : ℕ}
local notation "Ω₀" => (⊤ : Opens (X n))
local notation "μ₀" => (volume : Measure (X n))

private theorem smooth_divCoeffGradient {a : X n → Mat n} (ha : ContDiff ℝ ∞ a)
    {ψ : X n → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (divCoeffGradient a ψ) := by
  unfold divCoeffGradient
  apply ContDiff.sum
  intro i _
  let ei := EuclideanSpace.basisFun (Fin n) ℝ i
  have hh := contDiff_coeff_gradient ha hψ ei
  have heq : (fun x => lineDeriv ℝ (fun y => matrixBilinearForm (a y) ei (gradient ψ y)) x ei) =
      fun x => fderiv ℝ (fun y => matrixBilinearForm (a y) ei (gradient ψ y)) x ei :=
    funext fun x => ((hh.differentiable (by simp)) x).lineDeriv_eq_fderiv
  change ContDiff ℝ ∞ (fun x => lineDeriv ℝ (fun y => matrixBilinearForm (a y) ei (gradient ψ y)) x ei)
  rw [heq]
  exact (hh.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem locForcing_eq_coordinate_sum {a : X n → Mat n} (ψ : X n → ℝ)
    {V : Opens (X n)} (F : Lp ℝ 2 ((μ₀).restrict V)) (u : W1p μ₀ V 2)
    (x : X n) : locForcing a ψ F u x =
      ψ x * F x - (∑ j, (∑ i, (a x j i + a x i j) * gradient ψ x i) * W1p.gradient u x j) -
        divCoeffGradient a ψ x * W1p.value u x := by
  simp only [locForcing, mbf_eq_sum]
  have hSwap : (∑ i, ∑ j, gradient ψ x i * (a x i j * W1p.gradient u x j)) =
      ∑ j, ∑ i, gradient ψ x i * (a x i j * W1p.gradient u x j) := Finset.sum_comm
  rw [hSwap]
  have hmerge :
      (∑ j, ∑ i, W1p.gradient u x j * (a x j i * gradient ψ x i)) +
        (∑ j, ∑ i, gradient ψ x i * (a x i j * W1p.gradient u x j)) =
      ∑ j, (∑ i, (a x j i + a x i j) * gradient ψ x i) * W1p.gradient u x j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [← hmerge]
  ring


set_option maxHeartbeats 4500000 in
theorem exists_sobolev_localized_forcing_on
    {V H : Opens (X n)} {a : X n → Mat n} (ha : ContDiff ℝ ∞ a)
    {f : X n → ℝ} (hf : ContDiff ℝ ∞ f)
    (F : Lp ℝ 2 ((μ₀).restrict V)) (hF : ⇑F =ᵐ[(μ₀).restrict V] f)
    (u : W1p μ₀ V 2)
    {ψ η : X n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψV : tsupport ψ ∩ H ⊆ V)
    (hη : ∀ x ∈ tsupport ψ, η =ᶠ[𝓝 x] fun _ => 1)
    (m : ℕ) (W : Wkp μ₀ H 2 (m + 1))
    (hWv : ∀ᵐ x ∂(μ₀).restrict H, W1p.value (Wkp.firstOrder m W) x =
      (V : Set (X n)).indicator (fun y => η y * W1p.value u y) x)
    (hWg : ∀ᵐ x ∂(μ₀).restrict H, W1p.gradient (Wkp.firstOrder m W) x =
      (V : Set (X n)).indicator (fun y => η y • W1p.gradient u y +
        W1p.value u y • gradient η y) x) :
    ∃ Y : Wkp μ₀ H 2 m,
      ⇑(Wkp.value m Y) =ᵐ[(μ₀).restrict H] (V : Set (X n)).indicator (locForcing a ψ F u) := by
  classical
  let α (j : Fin n) (x : X n) := ∑ i, (a x j i + a x i j) * gradient ψ x i
  let δ := divCoeffGradient a ψ
  have hα (j : Fin n) : ContDiff ℝ ∞ (α j) := by
    refine ContDiff.sum fun i _ => ?_
    refine ((contDiff_matrix_entry ha j i).add (contDiff_matrix_entry ha i j)).mul ?_
    exact (EuclideanSpace.proj i : X n →L[ℝ] ℝ).contDiff.comp (hψ.gradient_right (m := ∞) (by simp))
  have hα0 (j : Fin n) {x : X n} (hx : x ∉ tsupport ψ) : α j x = 0 := by
    simp [α, gradient_of_notMem_tsupport hx]
  have hαc (j : Fin n) : HasCompactSupport (α j) :=
    hψc.mono' (fun _ h => by by_contra hh; exact h (hα0 j hh))
  have hδ : ContDiff ℝ ∞ δ := smooth_divCoeffGradient ha hψ
  have hδ0 {x : X n} (hx : x ∉ tsupport ψ) : δ x = 0 :=
    divCoeffGradient_eq_zero_of_notMem_tsupport ha hψ hx
  have hδc : HasCompactSupport δ :=
    hψc.mono' (fun _ h => by by_contra hh; exact h (hδ0 hh))
  let χ : 𝓓(Ω₀, ℝ) :=
    ⟨fun x => ψ x * f x, hψ.mul hf, hψc.mul_right, fun _ _ => mem_univ _⟩
  let Z₀ : Wkp μ₀ Ω₀ 2 m := Wkp.ofTestFunctionₗ (mu := μ₀) (p := 2) m χ
  let Z : Wkp μ₀ H 2 m := Wkp.restrictL le_top m Z₀
  have hZ : ⇑(Wkp.value m Z) =ᵐ[(μ₀).restrict H] fun x => ψ x * f x := by
    refine (Wkp.value_restrictL_ae (le_top : H ≤ Ω₀) m Z₀).trans ?_
    have hχ := testFunctionLp_apply_ae (mu := μ₀) 2 χ
    rw [show Wkp.value m Z₀ = testFunctionLp 2 χ from Wkp.value_ofTestFunctionₗ m χ]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_univ (H : Set (X n))) hχ] with x hx
    exact hx.trans rfl
  choose Q hQ using fun j => SobolevMultiplication.exists_mul m (hα j) (hαc j) (WkpCalculus.d j m W)
  obtain ⟨R,hR⟩ := SobolevMultiplication.exists_mul m hδ hδc (Wkp.lowerOrder m W)
  let S := ∑ j, Q j
  have hSum : ⇑(Wkp.value m S) =ᵐ[(μ₀).restrict H] fun x => ∑ j, Wkp.value m (Q j) x := by
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j => Wkp.valueL m (Q j))
    simpa only [S, ← Wkp.valueL_apply, map_sum] using hs
  have hQ' := ae_all_iff.2 hQ
  have hWV := ae_all_iff.2 fun j => WkpCalculus.value_d j m W
  have hSub₁ := Lp.coeFn_sub (Wkp.value m Z) (Wkp.value m S)
  have hSub₂ := Lp.coeFn_sub (Wkp.value m (Z - S)) (Wkp.value m R)
  have hF' := (ae_restrict_iff' V.isOpen.measurableSet).1 hF
  have hVS (A B : Wkp μ₀ H 2 m) : Wkp.value m (A - B) = Wkp.value m A - Wkp.value m B := by
    simp only [← Wkp.valueL_apply, map_sub]
  refine ⟨Z - S - R, ?_⟩
  filter_upwards [hZ, hSum, hQ', hWV, hR,
    hSub₁, hSub₂, ae_restrict_of_ae hF', hWv, hWg, ae_restrict_mem H.isOpen.measurableSet]
    with x hz hs hq hD hr h₁ h₂ hfx hv hg hxH
  rw [hVS, h₂, Pi.sub_apply, hVS, h₁, Pi.sub_apply, hz, hs, hr]
  simp only [hq, hD, ← Wkp.value_succ, ← Wkp.value_firstOrder, hv, hg]
  by_cases hx : x ∈ tsupport ψ
  · have hxV := hψV ⟨hx,hxH⟩
    have hη1 : η x = 1 := (hη x hx).eq_of_nhds
    have hηg : gradient η x = 0 := by
      unfold gradient
      rw [(hη x hx).fderiv_eq]
      simp
    simp only [indicator_of_mem hxV, hη1, one_mul, one_smul, hηg, smul_zero, add_zero, ← hfx hxV]
    exact (locForcing_eq_coordinate_sum ψ F u x).symm
  · have hz : locForcing a ψ F u x = 0 := locForcing_eq_zero_of_notMem_tsupport ha hψ F u hx
    simp [image_eq_zero_of_notMem_tsupport hx, hα0 _ hx, hδ0 hx, indicator_apply, hz]

end CalderonPatch
