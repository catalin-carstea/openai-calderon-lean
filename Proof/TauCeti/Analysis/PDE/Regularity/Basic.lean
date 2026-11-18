/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.PDE.DirichletProblem
public import Proof.TauCeti.Analysis.Sobolev.Wkp.SecondOrder
public import Proof.TauCeti.Analysis.Sobolev.W1p.DifferenceQuotient
import Proof.TauCeti.Analysis.Sobolev.DifferenceQuotient
import Proof.TauCeti.Analysis.Sobolev.W1p.Density

 


































































public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {A : Matrix ι ι ℝ} {lam : ℝ}

omit [DecidableEq ι] in
 



theorem energyFormH1_translate (A : Matrix ι ι ℝ) {h k : EuclideanSpace ℝ ι} (hk : h + k = 0)
    (u v : W1p mu ⊤ 2) :
    energyFormH1 (fun _ => A) 0 0 (W1p.translate (Set.mapsTo_univ (· + h) _) u) v
      = energyFormH1 (fun _ => A) 0 0 u (W1p.translate (Set.mapsTo_univ (· + k) _) v) := by
  rw [energyFormH1_const_eq_setIntegral, energyFormH1_const_eq_setIntegral]
   
  have hinv : ∀ F : EuclideanSpace ℝ ι → ℝ,
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F (x + h) ∂mu
        = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F x ∂mu := by
    intro F
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact integral_add_right_eq_self F h
  have hcancel : ∀ x : EuclideanSpace ℝ ι, x + h + k = x := fun x => by
    rw [add_assoc, hk, add_zero]
  calc ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
        matrixBilinearForm A (W1p.gradient v x)
          (W1p.gradient (W1p.translate (Set.mapsTo_univ (· + h) _) u) x) ∂mu
      = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm A (W1p.gradient v (x + h + k))
            (W1p.gradient u (x + h)) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_translate_ae (Set.mapsTo_univ (· + h) _) u] with x hx
        rw [hx, hcancel]
    _ = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm A (W1p.gradient v (x + k)) (W1p.gradient u x) ∂mu :=
        hinv fun y => matrixBilinearForm A (W1p.gradient v (y + k)) (W1p.gradient u y)
    _ = ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)),
          matrixBilinearForm A (W1p.gradient (W1p.translate (Set.mapsTo_univ (· + k) _) v) x)
            (W1p.gradient u x) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_translate_ae (Set.mapsTo_univ (· + k) _) v] with x hx
        rw [hx]

omit [DecidableEq ι] in
 







theorem energyFormH1_differenceQuotient_eq_neg (A : Matrix ι ι ℝ) (w : EuclideanSpace ℝ ι)
    (t : ℝ) (u v : W1p mu ⊤ 2) :
    energyFormH1 (fun _ => A) 0 0
        (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u) v
      = -energyFormH1 (fun _ => A) 0 0 u
        (W1p.differenceQuotient le_rfl w (-t) (Set.mapsTo_univ (· + (-t) • w) _) v) := by
  have hcoeff : MemLp (fun x => energyIntegrand ((fun _ => A) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
    simpa using memLp_top_const (α := EuclideanSpace ℝ ι)
      (μ := mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
      (energyIntegrand A 0 0)
   
   
  have hleft : ∀ (s : ℝ) (hs : MapsTo (· + s • w)
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) (x y : W1p mu ⊤ 2),
      energyFormH1 (fun _ => A) 0 0 (W1p.differenceQuotient le_rfl w s hs x) y
        = s⁻¹ * (energyFormH1 (fun _ => A) 0 0 (W1p.translate hs x) y
            - energyFormH1 (fun _ => A) 0 0 x y) := by
    intro s hs x y
    rw [W1p.differenceQuotient_def, W1p.restrictL_self, ← energyFormH1L_apply hcoeff]
    simp only [map_smul, map_sub, smul_apply, sub_apply, energyFormH1L_apply, smul_eq_mul]
  have hright : ∀ (s : ℝ) (hs : MapsTo (· + s • w)
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) (x y : W1p mu ⊤ 2),
      energyFormH1 (fun _ => A) 0 0 x (W1p.differenceQuotient le_rfl w s hs y)
        = s⁻¹ * (energyFormH1 (fun _ => A) 0 0 x (W1p.translate hs y)
            - energyFormH1 (fun _ => A) 0 0 x y) := by
    intro s hs x y
    rw [W1p.differenceQuotient_def, W1p.restrictL_self, ← energyFormH1L_apply hcoeff]
    simp only [map_smul, map_sub, energyFormH1L_apply, smul_eq_mul]
  have hk : t • w + (-t) • w = 0 := by rw [← add_smul]; simp
  rw [hleft, hright, energyFormH1_translate A hk, inv_neg]
  ring

omit [DecidableEq ι] in
 










theorem UniformlyEllipticOn.norm_gradient_differenceQuotient_le
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u)
    (w : EuclideanSpace ℝ ι) (t : ℝ) :
    ‖W1p.gradient (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _)
      (u : W1p mu ⊤ 2))‖ ≤ ‖w‖ * ‖f‖ / lam := by
  classical
   
  have hDQ := energyFormH1_differenceQuotient_eq_neg A w t (u : W1p mu ⊤ 2)
    (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) (u : W1p mu ⊤ 2))
  set g := W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) (u : W1p mu ⊤ 2)
  set v := W1p.differenceQuotient le_rfl w (-t) (Set.mapsTo_univ (· + (-t) • w) _) g
   
  have hcoeff : MemLp (fun x => energyIntegrand ((fun _ => A) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
    simpa using memLp_top_const (α := EuclideanSpace ℝ ι)
      (μ := mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
      (energyIntegrand A 0 0)
  have hlow : lam * ‖W1p.gradient g‖ ^ 2 ≤ energyFormH1 (fun _ => A) 0 0 g g := by
    have key := integral_mul_norm_snd_sq_le_energyFormIntegral_zero_drift_self
      (μ := mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
      (a := fun _ => A) (c := fun _ => 0) (U := jetField g)
      (Filter.Eventually.of_forall fun _ ξ => by
        simpa [Matrix.toQuadraticForm'_apply] using hA ξ)
      (by simp) ((integrable_norm_jetField_snd_sq g).const_mul lam)
      (TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff g g)
    rw [← integral_norm_jetField_snd_sq_eq_norm_gradient_sq g, ← integral_const_mul,
      energyFormH1_def]
    rw [energyFormIntegral_def] at key
    exact key
   
  have hv0 : v ∈ w1p0Submodule mu ⊤ 2 := W1p.mem_w1p0Submodule_top (by norm_num) v
  have hsol : energyFormH1 (fun _ => A) 0 0 (u : W1p mu ⊤ 2) v = ⟪f, W1p.value v⟫_ℝ := by
    have h1 := (isWeakSolutionDirichlet_iff f u).mp hu ⟨v, hv0⟩
    rw [← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply] at h1
    exact h1
  rw [hsol] at hDQ
   
  have hdq : ‖W1p.value v‖ ≤ ‖w‖ * ‖W1p.gradient g‖ :=
    W1p.norm_value_differenceQuotient_le (by norm_num) w (-t) g
  have hkey : lam * ‖W1p.gradient g‖ ^ 2 ≤ ‖f‖ * (‖w‖ * ‖W1p.gradient g‖) := by
    refine hlow.trans (hDQ.le.trans ?_)
    refine ((neg_le_abs _).trans (abs_real_inner_le_norm f _)).trans ?_
    gcongr
  rcases eq_or_lt_of_le (norm_nonneg (W1p.gradient g)) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (by positivity) hlam.le
  · rw [le_div_iff₀ hlam]
    nlinarith

omit [DecidableEq ι] in
 







theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u)
    (y w : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      ‖G‖ ≤ ‖y‖ * (‖w‖ * ‖f‖ / lam) ∧
        HasWeakLineDerivOn mu ⊤
          (fun x => ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ) G w := by
  classical
  have hloc : LocallyIntegrableOn
      (fun x => ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ)
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) mu := by
    simpa using
      ((W1p.hasWeakFDerivOn (u : W1p mu ⊤ 2)).hasWeakLineDerivOn y).locallyIntegrableOn_deriv
   
  have hglobal : ∀ t : ℝ, eLpNorm
      (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu ⊤ 2) (x + t • w), y⟫_ℝ
        - ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ)) 2
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
      ≤ ENNReal.ofReal (‖y‖ * (‖w‖ * ‖f‖ / lam)) := by
    intro t
    set g := W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) (u : W1p mu ⊤ 2)
    have hae : (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu ⊤ 2) (x + t • w), y⟫_ℝ
          - ⟪W1p.gradient (u : W1p mu ⊤ 2) x, y⟫_ℝ))
        =ᵐ[mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))]
          fun x => ⟪W1p.gradient g x, y⟫_ℝ := by
      filter_upwards [W1p.gradient_differenceQuotient_ae le_rfl w t (Set.mapsTo_univ (· + t • w) _)
        (u : W1p mu ⊤ 2)] with x hx
      rw [hx, inner_smul_left, inner_sub_left]
      simp [mul_sub]
    rw [eLpNorm_congr_ae hae]
    calc eLpNorm (fun x => ⟪W1p.gradient g x, y⟫_ℝ) 2
          (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))
        ≤ eLpNorm (‖y‖ • (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)) 2
            (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) :=
          have hmeas : AEStronglyMeasurable (fun x => ⟪W1p.gradient g x, y⟫_ℝ)
              (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) :=
            (Lp.aestronglyMeasurable (W1p.gradient g)).inner_const
          eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall fun x => by
            rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, mul_comm]
            exact abs_real_inner_le_norm _ y)
      _ = ‖y‖ₑ * eLpNorm (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
            (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
          rw [eLpNorm_const_smul, enorm_norm]
      _ = ‖y‖ₑ * ENNReal.ofReal ‖W1p.gradient g‖ := by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      _ ≤ ‖y‖ₑ * ENNReal.ofReal (‖w‖ * ‖f‖ / lam) := by
          gcongr
          exact UniformlyEllipticOn.norm_gradient_differenceQuotient_le hlam hA hu w t
      _ = ENNReal.ofReal (‖y‖ * (‖w‖ * ‖f‖ / lam)) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg y)]
  refine exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le hloc w
    (by positivity) fun K hK _ => Filter.Eventually.frequently ?_
  filter_upwards with t
  exact le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono hK le_rfl)) (hglobal t)

omit [DecidableEq ι] in
 




theorem UniformlyEllipticOn.exists_lowerOrder_eq
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {f : Lp ℝ 2 (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)))}
    {u : W1p0 mu ⊤ 2} (hu : IsWeakSolutionDirichlet (fun _ => A) 0 0 f u) :
    ∃ U : Wkp mu ⊤ 2 2, Wkp.lowerOrder 1 U = (u : W1p mu ⊤ 2) := by
  classical
  exact W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn _ (EuclideanSpace.basisFun ι ℝ)
    fun i j => by
      obtain ⟨G, -, hG⟩ := UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient
        hlam hA hu
        (EuclideanSpace.basisFun ι ℝ j) (EuclideanSpace.basisFun ι ℝ i)
      exact ⟨G, hG⟩

end PDE

end TauCeti
