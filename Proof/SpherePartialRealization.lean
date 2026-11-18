import Proof.OutputRealization
import Proof.HarmonicCoordinateFields
import Proof.HarmonicTruncation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

structure SpherePartialRealization (U V : X → SphereL2) (S : Set X) where
  field : ℕ → X × UnitSphere → ℂ
  continuous : ∀ n,Continuous (field n)
  zero : ∀ n y,y ∉ S → ∀ v,field n (y,v) = 0
  realAE : ∀ n y,harmonicPartialSum n (U y) =ᵐ[sphereProbability] (fun v => (field n (y,v)).re)
  imagAE : ∀ n y,harmonicPartialSum n (V y) =ᵐ[sphereProbability] (fun v => (field n (y,v)).im)

theorem exists_spherePartialRealization (U V : X → SphereL2) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hzeroU : ∀ y ∉ S,U y = 0) (hzeroV : ∀ y ∉ S,V y = 0) :
    Nonempty (SpherePartialRealization U V S) := by
  classical
  choose dim b c d hb hc hd hcc hcd hsc hsd hrc hrd using
    fun k => exists_common_harmonic_coordinates k U V hU hV S hS hzeroU hzeroV
  let R (n : ℕ) (z : X × UnitSphere) : ℝ := ∑ k ∈ Finset.range n,∑ j,c k z.1 j*(polynomialSphere (b k j)) z.2
  let J (n : ℕ) (z : X × UnitSphere) : ℝ := ∑ k ∈ Finset.range n,∑ j,d k z.1 j*(polynomialSphere (b k j)) z.2
  let G (n : ℕ) (z : X × UnitSphere) : ℂ := Complex.mk (R n z) (J n z)
  have hR (n : ℕ) : Continuous (R n) := by
    apply continuous_finsetSum
    intro k _
    exact continuous_finsetSum _ (fun j _ => (((continuous_apply j).comp (hc k).continuous).comp continuous_fst).mul
      ((polynomialSphere (b k j)).continuous.comp continuous_snd))
  have hJ (n : ℕ) : Continuous (J n) := by
    apply continuous_finsetSum
    intro k _
    exact continuous_finsetSum _ (fun j _ => (((continuous_apply j).comp (hd k).continuous).comp continuous_fst).mul
      ((polynomialSphere (b k j)).continuous.comp continuous_snd))
  refine ⟨⟨G,fun n => Complex.equivRealProdCLM.symm.continuous.comp ((hR n).prodMk (hJ n)),?_,?_,?_⟩⟩
  · intro n y hy v
    have hzC (k : ℕ) : c k y = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hy (hsc k hs))
    have hzD (k : ℕ) : d k y = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hy (hsd k hs))
    simp only [G,R,J,hzC,hzD,Pi.zero_apply,zero_mul,Finset.sum_const_zero]
    rfl
  · intro n y
    rw [harmonicPartialSum_eq_sum]
    have h := sphereL2_sum_ae (Finset.range n) (fun k => (harmonicProjection k (U y) : SphereL2))
      (fun k v => ∑ j,c k y j*(polynomialSphere (b k j)) v) (fun k _ => by
        rw [← hrc k y]
        have hrep := (polynomialSphere (finitePolynomialField (b k) (c k) y)).coeFn_toLp (p:=2) (𝕜:=ℝ) sphereProbability
        apply hrep.trans
        apply Filter.Eventually.of_forall
        intro v
        simp [polynomialSphere,finitePolynomialField])
    exact h
  · intro n y
    rw [harmonicPartialSum_eq_sum]
    have h := sphereL2_sum_ae (Finset.range n) (fun k => (harmonicProjection k (V y) : SphereL2))
      (fun k v => ∑ j,d k y j*(polynomialSphere (b k j)) v) (fun k _ => by
        rw [← hrd k y]
        have hrep := (polynomialSphere (finitePolynomialField (b k) (d k) y)).coeFn_toLp (p:=2) (𝕜:=ℝ) sphereProbability
        apply hrep.trans
        apply Filter.Eventually.of_forall
        intro v
        simp [polynomialSphere,finitePolynomialField])
    exact h

lemma integral_complex_norm_sq_components (F : UnitSphere → ℂ) (U V : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v => (F v).re))
    (hIm : V =ᵐ[sphereProbability] (fun v => (F v).im)) :
    (∫ v,‖F v‖^2 ∂sphereProbability) = ‖U‖^2+‖V‖^2 := by
  have heq : (fun v => ‖F v‖^2) =ᵐ[sphereProbability] fun v => (U v)^2+(V v)^2 := by
    filter_upwards [hRe,hIm] with v hr hi
    rw [Complex.sq_norm,Complex.normSq_apply,← hr,← hi]
    ring
  rw [integral_congr_ae heq,integral_add (integrable_square_L2 U) (integrable_square_L2 V),
    integral_square_L2,integral_square_L2]

lemma SpherePartialRealization.fiber_square {U V : X → SphereL2} {S : Set X}
    (A : SpherePartialRealization U V S) (n : ℕ) (y : X) :
    (∫ v,‖A.field n (y,v)‖^2 ∂sphereProbability) =
      ‖harmonicPartialSum n (U y)‖^2+‖harmonicPartialSum n (V y)‖^2 :=
  integral_complex_norm_sq_components _ _ _ (A.realAE n y) (A.imagAE n y)

end ShrinkingSpheres
