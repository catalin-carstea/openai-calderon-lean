import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

/-- The order-one remainder of two right-multiplied first-order generators. -/
def rightMultiplierWordCommutatorL
    (G H K : Mid →L[ℝ] Lo) (M N CHM CGN : Mid →L[ℝ] Mid) : Mid →L[ℝ] Lo :=
  (K.comp M).comp N-(G.comp CHM).comp N+(H.comp CGN).comp M

/-- The genuine higher-to-lower commutator factors through one inclusion,
provided the SAME scalar multipliers commute and the generator commutators
have their correct gained endpoint realizations. -/
lemma graded_right_multiplier_word_commutator
    (I : Hi →L[ℝ] Mid) (G H K : Mid →L[ℝ] Lo) (Gh Hh : Hi →L[ℝ] Mid)
    (M N CHM CGN : Mid →L[ℝ] Mid) (Mh Nh : Hi →L[ℝ] Hi)
    (hG : G.comp Hh-H.comp Gh=K.comp I)
    (hHM : Hh.comp Mh-M.comp Hh=CHM.comp I)
    (hGN : Gh.comp Nh-N.comp Gh=CGN.comp I)
    (hM : I.comp Mh=M.comp I) (hN : I.comp Nh=N.comp I)
    (hComm : Mh.comp Nh=Nh.comp Mh) :
    (G.comp M).comp (Hh.comp Nh)-(H.comp N).comp (Gh.comp Mh)=
      (rightMultiplierWordCommutatorL G H K M N CHM CGN).comp I := by
  apply ContinuousLinearMap.ext
  intro u
  have hMV (v : Hi) : I (Mh v)=M (I v) := DFunLike.congr_fun hM v
  have hNV (v : Hi) : I (Nh v)=N (I v) := DFunLike.congr_fun hN v
  have hCommV : Nh (Mh u)=Mh (Nh u) := (DFunLike.congr_fun hComm u).symm
  have hHMV : M (Hh (Nh u))=Hh (Mh (Nh u))-CHM (I (Nh u)) := by
    have hh := DFunLike.congr_fun hHM (Nh u)
    change Hh (Mh (Nh u))-M (Hh (Nh u))=CHM (I (Nh u)) at hh
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hh).symm)
  have hGNV : N (Gh (Mh u))=Gh (Nh (Mh u))-CGN (I (Mh u)) := by
    have hh := DFunLike.congr_fun hGN (Mh u)
    change Gh (Nh (Mh u))-N (Gh (Mh u))=CGN (I (Mh u)) at hh
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp hh).symm)
  have hGV : G (Hh (Mh (Nh u)))-H (Gh (Mh (Nh u)))=K (I (Mh (Nh u))) :=
    DFunLike.congr_fun hG (Mh (Nh u))
  change G (M (Hh (Nh u)))-H (N (Gh (Mh u)))=
    (K (M (N (I u)))-G (CHM (N (I u))))+H (CGN (M (I u)))
  rw [hHMV,hGNV,hCommV,map_sub,map_sub]
  simp only [hMV,hNV] at hGV ⊢
  exact (by abel :
    (G (Hh (Mh (Nh u)))-G (CHM (N (I u))))-
      (H (Gh (Mh (Nh u)))-H (CGN (M (I u))))=
    (G (Hh (Mh (Nh u)))-H (Gh (Mh (Nh u))))-
      G (CHM (N (I u)))+H (CGN (M (I u)))).trans (by rw [hGV])
lemma norm_rightMultiplierWordCommutatorL_le
    (G H K : Mid →L[ℝ] Lo) (M N CHM CGN : Mid →L[ℝ] Mid) :
    ‖rightMultiplierWordCommutatorL G H K M N CHM CGN‖ ≤
      ‖K‖*‖M‖*‖N‖+‖G‖*‖CHM‖*‖N‖+‖H‖*‖CGN‖*‖M‖ := by
  have hK := (ContinuousLinearMap.opNorm_comp_le (K.comp M) N).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le K M) (norm_nonneg N))
  have hG := (ContinuousLinearMap.opNorm_comp_le (G.comp CHM) N).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le G CHM) (norm_nonneg N))
  have hH := (ContinuousLinearMap.opNorm_comp_le (H.comp CGN) M).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le H CGN) (norm_nonneg M))
  have hSub := norm_sub_le ((K.comp M).comp N) ((G.comp CHM).comp N)
  have hAdd := norm_add_le ((K.comp M).comp N-(G.comp CHM).comp N) ((H.comp CGN).comp M)
  change ‖(K.comp M).comp N-(G.comp CHM).comp N+(H.comp CGN).comp M‖ ≤ _
  linarith only [hK,hG,hH,hSub,hAdd]
end ShrinkingSpheres
