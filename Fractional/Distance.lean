import Fractional.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Topology.MetricSpace.Defs


variable {α : Type} [Fintype α]

noncomputable instance : MetricSpace (𝍖 α) where
  dist x y :=
    (∑ i : α, |x i - y i|) / 2
  dist_self x := by
    simp [dist]
  dist_comm x y := by
    simp [dist, abs_sub_comm]
  dist_triangle x y z := by
    simp [dist]
    rw [←add_div, ←Finset.sum_add_distrib]
    apply div_le_div_of_nonneg_right
    swap; norm_num
    apply Finset.sum_le_sum
    intros
    apply abs_sub_le
  eq_of_dist_eq_zero hxy := by
    simp [dist] at hxy
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)] at hxy
    ext i
    simpa [abs_eq_zero, sub_eq_zero] using hxy i (Finset.mem_univ i)

infix:82 " 𝄩 " => dist

lemma dist_mul_two (x y : 𝍖 α) : x 𝄩 y * 2 = ∑ i : α, |x i - y i| :=
  div_mul_cancel₀ _ two_ne_zero

lemma two_mul_dist (x y : 𝍖 α) : 2 * x 𝄩 y = ∑ i : α, |x i - y i| :=
  mul_comm 2 (x 𝄩 y) ▸ dist_mul_two x y

lemma dist_le_real_iff (x y : 𝍖 α) (ζ : ℝ) : x 𝄩 y ≤ ζ ↔ ∑ i : α, |x i - y i| ≤ 2 * ζ := by
  rw [←two_mul_dist, mul_le_mul_left]
  exact zero_lt_two

lemma dist_le_dist_iff (u v x y : 𝍖 α) : u 𝄩 v ≤ x 𝄩 y ↔ ∑ i : α, |u i - v i| ≤ ∑ i : α, |x i - y i| := by
  rw [←two_mul_dist, ←two_mul_dist, mul_le_mul_left]
  exact zero_lt_two

lemma FOP₁.app₁_dist_app₁_eq_zero (f : FOP₁ α) {x y : 𝍖 α} (hxy : x 𝄩 y = 0) : f⌞ x 𝄩 f⌞ y = 0 := by
  simp_all

@[ext]
private structure PreDistr (α : Type) [Fintype α] : Type where
  theFun : α → ℝ
  nonNeg : 0 ≤ theFun

notation "𝌅" => PreDistr

private instance : CoeFun (𝌅 α) (fun _ => α → ℝ) where
  coe := PreDistr.theFun

private instance : Coe (𝍖 α) (𝌅 α) where
  coe x := ⟨x.theFun, x.nonNeg⟩

private noncomputable def commonPreDistr (x y : 𝌅 α) : 𝌅 α where
  theFun := fun i : α => min (x i) (y i)
  nonNeg := fun i : α => le_min (x.nonNeg i) (y.nonNeg i)

private noncomputable def differPreDistr (x y : 𝌅 α) : 𝌅 α where
  theFun := fun i : α => if x i ≤ y i then 0 else x i - y i
  nonNeg := fun i : α => by sorry

private noncomputable def addPreDistr (x y : 𝌅 α) : 𝌅 α where
  theFun := fun i : α => x i + y i
  nonNeg := fun i : α => by sorry

private lemma commonPreDistr_comm (x y : 𝌅 α) : commonPreDistr x y = commonPreDistr y x := by
  ext
  apply min_comm

private lemma add_common_differ (x y : 𝌅 α) : addPreDistr (commonPreDistr x y) (differPreDistr x y) = x := by
  ext i
  by_cases hi : x i ≤ y i <;> simp [addPreDistr, commonPreDistr, differPreDistr, hi]
  rw [min_eq_right (le_of_not_ge hi)]
  apply add_sub_cancel

private lemma add_common_differ' (x y : 𝍖 α) : addPreDistr (commonPreDistr x y) (differPreDistr x y) = (x : 𝌅 α) :=
  add_common_differ (x : 𝌅 α) (y : 𝌅 α)

private lemma ugly_sum (x y : 𝌅 α) :
    ∑ i : α,
      |addPreDistr (commonPreDistr x y) (differPreDistr x y) i -
       addPreDistr (commonPreDistr y x) (differPreDistr y x) i| =
    ∑ i : α,
      |(differPreDistr x y) i - (differPreDistr y x) i| := by
  congr
  ext
  simp only [addPreDistr]
  apply congr_arg
  rw [commonPreDistr_comm]
  abel

private lemma ugly_sum' (x y : 𝌅 α) :
    ∑ i : α,
      |(differPreDistr x y) i - (differPreDistr y x) i| =
    ∑ i : α,
      ((differPreDistr x y) i + (differPreDistr y x) i) := by
  congr
  ext i
  by_cases hi : x i ≤ y i
  · convert_to |0 - (y i - x i)| = (0 : ℝ) + (y i - x i) using 3
    · simp [differPreDistr, hi]
    · simp [differPreDistr, hi]
      intro
      linarith
    · simp [differPreDistr, hi]
    · simp [differPreDistr, hi]
      intro
      linarith
    rw [zero_add, zero_sub, abs_neg, abs_of_nonneg (sub_nonneg_of_le hi)]
  · sorry

private lemma less_ugly_sum (x y : 𝌅 α) :
    ∑ i : α,
      |addPreDistr (commonPreDistr x y) (differPreDistr x y) i -
       addPreDistr (commonPreDistr y x) (differPreDistr y x) i| =
    ∑ i : α,
      ((differPreDistr x y) i + (differPreDistr y x) i) :=
  (ugly_sum x y).trans (ugly_sum' x y)

theorem FOP₁.app₁_dist_app₁_le_dist (f : FOP₁ α) (x y : 𝍖 α) : f⌞ x 𝄩 f⌞ y ≤ x 𝄩 y := by
  rw [dist_le_dist_iff]
  have hx := add_common_differ' x y
  have hy := add_common_differ' y x
  have hd := hy ▸ hx ▸ less_ugly_sum (x : 𝌅 α) (y : 𝌅 α)
  rw [hd]
  have hx' := add_common_differ' (f⌞ x) (f⌞ y)
  have hy' := add_common_differ' (f⌞ y) (f⌞ x)
  have hd' := hy' ▸ hx' ▸ less_ugly_sum (f⌞ x : 𝌅 α) (f⌞ y : 𝌅 α)
  rw [hd']
  clear * -
  sorry
