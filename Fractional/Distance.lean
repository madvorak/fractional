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

set_option linter.unusedSectionVars false

private noncomputable def commonDistr (x y : α → ℝ) : α → ℝ :=
  fun i : α => min (x i) (y i)

private noncomputable def differDistr (x y : α → ℝ) : α → ℝ :=
  fun i : α => if x i ≤ y i then 0 else x i - y i

private lemma commonDistr_comm (x y : α → ℝ) : commonDistr x y = commonDistr y x := by
  ext
  apply min_comm

private lemma add_common_differ (x y : α → ℝ) : commonDistr x y + differDistr x y = x := by
  ext i
  by_cases hi : x i ≤ y i <;> simp [commonDistr, differDistr, hi]
  rw [min_eq_right (le_of_not_ge hi)]
  apply add_sub_cancel

private lemma ugly_sum_ (x y : α → ℝ) :
    ∑ i : α,
      |(commonDistr x y i + differDistr x y i) -
       (commonDistr y x i + differDistr y x i)| =
    ∑ i : α,
      |differDistr x y i - differDistr y x i| := by
  congr
  ext i
  apply congr_arg
  rw [commonDistr_comm]
  abel

private lemma ugly_sum' (x y : α → ℝ) :
    ∑ i : α, |differDistr x y i - differDistr y x i| =
    ∑ i : α, (differDistr x y i + differDistr y x i) := by
  congr
  ext i
  by_cases hi : x i ≤ y i
  · convert_to |0 - (y i - x i)| = 0 + (y i - x i) using 3
    · simp [differDistr, hi]
    · simp [differDistr, hi]
      intro
      linarith
    · simp [differDistr, hi]
    · simp [differDistr, hi]
      intro
      linarith
    rw [zero_add, zero_sub, abs_neg, abs_of_nonneg (sub_nonneg_of_le hi)]
  · convert_to |(x i - y i) - 0| = (x i - y i) + 0 using 3
    · simp [differDistr, hi]
    · simp [differDistr, hi]
      intro
      linarith
    · simp [differDistr, hi]
    · simp [differDistr, hi]
      intro
      linarith
    rw [add_zero, sub_zero, abs_of_nonneg (sub_nonneg_of_le (le_of_not_ge hi))]

private lemma ugly_sum (x y : α → ℝ) :
    ∑ i : α,
      |(commonDistr x y + differDistr x y) i -
       (commonDistr y x + differDistr y x) i| =
    ∑ i : α,
      (differDistr x y i + differDistr y x i) :=
  Eq.trans
    (ugly_sum_ x y)
    (ugly_sum' x y)

private lemma eq_max_sub_min (x y : α → ℝ) (i : α) :
    differDistr x y i + differDistr y x i = max (x i) (y i) - min (x i) (y i) := by
  simp [differDistr]
  by_cases hi : x i ≤ y i
  · simp [hi]
    intro
    linarith
  · simp [hi, le_of_not_ge hi]

theorem FOP₁.app₁_dist_app₁_le_dist (f : FOP₁ α) (x y : 𝍖 α) : f⌞ x 𝄩 f⌞ y ≤ x 𝄩 y := by
  rw [dist_le_dist_iff]
  have hx := add_common_differ x y
  have hy := add_common_differ y x
  have hd := hy ▸ hx ▸ ugly_sum (x : α → ℝ) (y : α → ℝ)
  rw [hd]
  have hx' := add_common_differ (f⌞ x) (f⌞ y)
  have hy' := add_common_differ (f⌞ y) (f⌞ x)
  have hd' := hy' ▸ hx' ▸ ugly_sum (f⌞ x : α → ℝ) (f⌞ y : α → ℝ)
  rw [hd']
  clear * -
  simp only [eq_max_sub_min]
  sorry
