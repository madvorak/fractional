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

theorem FOP₁.apply₁_dist_apply₁_le (f : FOP₁ α) (x y : 𝍖 α) : f⌞ x 𝄩 f⌞ y ≤ x 𝄩 y := by
  rw [dist_le_dist_iff]
  --apply Finset.sum_le_sum
  --intro i _
  sorry
