import Fractional.Classes
import Fractional.Distance


variable {S : Type} [Fintype S] [DecidableEq S] [Fragma S]

lemma easy :
    ∀ a b c d : S, ∃ a' b' c' d' : 𝍖 S,
      a ⬙ b 𝄩 c ⬙ d ≤ a' ⬘ b' 𝄩 c' ⬘ d' := by
  intro a b c d
  use a, b, c, d
  rw [Fragma.op_eq, Fragma.op_eq]

lemma hard :
    ∀ a b c d : 𝍖 S, ∃ a' b' c' d' : S,
      a ⬘ b 𝄩 c ⬘ d ≤ a' ⬙ b' 𝄩 c' ⬙ d' := by
  intro a b c d
  sorry

axiom almost_commutative : ∀ x y : S, x ⬙ y 𝄩 y ⬙ x ≤ 0.1

lemma almost_commutative_cor (x y : 𝍖 S) : x ⬘ y 𝄩 y ⬘ x ≤ 0.1 := by
  sorry

lemma almost_commutative_corr (x y z : 𝍖 S) :
    x ⬘ z 𝄩 y ⬘ z ≤ x 𝄩 y := by
  sorry

example (x y z : S) : (x ⬙ y) ⬘ z 𝄩 z ⬘ (y ⬙ x) ≤ 0.2 :=
  calc x ⬙ y ⬘ z 𝄩 z ⬘ y ⬙ x
     ≤ x ⬙ y ⬘ z 𝄩 y ⬙ x ⬘ z + y ⬙ x ⬘ z 𝄩 z ⬘ y ⬙ x := dist_triangle ..
   _ ≤ x ⬙ y ⬘ z 𝄩 y ⬙ x ⬘ z + 0.1 := add_le_add_left (almost_commutative_cor ..) _
   _ ≤ x ⬙ y 𝄩 y ⬙ x + 0.1 := add_le_add_right (almost_commutative_corr ..) _
   _ ≤ 0.1 + 0.1 := add_le_add_right (almost_commutative ..) _
   _ = 0.2 := by norm_num
