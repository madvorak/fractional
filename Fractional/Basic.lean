import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.NNReal.Basic

open scoped NNReal


@[ext]
structure Distr (α : Type) [Fintype α] : Type where
  theFun : α → ℝ
  nonNeg : 0 ≤ theFun
  sumOne : Finset.univ.sum theFun = 1

notation "𝍖" => Distr

abbrev FOP₁ (α : Type) [Fintype α] : Type :=
  α → 𝍖 α

abbrev FOP₂ (α : Type) [Fintype α] : Type :=
  α → α → 𝍖 α


variable {α : Type} [Fintype α]

instance : CoeFun (𝍖 α) (fun _ => α → ℝ) where
  coe := Distr.theFun

instance [DecidableEq α] : Coe α (𝍖 α) where
  coe x := ⟨_, fun _ => by aesop, Fintype.sum_ite_eq x 1⟩

abbrev FOP₁.app₁ (f : FOP₁ α) (x : 𝍖 α) : 𝍖 α where
  theFun (a : α) := ∑ i : α, x i * f i a
  nonNeg _ := by
    apply Finset.sum_nonneg
    intros
    apply mul_nonneg <;> apply Distr.nonNeg
  sumOne := by
    rw [Finset.sum_comm]
    conv => lhs; congr; rfl; ext; rw [←Finset.mul_sum, Distr.sumOne, mul_one]
    rw [Distr.sumOne]

abbrev FOP₂.app₂ (f : FOP₂ α) (x y : 𝍖 α) : 𝍖 α where
  theFun (a : α) := ∑ i : α, ∑ j : α, x i * y j * f i j a
  nonNeg _ := by
    apply Finset.sum_nonneg
    intros
    apply Finset.sum_nonneg
    intros
    apply mul_nonneg
    apply mul_nonneg
    all_goals { apply Distr.nonNeg }
  sumOne := by
    rw [Finset.sum_comm]
    conv => lhs; congr; rfl; ext; rw [Finset.sum_comm]; congr; rfl; ext; rw [←Finset.mul_sum, Distr.sumOne, mul_one]
    conv => lhs; congr; rfl; ext; rw [←Finset.mul_sum, Distr.sumOne, mul_one]
    rw [Distr.sumOne]

variable {f : FOP₁ α} in
notation:max f"⌞" => FOP₁.app₁ f

variable {f : FOP₂ α} in
notation:max f"⌞" => FOP₂.app₂ f

/-- `f a = f⌞ ↑a`  -/
theorem FOP₁.app₁_coe [DecidableEq α] (f : FOP₁ α) (a : α) :
    f a = f⌞ a := by
  ext i
  by_cases hf : f a = i <;> simp [hf]

/-- `f a b = f⌞ ↑a ↑b`  -/
theorem FOP₂.app₂_coe [DecidableEq α] (f : FOP₂ α) (a b : α) :
    f a b = f⌞ a b := by
  ext i
  by_cases hf : f a b = i <;> simp [hf]

/-- `f⌞ x y = ((f ·)⌞ y)⌞ x` -/
theorem FOP₂.app₂_eq_app₁_app₁ (f : FOP₂ α) (x y : 𝍖 α) :
    f⌞ x y = (fun i : α => (f i)⌞ y)⌞ x := by
  ext
  simp only [FOP₂.app₂, FOP₁.app₁, NNReal.coe_inj]
  apply congr_arg
  ext
  rw [Finset.mul_sum]
  simp_rw [mul_assoc]

/-- `f.swap⌞ x y = f⌞ y x` -/
lemma FOP₂.swap_app₂ (f : FOP₂ α) (x y : 𝍖 α) :
    (Function.swap f)⌞ x y = f⌞ y x := by
  ext
  simp only [FOP₂.app₂, FOP₁.app₁, NNReal.coe_inj]
  rw [Finset.sum_comm]
  apply congr_arg
  ext i
  apply congr_arg
  ext j
  rw [mul_comm (x j) (y i)]
