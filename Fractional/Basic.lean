import Mathlib--.Algebra.BigOperators.Fin


@[ext]
structure Distr (α : Type) [Fintype α] : Type where
  theFun : α → ℚ≥0
  sumOne : Finset.univ.sum theFun = 1

abbrev FOP₁ (α : Type) [Fintype α] : Type :=
  α → Distr α

abbrev FOP₂ (α : Type) [Fintype α] : Type :=
  α → α → Distr α


variable {α : Type} [Fintype α]

instance : CoeFun (Distr α) (fun _ => α → ℚ≥0) where
  coe := Distr.theFun

def FOP₁.apply₁ (f : FOP₁ α) (x : Distr α) : Distr α where
  theFun (a : α) := ∑ i : α, x i * f i a
  sumOne := by
    rw [Finset.sum_comm]
    conv => lhs; congr; rfl; ext; rw [←Finset.mul_sum, Distr.sumOne, mul_one]
    rw [Distr.sumOne]

def FOP₂.apply₂ (f : FOP₂ α) (x y : Distr α) : Distr α where
  theFun (a : α) := ∑ i : α, ∑ j : α, x i * y j * f i j a
  sumOne := by
    rw [Finset.sum_comm]
    conv => lhs; congr; rfl; ext; rw [Finset.sum_comm]; congr; rfl; ext; rw [←Finset.mul_sum, Distr.sumOne, mul_one]
    conv => lhs; congr; rfl; ext; rw [←Finset.mul_sum, Distr.sumOne, mul_one]
    rw [Distr.sumOne]

variable {f : FOP₁ α} in
notation:max f"⌞" => FOP₁.apply₁ f

variable {f : FOP₂ α} in
notation:max f"⌞" => FOP₂.apply₂ f

theorem FOP₂.apply₂_eq_apply₁_apply₁ (f : FOP₂ α) (x y : Distr α) :
    f⌞ x y = (fun i : α => (f i)⌞ y)⌞ x := by
  ext
  simp only [FOP₂.apply₂, FOP₁.apply₁, NNRat.coe_inj]
  apply congr_arg
  ext
  rw [NNRat.coe_inj, Finset.mul_sum]
  simp_rw [mul_assoc]
