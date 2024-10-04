import Mathlib.Data.NNRat.BigOperators


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

instance [DecidableEq α] : Coe α (Distr α) where
  coe a := ⟨_, Fintype.sum_ite_eq a 1⟩

abbrev FOP₁.apply₁ (f : FOP₁ α) (x : Distr α) : Distr α where
  theFun (a : α) := ∑ i : α, x i * f i a
  sumOne := by
    rw [Finset.sum_comm]
    conv => lhs; congr; rfl; ext; rw [←Finset.mul_sum, Distr.sumOne, mul_one]
    rw [Distr.sumOne]

abbrev FOP₂.apply₂ (f : FOP₂ α) (x y : Distr α) : Distr α where
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

/-- `f⌞ x y = ((f ·)⌞ y)⌞ x` -/
theorem FOP₂.apply₂_eq_apply₁_apply₁ (f : FOP₂ α) (x y : Distr α) :
    f⌞ x y = (fun i : α => (f i)⌞ y)⌞ x := by
  ext
  simp only [FOP₂.apply₂, FOP₁.apply₁, NNRat.coe_inj]
  apply congr_arg
  ext
  rw [NNRat.coe_inj, Finset.mul_sum]
  simp_rw [mul_assoc]

/-- `f a = f⌞ ↑a`  -/
theorem FOP₁.apply₁_coe [DecidableEq α] (f : FOP₁ α) (a : α) :
    f a = f⌞ a := by
  ext i
  by_cases hf : f a = i <;> simp [hf]

/-- `f a b = f⌞ ↑a ↑b`  -/
theorem FOP₂.apply₂_coe [DecidableEq α] (f : FOP₂ α) (a b : α) :
    f a b = f⌞ a b := by
  ext i
  by_cases hf : f a b = i <;> simp [hf]
