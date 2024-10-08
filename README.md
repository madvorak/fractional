# Fractional operations

This project provides API for fractional operations in Lean 4.

In particular, we focus on binary functions from a finite type to a (discrete probability) distribution over the same type.
We study compositions of these operations, distances between said distributions (in the sense of the total variational distance), and various (almost) equalities.


## Notation

Given a finite type `α` we write `𝍖 α` to denote a distribution over given type.

Unary fractional operation over `α` is denoted `FOP₁ α` which is an abbreviation for `α → 𝍖 α` functions.

Binary fractional operation over `α` is denoted `FOP₂ α` which is an abbreviation for `α → α → 𝍖 α` functions.

Apart from applying a unary fractional operation `f : FOP₁ α` to argument `a : α`
```
(f a) : 𝍖 α
```
you can also apply `f` to distribution `x : 𝍖 α` as follows (notation, definition):
```
f⌞ x = (fun a : α => ∑ i : α, x i * f i a)
```

Similarly a binary fractional operation `g : FOP₂ α` can be applied to arguments `a b : α`
```
(g a b) : 𝍖 α
```
or to distributions `x y : 𝍖 α` as follows (notation, definition):
```
g⌞ x = (fun a : α => ∑ i : α, ∑ j : α, x i * y j * g i j a)
```

If a type is equipped with a only one specified fractional binary operation, we call it `Fragma` (for FRactional mAGMA).

Application of the `Fragma` operation to arguments `a b : α` is denoted:
```
a ⬙ b
```

Application of the `Fragma` operation to distributions `x y : 𝍖 α` is denoted:
```
x ⬘ y
```

Given various implicit conversions, we can establish facts such as:
```
a ⬙ b = a ⬘ b
```

Distance between two distributions `x y : 𝍖 α` is denoted and defined as follows:
```
x 𝄩 y = (∑ i : α, |x i - y i|) / 2
```
We prove that it forms a metric space.


## Content

We provide some useful relationships (using notation from above):
```
f a = f⌞ ↑a
g⌞ x y = ((g ·)⌞ y)⌞ x
f⌞ x 𝄩 f⌞ y ≤ x 𝄩 y
g⌞ u x 𝄩 g⌞ v y ≤ u 𝄩 v + x 𝄩 y
```

In the experimental part, we study what certain almost-equality axioms such as
```
a ⬙ b 𝄩 b ⬙ a ≤ ε
```
imply about the structure.
