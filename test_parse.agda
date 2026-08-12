module test_parse where

open import Level using (Level; suc)
open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor.Core using (Functor)

variable ℓ : Level

record Test (C : Category (suc ℓ) ℓ ℓ) (FF : Functor (Sets ℓ) C) : Set (suc ℓ) where
  private
    module C = Category C
    module FF = Functor FF
  open C

  arr : ∀ {X Y : Set ℓ} → (X → Y) → (FF.F₀ X ⇒ FF.F₀ Y)
  arr = FF.F₁
