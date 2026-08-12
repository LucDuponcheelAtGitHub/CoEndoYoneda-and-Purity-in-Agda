module bfc_scratch where

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Level using (Level; _⊔_; suc; Lift; lift)
open import Data.Unit using (⊤; tt)
open import Axiom.Extensionality.Propositional using (Extensionality)

open Functor
open NaturalTransformation

variable
  ℓ : Level

postulate
  funext : ∀ {a b} → Extensionality a b

record BasicFunctionalCategory
    (C : Category (suc ℓ) ℓ ℓ) 
    (FF : Functor (Sets ℓ) C) : Set (suc ℓ) where
  private
    module C = Category C
    module FF = Functor FF
  open C
  
  field
    strict : ∀ {X Y} {f g : X ⇒ Y} → f ≈ g → f ≡ g
  T : Set ℓ
  T = Lift ℓ ⊤
  t : T
  t = lift tt
  CYF : Obj → Functor C (Sets ℓ)
  CYF X = record { F₀ = λ Y → X ⇒ Y ; F₁ = λ f g → C._∘_ f g ; identity = λ {Y} g → strict identityˡ ; homomorphism = λ {Y Z W f h} g → strict assoc ; F-resp-≈ = λ {Y} {Z} {f} {h} f≈h g → strict (∘-resp-≈ˡ f≈h) }
  CYEF : Obj → Functor C C
  CYEF X = FF ∘F (CYF X)
  FFT : Obj
  FFT = Functor.F₀ FF T
  GEFF : Functor C C
  GEFF = CYEF FFT 

  field
    nu : NaturalTransformation Categories.Functor.id GEFF
    nu-eq-T : η nu (Functor.F₀ FF T) ≡ FF.F₁ (λ _ → FF.F₁ (λ _ → t))

open BasicFunctionalCategory

uip : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

module _ {C : Category (suc ℓ) ℓ ℓ} {FF : Functor (Sets ℓ) C} where

  StrictType = ∀ {X Y} {f g : Category._⇒_ C X Y} → Category._≈_ C f g → f ≡ g

  CYF-helper : StrictType → Category.Obj C → Functor C (Sets ℓ)
  CYF-helper s X = record
    { F₀ = λ Y → Category._⇒_ C X Y
    ; F₁ = λ f g → Category._∘_ C f g
    ; identity = λ {Y} g → s (Category.identityˡ C)
    ; homomorphism = λ {Y Z W f h} g → s (Category.assoc C)
    ; F-resp-≈ = λ {Y} {Z} {f} {h} f≈h g → s (Category.∘-resp-≈ˡ C f≈h)
    }
    
  GEFF-helper : StrictType → Functor C C
  GEFF-helper s = FF ∘F (CYF-helper s (Functor.F₀ FF (Lift ℓ ⊤)))

  bfc-eq : (a b : BasicFunctionalCategory C FF)
      → (p : (λ {X Y f g} → strict a {X} {Y} {f} {g}) ≡ (λ {X Y f g} → strict b {X} {Y} {f} {g}))
      → subst (λ (s : StrictType) → NaturalTransformation Categories.Functor.id (GEFF-helper s)) p (nu a) ≡ nu b
      → a ≡ b
  bfc-eq record { strict = s1 ; nu = n1 ; nu-eq-T = e1 } record { strict = .s1 ; nu = .n1 ; nu-eq-T = e2 } refl refl = 
    cong (λ e → record { strict = s1 ; nu = n1 ; nu-eq-T = e }) (uip e1 e2)

